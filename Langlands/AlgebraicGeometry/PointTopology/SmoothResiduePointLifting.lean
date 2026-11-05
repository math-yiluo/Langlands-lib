import Langlands.AlgebraicGeometry.PointTopology.AdicSmoothPointLifting

/-! # Lifting smooth scheme points with field residue -/

noncomputable section

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]
variable (X : Over (Spec (CommRingCat.of R))) [Smooth X.hom]

/-- Over an adically complete algebra with field quotient, every quotient-valued
point of an arbitrary smooth scheme lifts with its specified reduction. -/
theorem surjective_changeRing_of_isAdicComplete_of_isMaximal
    (S : Type u) [CommRing S] [Algebra R S] (I : Ideal S) [I.IsMaximal]
    [IsAdicComplete I S] :
    Function.Surjective (fun p : RingPoint R X S =>
      p.changeRing (Ideal.Quotient.mkₐ R I)) := by
  let : Field (S ⧸ I) := Ideal.Quotient.field I
  intro p₀
  dsimp only [RingPoint] at p₀
  let t : PrimeSpectrum (S ⧸ I) := ⊥
  obtain ⟨i, y, hy⟩ := X.left.affineCover.exists_eq (p₀.left t)
  let j : X.left.affineCover.X i ⟶ X.left := X.left.affineCover.f i
  have hrange : Set.range p₀.left ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact ⟨y, hy.trans (congrArg p₀.left (Subsingleton.elim t z))⟩
  let g := IsOpenImmersion.lift j p₀.left hrange
  have hg : g ≫ j = p₀.left := IsOpenImmersion.lift_fac _ _ _
  let U : Over (Spec (CommRingCat.of R)) := Over.mk (j ≫ X.hom)
  let q₀ : RingPoint R U (S ⧸ I) := Over.homMk g (by
    change g ≫ (j ≫ X.hom) = Spec.algebraMap R (S ⧸ I)
    rw [← Category.assoc, hg]
    exact Over.w p₀)
  let f : U ⟶ X := Over.homMk j
  have : IsAffine U.left := inferInstanceAs (IsAffine (X.left.affineCover.X i))
  have : Smooth U.hom := inferInstanceAs (Smooth (j ≫ X.hom))
  obtain ⟨q, hq⟩ := surjective_changeRing_of_isAdicComplete R U S I q₀
  refine ⟨q ≫ f, ?_⟩
  change (ringTestMap R (Ideal.Quotient.mkₐ R I) ≫ q) ≫ f = p₀
  rw [show ringTestMap R (Ideal.Quotient.mkₐ R I) ≫ q = q₀ from hq]
  apply RingPoint.ext
  exact hg

/-- A chosen actual lift of a field-residue point of a smooth scheme. -/
def smoothResiduePointLift
    (S : Type u) [CommRing S] [Algebra R S] (I : Ideal S) [I.IsMaximal]
    [IsAdicComplete I S] (p₀ : RingPoint R X (S ⧸ I)) : RingPoint R X S :=
  (surjective_changeRing_of_isAdicComplete_of_isMaximal R X S I p₀).choose

/-- The chosen smooth lift preserves the given residue point exactly. -/
@[simp] theorem smoothResiduePointLift_changeRing
    (S : Type u) [CommRing S] [Algebra R S] (I : Ideal S) [I.IsMaximal]
    [IsAdicComplete I S] (p₀ : RingPoint R X (S ⧸ I)) :
    (smoothResiduePointLift R X S I p₀).changeRing (Ideal.Quotient.mkₐ R I) = p₀ :=
  (surjective_changeRing_of_isAdicComplete_of_isMaximal R X S I p₀).choose_spec

/-- A field-residue point gives an actual section of a smooth scheme over a
complete base, without an affineness hypothesis on the scheme. -/
theorem nonempty_ringPoint_of_residue
    (I : Ideal R) [I.IsMaximal] [IsAdicComplete I R]
    (h : Nonempty (RingPoint R X (R ⧸ I))) : Nonempty (RingPoint R X R) := by
  obtain ⟨p₀⟩ := h
  exact ⟨smoothResiduePointLift R X R I p₀⟩

end Langlands.AlgebraicGeometry.PointTopology
