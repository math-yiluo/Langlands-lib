import Langlands.AbelianScheme.FieldMultiplicationFiniteEtale
import Langlands.AbelianScheme.Tate.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Actual point fibres of multiplication and evaluation of torsion sections -/

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

variable {K : Type u} [Field K]

set_option backward.isDefEq.respectTransparency.types false in
/-- Two sections over a field with the same image point are equal. -/
theorem section_eq_of_point_eq {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K))
    {f g : Spec (CommRingCat.of K) ⟶ X}
    (hf : f ≫ p = 𝟙 _) (hg : g ≫ p = 𝟙 _)
    (h : f (IsLocalRing.closedPoint K) = g (IsLocalRing.closedPoint K)) : f = g := by
  let q := f (IsLocalRing.closedPoint K)
  let a : X.residueField q ⟶ CommRingCat.of K :=
    X.descResidueField (Scheme.stalkClosedPointTo f)
  let b : CommRingCat.of K ⟶ X.residueField q :=
    Spec.preimage (X.fromSpecResidueField q ≫ p)
  have ha : Spec.map a ≫ X.fromSpecResidueField q = f :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K X f
  have hba : b ≫ a = 𝟙 _ := by
    apply Spec.map_injective
    simpa only [Spec.map_comp, b, Spec.map_preimage, Spec.map_id, ← Category.assoc, ha] using hf
  have hsurj : Function.Surjective a := fun t => ⟨b t, ConcreteCategory.congr_hom hba t⟩
  have : IsIso a := (ConcreteCategory.isIso_iff_bijective a).mpr
    ⟨a.hom.injective, hsurj⟩
  have hb : b = inv a := by
    rw [← cancel_mono a, hba, IsIso.inv_hom_id]
  have : IsIso b := hb ▸ inferInstance
  apply (X.SpecToEquivOfField K).injective
  rw [Scheme.SpecToEquivOfField_eq_iff]
  refine ⟨h, ?_⟩
  apply (cancel_epi b).mp
  change b ≫ a = b ≫ (X.residueFieldCongr h).hom ≫
    X.descResidueField (Scheme.stalkClosedPointTo g)
  rw [hba]
  apply Spec.map_injective
  simp only [Spec.map_id, Spec.map_comp, b, Spec.map_preimage]
  rw [Category.assoc, Scheme.residueFieldCongr_fromSpecResidueField_assoc,
    ← Category.assoc,
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField, hg]

/-- Evaluation at the point of `Spec K` is injective on sections over `Spec K`. -/
theorem sectionPoint_injective {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of K)) :
    Function.Injective
      (fun x : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk p =>
        x.left (IsLocalRing.closedPoint K)) := by
  intro x y h
  apply Over.OverMorphism.ext
  exact section_eq_of_point_eq p x.w y.w h

variable (A : AbelianScheme (Spec (CommRingCat.of K))) (n : ℕ)

/-- The actual underlying point fibre of multiplication by `n` over the identity. -/
def TorsionPointFibre : Set A.X.left :=
  (GroupScheme.multiplication A.toGrp (n : ℤ)).hom.hom.left ⁻¹'
    {η[A.X].left (IsLocalRing.closedPoint K)}

/-- The point fibre is finite when `n` is nonzero in `K`. -/
theorem torsionPointFibre_finite (hn : (n : K) ≠ 0) :
    (TorsionPointFibre A n).Finite := by
  have := multiplication_isFinite_of_ne_zero A n hn
  exact Scheme.Hom.finite_preimage_singleton _ _

/-- The identity is a closed point over every field. -/
theorem isClosed_identityPoint :
    IsClosed ({η[A.X].left (IsLocalRing.closedPoint K)} : Set A.X.left) := by
  let e : Spec (CommRingCat.of K) ⟶ A.X.left := η[A.X].left
  have he : e ≫ A.X.hom = 𝟙 _ := by
    exact Over.w η[A.X]
  have : IsClosedImmersion e := isClosedImmersion_of_comp_eq_id A.X.hom e he
  have hrange : Set.range e = {e (IsLocalRing.closedPoint K)} :=
    Set.range_eq_singleton fun z => congrArg e (Subsingleton.elim z _)
  change IsClosed {e (IsLocalRing.closedPoint K)}
  rw [← hrange]
  exact e.isClosedEmbedding.isClosed_range

/-- The point fibre of multiplication is closed. -/
theorem torsionPointFibre_isClosed : IsClosed (TorsionPointFibre A n) :=
  (isClosed_identityPoint A).preimage
    (GroupScheme.multiplication A.toGrp (n : ℤ)).hom.hom.left.continuous

/-- Every point of the finite multiplication fibre is closed. -/
theorem torsionPointFibre_isClosed_singleton (hn : (n : K) ≠ 0)
    {z : A.X.left} (hz : z ∈ TorsionPointFibre A n) : IsClosed ({z} : Set A.X.left) := by
  have := multiplication_isFinite_of_ne_zero A n hn
  exact isClosed_of_subset_discrete_closed (Set.singleton_subset_iff.mpr hz)
    (Scheme.Hom.isDiscrete_preimage_singleton _ _) (torsionPointFibre_isClosed A n)

/-- Evaluation of an actual torsion section lies in the actual multiplication fibre. -/
def levelToTorsionPointFibre
    (x : GroupScheme.Tate.Level A.toGrp (Over.mk (𝟙 (Spec (CommRingCat.of K)))) n) :
    TorsionPointFibre A n := by
  refine ⟨(Additive.toMul x).val.left (IsLocalRing.closedPoint K), ?_⟩
  have hx : (Additive.toMul x).val ≫
      (GroupScheme.multiplication A.toGrp (n : ℤ)).hom.hom = 1 :=
    (Additive.toMul x).property
  have ht : CategoryTheory.CartesianMonoidalCategory.toUnit
      (Over.mk (𝟙 (Spec (CommRingCat.of K)))) = 𝟙 _ :=
    CategoryTheory.CartesianMonoidalCategory.toUnit_unique _ _
  simp only [CategoryTheory.Hom.one_def, ht, Category.id_comp] at hx
  have hx' := congrArg Over.Hom.left hx
  have he : (Additive.toMul x).val.left ≫
      (GroupScheme.multiplication A.toGrp (n : ℤ)).hom.hom.left = η[A.X].left := by
    simpa only [Over.comp_left] using hx'
  exact congrArg (fun f : Spec (CommRingCat.of K) ⟶ A.X.left =>
    f (IsLocalRing.closedPoint K)) he

/-- Distinct actual torsion sections give distinct points of the multiplication fibre. -/
theorem levelToTorsionPointFibre_injective :
    Function.Injective (levelToTorsionPointFibre A n) := by
  intro x y h
  apply GroupScheme.Tate.toSection_injective A.toGrp _ n
  apply sectionPoint_injective A.X.hom
  exact congrArg Subtype.val h

end Langlands.AbelianScheme.PolarizedFiniteLevel
