import Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluingAdic
import Langlands.GroupScheme.Cohomology.MultiplicativeTypeVanishingProof
import Langlands.GroupScheme.HomScheme.AdicConjugatorSteps
import Langlands.GroupScheme.HomScheme.InfinitesimalReduction
import Langlands.GroupScheme.HomScheme.SquareZeroCohomology
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry

/-! # Adic Hom effectivity from a lift of the first quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry (affineTestMorphismProperty
  affineTestMorphismProperty_of_isIso)
open Langlands.AlgebraicGeometry.AdicAffinePoints
open Langlands.AlgebraicGeometry.UnramifiedFunctor.ChartGluing

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S} [Smooth G.X.hom]

private theorem hasAffineSquareZeroConjugatorLifting_of_multiplicativeType
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H) :
    HasAffineSquareZeroConjugatorLifting H G := by
  intro A _ I hI a b w
  have hHa := hH.baseChange a
  let : IsAffineHom ((baseChange a).obj H).X.hom := hHa.isAffineHom
  exact squareZeroHomomorphismCohomology S H G A I hI a b w hHa.flat
    (isAffine_of_isAffineHom ((baseChange a).obj H).X.hom)
    (Cohomology.multiplicativeTypeLowDegreeVanishing _ _ (hH.baseChange b))

private theorem hasConjugatorLifting_affine_of_surjective
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Surjective φ) (hnil : IsNilpotent (RingHom.ker φ)) :
    affineTestMorphismProperty (HasConjugatorLifting H G) (CommRingCat.ofHom φ) := by
  let P := affineTestMorphismProperty (HasConjugatorLifting H G)
  let q := CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker φ))
  let e := (RingHom.quotientKerEquivOfSurjective hφ).toCommRingCatIso
  have hcomp : (CommRingCat.ofHom φ) = q ≫ e.hom := by
    ext a
    rfl
  have hq : P q :=
    hasConjugatorLifting_nilpotent
      (hasAffineSquareZeroConjugatorLifting_of_multiplicativeType hH) A (RingHom.ker φ) hnil
  have he : P e.hom := affineTestMorphismProperty_of_isIso (HasConjugatorLifting H G) _
  exact hcomp.symm ▸ P.comp_mem q e.hom hq he

namespace Adic

variable {A : Type u} [CommRing A] [IsLocalRing A]
  {H G : GroupScheme (Spec (CommRingCat.of A))} [Smooth G.X.hom]

/-- Over a complete local ring, it suffices to lift the first quotient of
a formal Hom system into the smooth group. -/
def HasFirstQuotientLift
    (s : System (maximalIdeal A) H G) : Prop :=
  ∃ f : H ⟶ G, (System.restrict (maximalIdeal A) H G f).hom 0 = s.hom 0

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1200000 in
/-- A lift of the first quotient extends to an algebraization by one actual
conjugation. The target need only be smooth. -/
theorem exists_algebraization_of_firstQuotientLift [IsAdicComplete (maximalIdeal A) A]
    (hH : RelativeMultiplicativeType.IsMultiplicativeType H)
    (s : System (maximalIdeal A) H G) (hs : HasFirstQuotientLift s) :
    ∃ f : H ⟶ G, System.restrict (maximalIdeal A) H G f = s := by
  obtain ⟨f, hf⟩ := hs
  let m := maximalIdeal A
  let T (n : ℕ) := Over.mk (quotientMap m n)
  let C (n : ℕ) := {g : T n ⟶ G.X // s.hom n = conjugationFamily f g}
  have hstep (n : ℕ) (g : C n) :
      ∃ g' : C (n + 1), transitionOver m n ≫ g'.1 = g.1 := by
    let a := transitionOver m n
    have ha : HasConjugatorLifting H G a :=
      hasConjugatorLifting_affine_of_surjective hH (transitionRingHom m n)
        (transitionRingHom_surjective m n) ⟨2, transitionRingHom_ker_sq m n⟩
        (quotientMap m (n + 1)) (quotientMap m n) (transition_quotientMap m n)
    have hEval : evaluate a (s.hom (n + 1)) =
        conjugateRelative
          (evaluate a ((baseChange (quotientMap m (n + 1))).map f)) g.1 := by
      have hBase :
          evaluate a ((baseChange (quotientMap m (n + 1))).map f) =
            (baseChange (quotientMap m n)).map f := evaluate_baseChange a f
      rw [s.compatible, hBase]
      exact g.2
    obtain ⟨g', hred, hconj⟩ := ha.2 _ _ g.1 hEval
    exact ⟨⟨g', hconj⟩, hred⟩
  let c₀ : C 0 := ⟨1, by rw [conjugationFamily_one]; exact hf.symm⟩
  let c : ∀ n, C n := Nat.rec (motive := C) c₀
    (fun n g => (hstep n g).choose)
  let g (n : ℕ) := (c n).1
  have hcompat (n : ℕ) : transitionOver m n ≫ g (n + 1) = g n :=
    (hstep n (c n)).choose_spec
  obtain ⟨q, hq⟩ := exists_specMap_adic_lift (fun n => (g n).left)
    (fun n => congrArg Over.Hom.left (hcompat n))
  have hw : q ≫ G.X.hom = 𝟙 _ := by
    apply specMap_adic_ext
    intro n
    change quotientMap m n ≫ (q ≫ G.X.hom) = quotientMap m n ≫ 𝟙 _
    rw [← Category.assoc, Category.comp_id]
    exact (congrArg (· ≫ G.X.hom) (hq n)).trans (Over.w (g n))
  let p : Over.mk (𝟙 (Spec (CommRingCat.of A))) ⟶ G.X := Over.homMk q hw
  have hp (n : ℕ) : G.constantPoint p (T n) = g n :=
    Over.OverMorphism.ext (hq n)
  refine ⟨f ≫ (G.innerIso p).hom, System.ext (fun n => ?_)⟩
  exact (conjugationFamily_constantPoint f p (T n)).symm.trans
    ((congrArg (conjugationFamily f) (hp n)).trans (c n).2.symm)

end Adic

end Langlands.GroupScheme.HomScheme
