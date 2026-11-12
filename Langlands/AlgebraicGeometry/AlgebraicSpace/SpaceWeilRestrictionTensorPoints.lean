import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.WeilRestrictionFiniteProductTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.RingPointsEquivalence
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeComparison
import Langlands.AlgebraicGeometry.PointTopology.CompletedTensorWeilRestrictionNaturality

/-!
# Original coefficient maps on tensor Weil restriction points

The tensor comparison on actual algebraic-space points is expressed by
its actual test map. Its factor maps commute with compatible
changes of the lower and upper coefficient rings.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

section Tensor

variable (R B C D : Type u) [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra C D] [Algebra B D]
  (e : C ⊗[R] B ≃ₐ[C] D)
  (he : ∀ b : B, e (1 ⊗ₜ[R] b) = algebraMap B D b)

/-- The same tensor equivalence, retaining the original upper coefficient
algebra rather than the completed lower coefficient algebra. -/
def weilRestrictionTensorCoefficientEquiv : B ⊗[R] C ≃ₐ[B] D :=
  { toRingEquiv := (Algebra.TensorProduct.comm R B C).toRingEquiv.trans e.toRingEquiv
    commutes' := he }

@[simp]
theorem weilRestrictionTensorCoefficientEquiv_tmul (b : B) (c : C) :
    weilRestrictionTensorCoefficientEquiv R B C D e he (b ⊗ₜ[R] c) =
      e (c ⊗ₜ[R] b) := rfl

variable (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))

/-- The canonical tensor point equivalence, using the original upper
coefficient algebra structure. -/
def ringWeilRestrictionTensorPointsEquiv :
    RingPoints R (ringWeilRestrictionSpace R B X h) C ≃ RingPoints B X D :=
  (ringWeilRestrictionPointsEquiv R B C X h).trans
    (RingPoints.changeRingEquiv X (weilRestrictionTensorCoefficientEquiv R B C D e he))

/-- The corresponding map of actual test spectra. -/
def weilRestrictionTensorPointTestMap :
    ringTest B D ⟶ ringBaseChange R B (ringTest R C) :=
  ringTestMap B (weilRestrictionTensorCoefficientEquiv R B C D e he).toAlgHom ≫
    (ringBaseChangeSpectrumIso R B C).inv

@[reassoc (attr := simp)]
theorem weilRestrictionTensorPointTestMap_fst :
    (weilRestrictionTensorPointTestMap R B C D e he).left ≫
      pullback.fst (Spec.algebraMap R C) (Spec.algebraMap R B) =
        Spec.algebraMap C D := by
  simp only [weilRestrictionTensorPointTestMap, Over.comp_left, Category.assoc,
    ringBaseChangeSpectrumIso_inv_fst, ringTestMap_left]
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext e.commutes

@[reassoc (attr := simp)]
theorem weilRestrictionTensorPointTestMap_snd :
    (weilRestrictionTensorPointTestMap R B C D e he).left ≫
      pullback.snd (Spec.algebraMap R C) (Spec.algebraMap R B) =
        Spec.algebraMap B D :=
  Over.w (weilRestrictionTensorPointTestMap R B C D e he)

theorem ringWeilRestrictionTensorPointsEquiv_apply
    (x : RingPoints R (ringWeilRestrictionSpace R B X h) C) :
    ringWeilRestrictionTensorPointsEquiv R B C D e he X h x =
      X.pullback (weilRestrictionTensorPointTestMap R B C D e he) x := by
  change X.presheaf.map (ringTestMap B
      (weilRestrictionTensorCoefficientEquiv R B C D e he).toAlgHom).op
    (X.presheaf.map (ringBaseChangeSpectrumIso R B C).inv.op x) =
    X.presheaf.map (weilRestrictionTensorPointTestMap R B C D e he).op x
  rw [weilRestrictionTensorPointTestMap, op_comp, Functor.map_comp]
  rfl

end Tensor

section Factors

variable (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C]
  {ι : Type u} (D : ι → Type u) [∀ i, CommRing (D i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  (e : C ⊗[R] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[R] b) i = algebraMap B (D i) b)

/-- The original upper component of a tensor Weil point, evaluated on the
same factor test spectrum as the scheme comparison. -/
def completedTensorSpaceWeilRestrictionPointMap
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))
    (x : RingPoints R (ringWeilRestrictionSpace R B X h) C) (i : ι) :
    RingPoints B X (D i) :=
  X.pullback (completedTensorWeilRestrictionFactorTestMap R B C D e he i) x

theorem weilRestrictionTensorPointTestMap_factor (i : ι) :
    ringTestMap B (Pi.evalAlgHom B D i) ≫
      weilRestrictionTensorPointTestMap R B C (∀ j, D j) e (fun b => funext (he b)) =
        completedTensorWeilRestrictionFactorTestMap R B C D e he i := by
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · change (ringTestMap B (Pi.evalAlgHom B D i)).left ≫
        (weilRestrictionTensorPointTestMap R B C (∀ j, D j) e
          (fun b => funext (he b))).left ≫
        pullback.fst (Spec.algebraMap R C) (Spec.algebraMap R B) =
      (completedTensorWeilRestrictionFactorTestMap R B C D e he i).left ≫
        pullback.fst (Spec.algebraMap R C) (Spec.algebraMap R B)
    simp only [
      weilRestrictionTensorPointTestMap_fst,
      completedTensorWeilRestrictionFactorTestMap_fst, ringTestMap_left]
    rw [← Spec.map_comp]
    rfl
  · exact (Over.w (ringTestMap B (Pi.evalAlgHom B D i) ≫
        weilRestrictionTensorPointTestMap R B C (∀ j, D j) e
          (fun b => funext (he b)))).trans
      (Over.w (completedTensorWeilRestrictionFactorTestMap R B C D e he i)).symm

/-- The component map agrees exactly with the canonical tensor point
equivalence followed by the original product-ring projection. -/
theorem completedTensorSpaceWeilRestrictionPointMap_eq
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))
    (x : RingPoints R (ringWeilRestrictionSpace R B X h) C) (i : ι) :
    completedTensorSpaceWeilRestrictionPointMap R B C D e he X h x i =
      RingPoints.changeRing (Pi.evalAlgHom B D i)
        (ringWeilRestrictionTensorPointsEquiv R B C (∀ j, D j) e
          (fun b => funext (he b)) X h x) := by
  rw [ringWeilRestrictionTensorPointsEquiv_apply]
  change X.pullback _ x = X.pullback _ (X.pullback _ x)
  rw [← pullback_comp, weilRestrictionTensorPointTestMap_factor]

end Factors

section Naturality

variable (R B C C' : Type u) [CommRing R] [CommRing B] [CommRing C] [CommRing C']
  [Algebra R B] [Algebra R C] [Algebra R C']
  {ι : Type u} (D D' : ι → Type u) [∀ i, CommRing (D i)] [∀ i, CommRing (D' i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  [∀ i, Algebra C' (D' i)] [∀ i, Algebra B (D' i)]
  (e : C ⊗[R] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[R] b) i = algebraMap B (D i) b)
  (e' : C' ⊗[R] B ≃ₐ[C'] (∀ i, D' i))
  (he' : ∀ (b : B) (i : ι), e' (1 ⊗ₜ[R] b) i = algebraMap B (D' i) b)
  (f : C →ₐ[R] C') (g : ∀ i, D i →ₐ[B] D' i)
  (hfg : ∀ (c : C) (i : ι), g i (algebraMap C (D i) c) =
    algebraMap C' (D' i) (f c))

include hfg in
/-- The tensor space point map commutes with compatible original lower
and upper coefficient maps, including integral-to-field inclusions. -/
theorem completedTensorSpaceWeilRestrictionPointMap_natural
    (X : AlgebraicSpace (Spec (CommRingCat.of B)))
    (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))
    (x : RingPoints R (ringWeilRestrictionSpace R B X h) C) (i : ι) :
    completedTensorSpaceWeilRestrictionPointMap R B C' D' e' he' X h
        (RingPoints.changeRing f x) i =
      RingPoints.changeRing (g i)
        (completedTensorSpaceWeilRestrictionPointMap R B C D e he X h x i) := by
  change X.pullback _ (X.pullback _ x) = X.pullback _ (X.pullback _ x)
  rw [← pullback_comp, ← pullback_comp,
    completedTensorWeilRestrictionFactorTestMap_natural R B C C' D D' e he e' he' f g hfg]
  rfl

end Naturality

end Langlands.AlgebraicGeometry.AlgebraicSpace
