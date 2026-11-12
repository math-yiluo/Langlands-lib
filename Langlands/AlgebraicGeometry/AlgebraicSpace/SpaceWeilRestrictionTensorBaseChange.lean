import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionBaseChange
import Langlands.AlgebraicGeometry.PointTopology.AffineChartWeilRestrictionSpecifiedTensorBaseChange

/-!
# Algebraicity and geometry of tensor base changes of Weil restrictions

The algebraicity of a Weil restriction implies the algebraicity of its
cartesian base change. A specified tensor algebra equivalence supplies the
cartesian square, with both of its original coefficient maps.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

section General

variable {S S' T T' : Scheme.{u}}
variable {g : S' ⟶ S} {f : T ⟶ S} {f' : T' ⟶ S'} {g' : T' ⟶ T}
variable (h : IsPullback f' g' g f) (X' : AlgebraicSpace S')
variable (hX : IsAlgebraicSpace S ((weilRestriction g).obj X'.toSheaf))

include h hX

/-- Algebraicity after cartesian base change follows from algebraicity before
base change; no second representability input is needed. -/
theorem isAlgebraicSpace_weilRestriction_baseChange :
    IsAlgebraicSpace T ((weilRestriction g').obj (baseChange f' X').toSheaf) :=
  isAlgebraicSpace_of_presheafIso
    (weilRestrictionBaseChangePresheafIso h X'.presheaf)
    (isAlgebraicSpace_restrict f ⟨(weilRestriction g).obj X'.toSheaf, hX⟩)

/-- The cartesian base-change isomorphism with algebraicity on the right
derived from the given algebraic Weil restriction. -/
def weilRestrictionBaseChangeIso :
    baseChange f ⟨(weilRestriction g).obj X'.toSheaf, hX⟩ ≅
      (⟨(weilRestriction g').obj (baseChange f' X').toSheaf,
        isAlgebraicSpace_weilRestriction_baseChange h X' hX⟩ : AlgebraicSpace T) :=
  weilRestrictionBaseChangeSpaceIso h X' hX
    (isAlgebraicSpace_weilRestriction_baseChange h X' hX)

/-- Separatedness of the restriction transfers to the cartesian restriction. -/
theorem isSeparated_weilRestriction_baseChange
    (hsep : IsSeparated (⟨(weilRestriction g).obj X'.toSheaf, hX⟩ : AlgebraicSpace S)) :
    IsSeparated (⟨(weilRestriction g').obj (baseChange f' X').toSheaf,
      isAlgebraicSpace_weilRestriction_baseChange h X' hX⟩ : AlgebraicSpace T) :=
  relative_diag_of_iso (@_root_.AlgebraicGeometry.IsClosedImmersion.{u})
    (weilRestrictionBaseChangePresheafIso h X'.presheaf) hsep.baseChange

/-- Quasi-separatedness transfers in the same way. -/
theorem isQuasiSeparated_weilRestriction_baseChange
    (hqs : IsQuasiSeparated
      (⟨(weilRestriction g).obj X'.toSheaf, hX⟩ : AlgebraicSpace S)) :
    IsQuasiSeparated (⟨(weilRestriction g').obj (baseChange f' X').toSheaf,
      isAlgebraicSpace_weilRestriction_baseChange h X' hX⟩ : AlgebraicSpace T) :=
  relative_diag_of_iso (@QuasiCompact.{u})
    (weilRestrictionBaseChangePresheafIso h X'.presheaf) hqs.baseChange

/-- Any atlas property stable under scheme base change transfers to the
cartesian restriction, retaining the base-changed atlas source. -/
theorem hasAtlasProperty_weilRestriction_baseChange
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (hP : HasAtlasProperty P
      (⟨(weilRestriction g).obj X'.toSheaf, hX⟩ : AlgebraicSpace S)) :
    HasAtlasProperty P
      (⟨(weilRestriction g').obj (baseChange f' X').toSheaf,
        isAlgebraicSpace_weilRestriction_baseChange h X' hX⟩ : AlgebraicSpace T) :=
  hP.baseChange.of_iso (weilRestrictionBaseChangePresheafIso h X'.presheaf)

end General

section Tensor

open Langlands.AlgebraicGeometry.PointTopology

variable (R B C D : Type u) [CommRing R] [CommRing B] [CommRing C] [CommRing D]
  [Algebra R B] [Algebra R C] [Algebra C D] [Algebra B D]
  (e : C ⊗[R] B ≃ₐ[C] D)
  (he : ∀ b : B, e (1 ⊗ₜ[R] b) = algebraMap B D b)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The specified tensor equivalence identifies the coefficient spectrum
with the actual pullback spectrum. -/
def weilRestrictionTensorPullbackIso :
    Spec (CommRingCat.of D) ≅
      Limits.pullback (Spec.algebraMap R C) (Spec.algebraMap R B) :=
  (weilCoefficientSpecIso C (C ⊗[R] B) D e).trans (pullbackSpecIso R C B).symm

omit [Algebra B D] in
@[reassoc (attr := simp)]
theorem weilRestrictionTensorPullbackIso_hom_fst :
    (weilRestrictionTensorPullbackIso R B C D e).hom ≫
      pullback.fst (Spec.algebraMap R C) (Spec.algebraMap R B) =
        Spec.algebraMap C D := by
  dsimp only [weilRestrictionTensorPullbackIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, pullbackSpecIso_inv_fst']
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap C (C ⊗[R] B))) = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext e.commutes

include he in
@[reassoc (attr := simp)]
theorem weilRestrictionTensorPullbackIso_hom_snd :
    (weilRestrictionTensorPullbackIso R B C D e).hom ≫
      pullback.snd (Spec.algebraMap R C) (Spec.algebraMap R B) =
        Spec.algebraMap B D := by
  dsimp only [weilRestrictionTensorPullbackIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, pullbackSpecIso_inv_snd]
  exact specifiedTensorCoefficientSpec_comp R B C D e he

include he in
/-- The tensor equivalence and its original-coefficient law give the
cartesian square needed for Weil base change. -/
theorem isPullback_weilRestrictionTensor :
    IsPullback (Spec.algebraMap B D) (Spec.algebraMap C D)
      (Spec.algebraMap R B) (Spec.algebraMap R C) := by
  have hf := weilRestrictionTensorPullbackIso_hom_fst R B C D e
  have hs := weilRestrictionTensorPullbackIso_hom_snd R B C D e he
  have hw : Spec.algebraMap C D ≫ Spec.algebraMap R C =
      Spec.algebraMap B D ≫ Spec.algebraMap R B := by
    rw [← hf, ← hs, Category.assoc, Category.assoc, pullback.condition]
  exact (IsPullback.of_iso_pullback ⟨hw⟩
    (weilRestrictionTensorPullbackIso R B C D e) hf hs).flip

variable (X' : AlgebraicSpace (Spec (CommRingCat.of B)))
  (hX : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X'.toSheaf))

include he hX

/-- Representability of the local tensor restriction is inherited from the
original Weil restriction. -/
theorem isAlgebraicSpace_ringWeilRestriction_tensor :
    IsAlgebraicSpace _
      ((ringWeilRestriction C D).obj (baseChange (Spec.algebraMap B D) X').toSheaf) :=
  isAlgebraicSpace_weilRestriction_baseChange
    (isPullback_weilRestrictionTensor R B C D e he) X' hX

/-- The original Weil space after scalar extension is the Weil space for
the specified tensor algebra and the ordinary original-coefficient base change. -/
def ringWeilRestrictionTensorBaseChangeIso :
    baseChange (Spec.algebraMap R C) (ringWeilRestrictionSpace R B X' hX) ≅
      ringWeilRestrictionSpace C D (baseChange (Spec.algebraMap B D) X')
        (isAlgebraicSpace_ringWeilRestriction_tensor R B C D e he X' hX) :=
  weilRestrictionBaseChangeIso
    (isPullback_weilRestrictionTensor R B C D e he) X' hX

end Tensor

end Langlands.AlgebraicGeometry.AlgebraicSpace
