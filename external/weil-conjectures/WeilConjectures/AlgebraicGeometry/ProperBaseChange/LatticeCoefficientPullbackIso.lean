/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousCoefficientPullbackIso

/-!
# Immersion restriction in the lattice coefficient presentation

## References

* Bhatt--Scholze, Lemma 6.5.8(1), Definition 6.8.1 and the paragraph before Definition 6.8.6
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

private def coefficientPresentation (X : Scheme.{u})
    {T S : Type u} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (e : T ≃+* S) (he : Continuous e) (hei : Continuous e.symm) :
    latticeCoefficientSheaf X T ≅ Scheme.continuousCoefficientSheaf X (ULift.{u + 1} S) := by
  apply (fullyFaithfulSheafToPresheaf _ _).preimageIso
  refine NatIso.ofComponents (fun V ↦ RingEquiv.toCommRingCatIso ?_) ?_
  · exact
      { toFun := fun f ↦
          ⟨fun x ↦ ULift.up (e (f.down x)),
            continuous_uliftUp.comp (he.comp f.down.continuous)⟩
        invFun := fun f ↦ ULift.up
          ⟨fun x ↦ e.symm (f x).down,
            hei.comp (continuous_uliftDown.comp f.continuous)⟩
        left_inv := by intro f; apply ULift.ext; ext x; exact e.symm_apply_apply _
        right_inv := by intro f; ext x; exact e.apply_symm_apply _
        map_mul' := by intro f g; ext x; exact e.map_mul _ _
        map_add' := by intro f g; ext x; exact e.map_add _ _ }
  · intro V W f
    rfl

private theorem coefficientPresentation_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {T S : Type u} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (e : T ≃+* S) (he : Continuous e) (hei : Continuous e.symm) :
    (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
        (coefficientPresentation Y e he hei).hom ≫
          Scheme.continuousCoefficientPullback (ULift.{u + 1} S) f =
      continuousCoefficientInverseImageMap f T ≫ (coefficientPresentation X e he hei).hom := by
  let adj := Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}
  unfold Scheme.continuousCoefficientPullback continuousCoefficientInverseImageMap
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1

private theorem coefficientPresentation_isIso
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {T S : Type u} [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TopologicalSpace S] [CommRing S] [IsTopologicalRing S]
    (e : T ≃+* S) (he : Continuous e) (hei : Continuous e.symm)
    [IsIso (Scheme.continuousCoefficientPullback (ULift.{u + 1} S) f)] :
    IsIso (continuousCoefficientInverseImageMap f T) := by
  have h : IsIso (continuousCoefficientInverseImageMap f T ≫
      (coefficientPresentation X e he hei).hom) := by
    rw [← coefficientPresentation_pullback f e he hei]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (coefficientPresentation X e he hei).hom

/-- Canonical coefficient pullback along an immersion is invertible in both the integral
and rational lattice presentations. The maps are the adjuncts of precomposition with the
base-change projection, so the result fixes their normalization as well as their objects.
-/
theorem latticeCoefficientPullback_isIso (l : ℕ) [Fact l.Prime] (E : Type u)
    [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [IsImmersion f] :
    IsIso (continuousCoefficientInverseImageMap f (latticeCoefficientIntegers l E)) ∧
      IsIso (continuousCoefficientInverseImageMap f
        (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))) := by
  let := Scheme.coefficientExtensionNormedField l E
  obtain ⟨hA, hE⟩ := Scheme.continuousCoefficientPullback_isIso l E Y f
  let := hA
  let := hE
  let e := WithAbs.equiv (Padic.coefficientExtensionAbsoluteValue l E)
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  let ei := RingEquiv.restrict e (latticeCoefficientIntegers l E)
    (Padic.coefficientExtensionIntegers l E) (fun _ ↦ Iff.rfl)
  have hei : Isometry ei := by
    intro x y
    exact he x.val y.val
  refine ⟨coefficientPresentation_isIso f ei hei.continuous ?_,
    coefficientPresentation_isIso f e he.continuous ?_⟩
  · exact hei.comp_continuous_iff.mp (by
    convert (continuous_id : Continuous (id : _ → _)) using 1
    funext x
    exact ei.apply_symm_apply x)
  · exact he.comp_continuous_iff.mp (by
    convert (continuous_id : Continuous (id : _ → _)) using 1
    funext x
    exact e.apply_symm_apply x)

end AlgebraicGeometry.ProEtale
