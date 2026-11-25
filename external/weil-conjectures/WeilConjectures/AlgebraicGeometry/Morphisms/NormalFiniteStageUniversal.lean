/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.RingTheory.FiniteTypeZDomainNormalizationFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Normal finite replacement of an approximation stage

## References

* Stacks Project, Tag 0EZJ (normal approximation paragraph), and Tags 035E, 035N, 035L, 0335
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

private theorem normalization_finite_int (Z : Scheme.{u}) [IsIntegral Z]
    [LocallyOfFiniteType (specULiftZIsTerminal.from Z)] : IsFinite Z.fromNormalization := by
  let φ := Z.fromSpecFunctionField
  refine φ.isFinite_fromNormalization_of_finite fun U hU hne ↦ ?_
  let := (φ.app U).hom.toAlgebra
  have hηU : genericPoint Z ∈ U :=
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen).mpr (by simpa using hne)
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have hxU : φ (IsLocalRing.closedPoint Z.functionField) ∈ U := by
    convert hηU
    exact fromSpecStalk_closedPoint
  have hφU : φ ⁻¹ᵁ U = ⊤ := preimage_eq_top_of_closedPoint_mem φ hxU
  let θ : Γ(Spec Z.functionField, φ ⁻¹ᵁ U) ≅ Z.functionField :=
    (Spec Z.functionField).presheaf.mapIso (eqToIso hφU.symm).op ≪≫ ΓSpecIso Z.functionField
  have hθφ : φ.app U ≫ θ.hom = Z.germToFunctionField U := by
    rw [Scheme.fromSpecStalk_app hηU]
    simp [θ, φ, Subsingleton.elim (homOfLE le_top) (eqToHom hφU)]
  let : Algebra Γ(Z, U) Z.functionField := (φ.app U ≫ θ.hom).hom.toAlgebra
  have hfrac : IsFractionRing Γ(Z, U) Z.functionField := by
    have := functionField_isFractionRing_of_isAffineOpen Z U hU
    convert this using 1
    exact congrArg (fun a : Γ(Z, U) ⟶ Z.functionField ↦ a.hom.toAlgebra) hθφ
  let q := specULiftZIsTerminal.from Z
  let : Algebra (ULift.{u} ℤ) Γ(Z, U) :=
    ((q.appLE ⊤ U le_top).hom.comp (ΓSpecIso (.of (ULift.{u} ℤ))).inv.hom).toAlgebra
  have : Algebra.FiniteType (ULift.{u} ℤ) Γ(Z, U) :=
    RingHom.FiniteType.comp (HasRingHomProperty.appLE @LocallyOfFiniteType q ‹_›
      ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ le_top) (RingHom.FiniteType.of_surjective _
        (ΓSpecIso (.of (ULift.{u} ℤ))).commRingCatIsoToRingEquiv.symm.surjective)
  have : Algebra.FiniteType ℤ Γ(Z, U) := by
    apply RingHom.finiteType_algebraMap.mp
    have he : (algebraMap (ULift.{u} ℤ) Γ(Z, U)).comp
        ULift.ringEquiv.symm.toRingHom = algebraMap ℤ Γ(Z, U) := Subsingleton.elim _ _
    rw [← he]
    exact RingHom.FiniteType.comp (RingHom.finiteType_algebraMap.mpr inferInstance)
      (RingHom.FiniteType.of_surjective _ ULift.ringEquiv.symm.surjective)
  have := RingTheory.finiteTypeZDomain_integralClosure_finite Γ(Z, U) Z.functionField
  let e : Γ(Spec Z.functionField, φ ⁻¹ᵁ U) ≃ₐ[Γ(Z, U)] Z.functionField :=
    { θ.commRingCatIsoToRingEquiv with commutes' _ := rfl }
  exact Module.Finite.equiv e.mapIntegralClosure.toLinearEquiv.symm

private theorem integral_image {S T : Scheme.{u}} [IsIntegral S]
    (f : S ⟶ T) [QuasiCompact f] : IsIntegral f.image := by
  have : IrreducibleSpace f.image := by
    apply (irreducibleSpace_def _).mpr
    have h := (IrreducibleSpace.isIrreducible_univ S).image f.toImage.base
      f.toImage.continuous.continuousOn
    rw [Set.image_univ] at h
    simpa [f.toImage.denseRange.closure_eq] using h.closure
  have : IsReduced f.image := IsSchemeTheoreticallyDominant.isReduced f.toImage
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- A single approximation stage has a finite normal replacement with its universal
property among normal integral factorizations dominated by `S`. -/
theorem exists_normal_finite_stage_universal {S : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (N : S.NoetherianApproximation) (i : N.I) :
    ∃ (X : Scheme.{u}) (α : S ⟶ X) (p : X ⟶ N.D.obj i),
      α ≫ p = N.π.app i ∧ IsFinite p ∧ IsDominant α ∧ IsIntegral X ∧
      (∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)) ∧
      (∀ (Y : Scheme.{u}) (_ : IsIntegral Y)
        (_ : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y))
        (β : S ⟶ Y) (_ : IsDominant β) (g : Y ⟶ N.D.obj i),
        β ≫ g = N.π.app i → ∃! f : Y ⟶ X, β ≫ f = α ∧ f ≫ p = g) := by
  let t : S ⟶ N.D.obj i := N.π.app i
  have : QuasiCompact t := quasiCompact_of_compactSpace t
  have : IsIntegral t.image := integral_image t
  have hnorm : ∀ x : t.image.normalization,
      IsIntegrallyClosed (t.image.normalization.presheaf.stalk x) :=
    t.image.fromSpecFunctionField.isIntegrallyClosed_stalk_normalization
      (fun x ↦ isIntegrallyClosed_stalk_Spec t.image.functionField x)
  have : LocallyOfFiniteType (specULiftZIsTerminal.from t.image) := by
    rw [specULiftZIsTerminal.hom_ext (specULiftZIsTerminal.from t.image)
      (t.imageι ≫ specULiftZIsTerminal.from (N.D.obj i))]
    infer_instance
  have : IsFinite t.image.fromNormalization := normalization_finite_int t.image
  obtain ⟨α, ⟨hα, hαdom⟩, hαuniq⟩ := existsUnique_lift_normalization_of_dominant hS t.toImage
  have : IsDominant α := hαdom
  let p := t.image.fromNormalization ≫ t.imageι
  refine ⟨t.image.normalization, α, p, ?_, inferInstance, inferInstance,
    inferInstance, hnorm, ?_⟩
  · simp [p, ← Category.assoc, hα, t]
  intro Y hYint hY β hβ g hg
  have : IsSchemeTheoreticallyDominant β := .of_isDominant β
  have hker : t.imageι.ker ≤ g.ker := by
    rw [IdealSheafData.ker_subschemeι]
    change (N.π.app i).ker ≤ g.ker
    rw [← hg, Hom.ker_comp_of_isSchemeTheoreticallyDominant]
  let gZ := IsClosedImmersion.lift t.imageι g hker
  have hgZ : gZ ≫ t.imageι = g := IsClosedImmersion.lift_fac _ _ _
  have hβZ : β ≫ gZ = t.toImage := by
    apply (cancel_mono t.imageι).mp
    rw [Category.assoc, hgZ, hg, Hom.toImage_imageι]
  have : IsDominant gZ := by
    have : IsDominant (β ≫ gZ) := hβZ.symm ▸ inferInstance
    exact IsDominant.of_comp β gZ
  obtain ⟨f, ⟨hf, hfdom⟩, hfuniq⟩ := existsUnique_lift_normalization_of_dominant hY gZ
  have : IsDominant f := hfdom
  have hβf : β ≫ f = α := hαuniq _ ⟨by rw [Category.assoc, hf, hβZ], inferInstance⟩
  refine ⟨f, ⟨hβf, ?_⟩, ?_⟩
  · dsimp only [p]
    rw [← Category.assoc, hf, hgZ]
  · intro f' hf'
    apply hfuniq
    have : IsDominant (β ≫ f') := hf'.1.symm ▸ inferInstance
    refine ⟨?_, IsDominant.of_comp β f'⟩
    apply (cancel_mono t.imageι).mp
    simpa only [Category.assoc, hgZ] using hf'.2

end AlgebraicGeometry.Scheme
