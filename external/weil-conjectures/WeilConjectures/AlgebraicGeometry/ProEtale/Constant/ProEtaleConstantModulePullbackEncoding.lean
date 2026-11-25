/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement

/-!
# Pullback and restriction to constant scalars

## References

* Stacks Project, Tags 093I, 03D3 and 098T(2)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (B : Type u) [CommRing B]

private noncomputable def coefficientIso
    [IsIso (proEtaleCoefficientInverseImageMap f B)] :=
  asIso (proEtaleCoefficientInverseImageMap f B)

private theorem coefficient_adjunct [IsIso (proEtaleCoefficientInverseImageMap f B)] :
    proEtaleRingDirectImageMap f (proEtaleConstantRing Y B) (proEtaleConstantRing X B)
      (coefficientIso f B) = proEtaleCoefficientDirectImageMap f B := by
  let adj := proEtaleSheafAdjunction f CommRingCat.{u + 1}
  change adj.unit.app _ ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
    ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
      (proEtaleCoefficientDirectImageMap f B) ≫ adj.counit.app _) = _
  exact (adj.homEquiv _ _).apply_symm_apply (proEtaleCoefficientDirectImageMap f B)

private theorem constant_sections :
    toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B))) ≫
      (proEtaleCoefficientDirectImageMap f B).hom =
    Functor.whiskerLeft (proEtaleBaseChange f).op
      (toSheafify (ProEt.topology X)
        ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B)))) := by
  exact ((sheafificationAdjunction (ProEt.topology Y) CommRingCat.{u + 1}).homEquiv
    _ _).apply_symm_apply _

private noncomputable def directImageComparison
    [IsIso (proEtaleCoefficientInverseImageMap f B)] :
    proEtaleRingModuleDirectImage f (proEtaleConstantRing Y B) (proEtaleConstantRing X B)
        (coefficientIso f B) ⋙ proEtaleModuleRestriction Y B ≅
      proEtaleModuleRestriction X B ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f := by
  refine NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    (NatIso.ofComponents (fun U ↦ ?_) ?_)) ?_
  · let P := (((proEtaleRingModuleDirectImage f (proEtaleConstantRing Y B)
        (proEtaleConstantRing X B) (coefficientIso f B) ⋙
          proEtaleModuleRestriction Y B).obj M).obj.obj U)
    let Q := (((proEtaleModuleRestriction X B ⋙
        ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj M).obj.obj U)
    change P ≅ Q
    refine (show (P : Type (u + 1)) ≃ₗ[ULift.{u + 1, u} B] Q from
      { toFun := fun m ↦ m
        invFun := fun m ↦ m
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun b m ↦ ?_ }).toModuleIso
    change ((proEtaleRingDirectImageMap f (proEtaleConstantRing Y B)
        (proEtaleConstantRing X B) (coefficientIso f B)).hom.app U).hom
          (((proEtaleModuleScalarUnit Y B).app U).hom b) •
          (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m) =
      (((proEtaleModuleScalarUnit X B).app ((proEtaleBaseChange f).op.obj U)).hom b) •
          (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m)
    rw [coefficient_adjunct]
    exact congrArg (fun r ↦ r •
      (show M.val.obj ((proEtaleBaseChange f).op.obj U) from m))
      (ConcreteCategory.congr_hom (congr_app (constant_sections f B) U) b)
  · intro U V a
    ext m
    rfl
  · intro M N a
    ext U m
    rfl

/-- Restriction to constant scalars commutes with canonical module pullback when the
canonical coefficient inverse-image map is invertible. -/
theorem proEtaleModuleRestriction_pullback_of_isIso
    [IsIso (proEtaleCoefficientInverseImageMap f B)]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
    Nonempty ((proEtaleModuleRestriction X B).obj (proEtaleConstantModulePullback f B F) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj
        ((proEtaleModuleRestriction Y B).obj F)) := by
  let EX := proEtaleModuleEncoding X B
  let EY := proEtaleModuleEncoding Y B
  let L := ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f
  let R := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f
  let adj := EY.toAdjunction.comp
    ((ProEtale.upperStarLowerStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).comp EX.symm.toAdjunction)
  let eR : EX.functor ⋙ R ⋙ EY.inverse ≅
      proEtaleRingModuleDirectImage f (proEtaleConstantRing Y B) (proEtaleConstantRing X B)
        (coefficientIso f B) :=
    (isoWhiskerRight (directImageComparison f B).symm EY.inverse) ≪≫
      isoWhiskerLeft _ EY.unitIso.symm
  let adj' := adj.ofNatIsoRight eR
  let e := (proEtaleRingModuleAdjunction f (proEtaleConstantRing Y B)
    (proEtaleConstantRing X B) (coefficientIso f B)).leftAdjointUniq adj'
  exact ⟨EX.functor.mapIso (e.app F) ≪≫ EX.counitIso.app (L.obj (EY.functor.obj F))⟩

/-- Restriction to constant scalars commutes with canonical pullback for finite rings. -/
theorem proEtaleModuleRestriction_pullback [Finite B]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y B)) :
    Nonempty ((proEtaleModuleRestriction X B).obj (proEtaleConstantModulePullback f B F) ≅
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) f).obj
        ((proEtaleModuleRestriction Y B).obj F)) := by
  have : IsIso (proEtaleCoefficientInverseImageMap f B) := by
    let Q := (Functor.const ℕᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B))
    have : ∀ n, Finite (Q.obj n) := fun _ ↦ inferInstanceAs (Finite (ULift.{u + 1, u} B))
    exact (proEtale_profinite_coefficient_inverse_image
      ((Functor.const ℕᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} B)))).1 X Y f
        (Opposite.op 0)
  exact proEtaleModuleRestriction_pullback_of_isIso f B F

end AlgebraicGeometry.Scheme
