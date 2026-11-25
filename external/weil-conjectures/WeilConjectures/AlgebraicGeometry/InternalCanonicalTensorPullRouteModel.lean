/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CanonicalCoefficientTensorNormalization
public import WeilConjectures.AlgebraicGeometry.InternalScalarTensorPullModels
import WeilConjectures.AlgebraicGeometry.NativeModulePullbackBraiding
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalTensorCounit

/-! # The canonical tensor route in the common tensor model

Source: Stacks 06YY, 0G7E; integral proper-base-change proof (1), (3).
(auxiliary; not a blueprint node). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
set_option allowUnsafeReducibility true
attribute [local reducible] L CondensedRing.moduleObjectDerivedPullback
attribute [local irreducible] scalarTensorRegularPullIso

/-- The fixed canonical tensor presentation computes the ordinary tensorator model.

Source: Stacks 06YY, 0G7E; integral proper-base-change proof (1), (3),
step 2 of the original tensor-pull normalization argument.
(auxiliary; not a blueprint node).

Proof. Expand the model target and cancel tensoring the coefficient pullback
isomorphism against its inverse. Unfold the canonical normalization to identify
its derived presentation with `derivedTensorPresentationIso` for the restricted
scalar computation counit. Use the native ordinary pullback monoidal structure;
`nativeUpperStar_braiding` verifies its braiding equation directly on balanced
tensor coequalizers. Give its derived pullback the canonical derived monoidal
structure. The native geometric tensor comparison is its oplax tensorator by
`leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison`, and
`residueDerivedMonoidal_counit` supplies the tensor/counit equation. Apply
`Functor.tensorModelRoute_fac` to these equations and the scalar presentation.
After unfolding the model maps its conclusion is the required identity. No
localization tensor comparison is cancelled and no flatness of the coefficient
or complex is assumed. -/
theorem canonical_tensor_pull_route_model (a : Λ ⟶ Λ') [IsMonHom a]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : HomotopyCategory (Modules Λ Y) (.up ℤ)) :
    (L Λ f).map ((canonicalCoefficientTensorNormalization a Y).derived.hom.app
      (DerivedCategory.Qh.obj P)) ≫
        ((CondensedRing.leftDerivedUpperStarTensor Λ f).app
          (DerivedCategory.Qh.obj P)).app (B a Y) ≫
        ((L Λ f).obj (DerivedCategory.Qh.obj P) ◁ (scalarTensorRegularPullIso a f).hom) ≫
        scalarTensorPullModelTarget a f P = scalarTensorPullModelMap a f P := by
  let F := CondensedRing.upperStar Λ f
  let G := L Λ f
  let γ := pullCounit (Λ := Λ) f
  letI hm : F.Monoidal := CondensedRing.monoidal_upperStar Λ f
  letI hdm : G.Monoidal := CategoryTheory.Functor.residueDerivedMonoidal F
  letI : F.OplaxMonoidal := hm.toOplaxMonoidal
  have hδ := CategoryTheory.Functor.residueDerivedMonoidal_counit F
  have hG : ∀ M N : Modules Λ Y, F.map (β_ M N).hom ≫
      Functor.OplaxMonoidal.δ F N M = Functor.OplaxMonoidal.δ F M N ≫
        (β_ (F.obj M) (F.obj N)).hom := by
    exact CondensedRing.nativeUpperStar_braiding Λ f
  let H : DerivedCategory (Modules Λ Y) ⥤ DerivedCategory (Modules Λ Y) := D a Y ⋙ V a Y
  let ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft (B₀ a Y)).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh := by
    unfold H D V
    exact Mod.tensorPresentationDerivedCounit (coefficientMap a Y)
  letI hε : H.IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso (Modules Λ Y) (.up ℤ)) := by
    unfold H ε D V
    exact Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor
      (coefficientMap a Y)
  have hcan :
      (canonicalCoefficientTensorNormalization a Y).derived.hom =
        (CategoryTheory.derivedTensorPresentationIso (B₀ a Y) H ε).hom := by
    unfold canonicalCoefficientTensorNormalization Mod.residueDerivedTensorIso H ε D
    rfl
  have htensor :
      ((CondensedRing.leftDerivedUpperStarTensor Λ f).app
          (DerivedCategory.Qh.obj P)).app (B a Y) =
        Functor.OplaxMonoidal.δ G (DerivedCategory.Qh.obj P)
          ((DerivedCategory.singleFunctor (Modules Λ Y) 0).obj (B₀ a Y)) := by
    rw [CondensedRing.leftDerivedUpperStarTensor_eq_leftDerivedTensorComparison]
    rfl
  have h := CategoryTheory.Functor.tensorModelRoute_fac F G γ hδ hG
      (B₀ a Y) H ε P
  rw [hcan, htensor]
  simpa only [F, G, γ, H, ε, scalarTensorPullModelTarget,
    scalarTensorPullModelMap, Category.assoc, whiskerLeft_hom_inv_assoc, id_eq] using h

end AlgebraicGeometry.ProEtale.QuotientChange
