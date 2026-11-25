/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.IntegralFiniteScalarModelDefinitions
import WeilConjectures.Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarProjectionTensorUnit
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarProjectionShift
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! The distinguished-triangle package for the finite-free scalar projection.

## References

* Stacks Tag 0944
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.IntegralFiniteScalar
open CondensedRing

private abbrev scalarProjectionGeneric
    {C D : Type*} [Category* C] [Category* D]
    [mc : MonoidalCategory C] [md : MonoidalCategory D] {L : D ⥤ C} {R : C ⥤ D}
    (adj : L ⊣ R)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C)) (K : C) :
    tensorRight (R.obj K) ⟶ (L ⋙ tensorRight K) ⋙ R :=
  (adj.rightAdjointProjectionMap
    (T_C := (curriedTensor C).flip) (T_D := (curriedTensor D).flip)
    ((flipFunctor _ _ _).map δ)).app K

private theorem scalarProjectionGeneric_transport
    {C D : Type*} [Category* C] [Category* D]
    [mc : MonoidalCategory C] [md : MonoidalCategory D] {L F : D ⥤ C} {R : C ⥤ D}
    (adj : L ⊣ R)
    (δ : (Functor.postcompose₂.obj L).obj (curriedTensor D) ⟶
      (((Functor.whiskeringLeft₂ C).obj L).obj L).obj (curriedTensor C))
    (τ : L ≅ F) (B : D) (P : C) (e : F.obj B ≅ P) (K : C) :
    (adj.ofNatIsoLeft τ).homEquiv _ _
      ((τ.inv.app (B ⊗ R.obj K) ≫ (δ.app B).app (R.obj K) ≫
        (τ.hom.app B ⊗ₘ τ.hom.app (R.obj K))) ≫
        (e.hom ⊗ₘ (adj.ofNatIsoLeft τ).counit.app K)) =
      (scalarProjectionGeneric adj δ K).app B ≫
        R.map ((τ.hom.app B ≫ e.hom) ▷ K) := by
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  unfold scalarProjectionGeneric
  rw [Adjunction.rightAdjointProjectionMap_app_app,
    ← Adjunction.homEquiv_naturality_right]
  apply (adj.homEquiv _ _).congr_arg
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    tensorHom_comp_tensorHom, Iso.hom_inv_id_app_assoc]
  change (δ.app B).app (R.obj K) ≫
    ((τ.hom.app B ≫ e.hom) ⊗ₘ adj.counit.app K) = _
  rw [tensorHom_def']
  rfl

private theorem projection_eq_native
    (Λ : ScalarSixRing.{u}) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B : DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y))
    (P : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X))
    (e : (scalarSixPull Λ f).obj B ≅ P)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    projection Λ f B P e K = (scalarFirstProjection Λ.X f K).app B ≫
      ((CondensedRing.lowerStar Λ.X f).rightDerivedFunctor).map
        (((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).hom.app B ≫
          e.hom) ▷ K) := by
  unfold projection tensorPull geometricAdjunction scalarFirstProjection
  apply scalarProjectionGeneric_transport

private abbrev projectionSource
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D} (_ : F ⟶ G) : C ⥤ D := F

private abbrev projectionTarget
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D} (_ : F ⟶ G) : C ⥤ D := G

set_option backward.defeqAttrib.useBackward true in
private def triangleMap
    {C D : Type*} [Category* C] [Category* D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (α : F ⟶ G) [NatTrans.CommShift α ℤ] (T : Triangle C) :
    F.mapTriangle.obj T ⟶ G.mapTriangle.obj T :=
  Triangle.homMk _ _ (α.app T.obj₁) (α.app T.obj₂) (α.app T.obj₃)
    (α.naturality _) (α.naturality _) (by
      dsimp
      simp only [Category.assoc, NatTrans.shift_app_comm α (1 : ℤ) T.obj₁,
        NatTrans.naturality_assoc])

private def replaceThird
    {C : Type*} [Category* C] [HasShift C ℤ] (T : Triangle C) {W : C}
    (e : T.obj₃ ≅ W) : Triangle C :=
  Triangle.mk T.mor₁ (T.mor₂ ≫ e.hom) (e.inv ≫ T.mor₃)

private def replaceThirdIso
    {C : Type*} [Category* C] [HasShift C ℤ] (T : Triangle C) {W : C}
    (e : T.obj₃ ≅ W) : T ≅ replaceThird T e :=
  Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e
    (by simp [replaceThird]) (by simp [replaceThird]) (by simp [replaceThird])

private def pointSingleDerivedUnit
    (Λ : ScalarSixRing.{u}) (Y : Scheme.{u}) :
    DerivedCategory.Q.obj
        (((pointPull Λ Y).mapHomologicalComplex (.up ℤ)).obj
          ((CochainComplex.singleFunctor (PointModules Λ) 0).obj (Mod.regular Λ.X))) ≅
      𝟙_ (DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) :=
  DerivedCategory.Q.mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (pointPull Λ Y) (.up ℤ) 0).app
        (Mod.regular Λ.X)) ≪≫
    DerivedCategory.Q.mapIso ((CochainComplex.singleFunctor _ 0).mapIso
      ((sfbPullbackFromPoint Y).mapModUnitIso (R := Λ.X)).symm) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ
      (ModuleRingedComparison.internalModules Λ.X Y) 0).app _).symm ≪≫
    DerivedCategory.singleFunctorObjUnitIso
      (ModuleRingedComparison.internalModules Λ.X Y)

/-- The coefficient projection sends the mapping-cone triangle of `S.f` to a distinguished
triangle whose first two components are isomorphisms and whose third component is
`projection` after the `modelPull` identification. -/
theorem finiteFreeScalarProjection_triangle
    (Λ : ScalarSixRing.{u}) (S : ShortComplex (PointModules Λ)) (r : ℕ)
    (e₁ : S.X₁ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    (e₂ : S.X₂ ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X))
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (ModuleRingedComparison.internalModules Λ.X X)) :
    ∃ (T T' : Triangle (DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)))
      (φ : T ⟶ T'),
      T ∈ distTriang (DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) ∧
      T' ∈ distTriang (DerivedCategory (ModuleRingedComparison.internalModules Λ.X Y)) ∧
      T.obj₃ = DerivedCategory.Q.obj (complex Λ S Y) ⊗
        (moduleObjectDerivedPushforward Λ.X f).obj K ∧
      T'.obj₃ = (moduleObjectDerivedPushforward Λ.X f).obj
        (DerivedCategory.Q.obj (complex Λ S X) ⊗ K) ∧
      IsIso φ.hom₁ ∧ IsIso φ.hom₂ ∧
      ∀ (hY : T.obj₃ = DerivedCategory.Q.obj (complex Λ S Y) ⊗
          (moduleObjectDerivedPushforward Λ.X f).obj K)
        (hX : T'.obj₃ = (moduleObjectDerivedPushforward Λ.X f).obj
          (DerivedCategory.Q.obj (complex Λ S X) ⊗ K)),
        eqToHom hY.symm ≫ φ.hom₃ ≫ eqToHom hX =
          projection Λ f (DerivedCategory.Q.obj (complex Λ S Y))
            (DerivedCategory.Q.obj (complex Λ S X)) (modelPull Λ S f) K := by
  classical
  let R := (CondensedRing.lowerStar Λ.X f).rightDerivedFunctor
  let α := scalarFirstProjection Λ.X f K
  let F := projectionSource α
  let G := projectionTarget α
  have : R.Additive :=
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ.X f).right_adjoint_additive
  have : NatTrans.CommShift α ℤ := scalarProjection_commShift Λ.X f K
  let H := (pointPull Λ Y).mapHomologicalComplex (.up ℤ)
  let J := CochainComplex.singleFunctor (PointModules Λ) 0
  let U := DerivedCategory.Q.mapTriangle.obj
    (H.mapTriangle.obj (CochainComplex.mappingCone.triangle (J.map S.f)))
  have hU : U ∈ distTriang _ := by
    exact isomorphic_distinguished _
      (DerivedCategory.mappingCone_triangle_distinguished (H.map (J.map S.f))) _
      (DerivedCategory.Q.mapTriangle.mapIso
        (CochainComplex.mappingCone.mapTriangleIso (J.map S.f) (pointPull Λ Y)))
  let α₀ := Functor.whiskerLeft (J ⋙ H ⋙ DerivedCategory.Q) α
  have hu : IsIso (α₀.app (Mod.regular Λ.X)) :=
    (NatTrans.isIso_app_iff_of_iso α (pointSingleDerivedUnit Λ Y)).mpr
      (scalarProjection_tensorUnit_isIso Λ.X f K)
  have hend (P : PointModules Λ)
      (e : P ≅ biproduct (fun _ : Fin r ↦ Mod.regular Λ.X)) :
      IsIso (α₀.app P) :=
    (NatTrans.isIso_app_iff_of_iso α₀ e).mpr
      (NatTrans.isIso_app_biproduct α₀ _ (fun _ ↦ hu))
  let T := F.mapTriangle.obj U
  let V := G.mapTriangle.obj U
  let e : V.obj₃ ≅ R.obj (DerivedCategory.Q.obj (complex Λ S X) ⊗ K) :=
    R.mapIso (whiskerRightIso
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory Λ.X f).app _ ≪≫
        modelPull Λ S f) K)
  let T' := replaceThird V e
  let φ : T ⟶ T' := triangleMap α U ≫ (replaceThirdIso V e).hom
  refine ⟨T, T', φ, F.map_distinguished U hU, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · exact isomorphic_distinguished _ (G.map_distinguished U hU) _
      (replaceThirdIso V e).symm
  · change IsIso (α₀.app S.X₁ ≫ 𝟙 _)
    simpa only [Category.comp_id] using hend S.X₁ e₁
  · change IsIso (α₀.app S.X₂ ≫ 𝟙 _)
    simpa only [Category.comp_id] using hend S.X₂ e₂
  · intro hY hX
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    exact (projection_eq_native Λ f _ _ (modelPull Λ S f) K).symm

end AlgebraicGeometry.ProEtale.IntegralFiniteScalar
