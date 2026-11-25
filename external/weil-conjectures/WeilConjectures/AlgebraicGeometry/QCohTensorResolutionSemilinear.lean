/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartCoordinates
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackTilde
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The affine adjunction for semilinear maps along an affine open immersion. -/
noncomputable def tensorResolutionSemilinearAdjunction {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)] :
    tilde.functor A ⋙ Scheme.Modules.restrictFunctor (Spec.map φ) ⊣
      moduleSpecΓFunctor (R := B) ⋙ ModuleCat.restrictScalars φ.hom :=
  ((tilde.adjunction (R := A)).comp (Scheme.Modules.restrictAdjunction (Spec.map φ)))
    |>.ofNatIsoRight (Scheme.Modules.pushforwardSpecMapCompΓIso φ)

/-- Sheafification of a semilinear map, using the affine adjunction. -/
noncomputable def tensorResolutionSemilinearMap {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N) :
    (Scheme.Modules.restrictFunctor (Spec.map φ)).obj (tilde M) ⟶ tilde N :=
  ((tensorResolutionSemilinearAdjunction φ).homEquiv M (tilde N)).symm
    (f ≫ (ModuleCat.restrictScalars φ.hom).map (tilde.isoTop N).hom)

/-- The sheafified semilinear map has the prescribed value on section generators. -/
theorem tensorResolutionSemilinearMap_unit {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N) (m : M) :
    (tensorResolutionSemilinearMap φ f).app ⊤
      (((Scheme.Modules.restrictAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
        (tilde.toOpen M ⊤ m)) = tilde.toOpen N ⊤ (f m) := by
  let e := (tensorResolutionSemilinearAdjunction φ).homEquiv M (tilde N)
  have h := congrArg ModuleCat.Hom.hom
    (e.apply_symm_apply (f ≫ (ModuleCat.restrictScalars φ.hom).map (tilde.isoTop N).hom))
  exact DFunLike.congr_fun h m

/-- Sheafification commutes with precomposition by a linear map. -/
theorem tensorResolutionSemilinearMap_precomp {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {M M' : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (a : M ⟶ M') (f : M' ⟶ (ModuleCat.restrictScalars φ.hom).obj N) :
    (Scheme.Modules.restrictFunctor (Spec.map φ)).map (tilde.map a) ≫
      tensorResolutionSemilinearMap φ f = tensorResolutionSemilinearMap φ (a ≫ f) := by
  apply ((tensorResolutionSemilinearAdjunction φ).homEquiv M (tilde N)).injective
  change ((tensorResolutionSemilinearAdjunction φ).homEquiv M (tilde N))
    ((tilde.functor A ⋙ Scheme.Modules.restrictFunctor (Spec.map φ)).map a ≫ _) = _
  rw [Adjunction.homEquiv_naturality_left]
  simp only [tensorResolutionSemilinearMap, Equiv.apply_symm_apply, Category.assoc]

/-- Sheafification commutes with postcomposition by a linear map. -/
theorem tensorResolutionSemilinearMap_postcomp {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {M : ModuleCat.{u} A} {N N' : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N) (b : N ⟶ N') :
    tensorResolutionSemilinearMap φ f ≫ tilde.map b =
      tensorResolutionSemilinearMap φ (f ≫ (ModuleCat.restrictScalars φ.hom).map b) := by
  apply ((tensorResolutionSemilinearAdjunction φ).homEquiv M (tilde N')).injective
  rw [Adjunction.homEquiv_naturality_right]
  simp only [tensorResolutionSemilinearMap, Equiv.apply_symm_apply]
  change (f ≫ (ModuleCat.restrictScalars φ.hom).map (tilde.isoTop N).hom) ≫
      (ModuleCat.restrictScalars φ.hom).map ((moduleSpecΓFunctor (R := B)).map (tilde.map b)) =
    (f ≫ (ModuleCat.restrictScalars φ.hom).map b) ≫
      (ModuleCat.restrictScalars φ.hom).map (tilde.isoTop N').hom
  apply ModuleCat.hom_ext
  ext m
  change (tilde.map b).app ⊤ (tilde.toOpen N ⊤ (f m)) =
    tilde.toOpen N' ⊤ (b (f m))
  exact congr($(tilde.toOpen_map_app b ⊤) (f m))

/-- Sheafify a chain map that is semilinear in every degree. -/
noncomputable def tensorResolutionSemilinearComplexMap {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)] {ι : Type*} (c : ComplexShape ι)
    (E : HomologicalComplex (ModuleCat.{u} A) c)
    (F : HomologicalComplex (ModuleCat.{u} B) c)
    (a : E ⟶ ((ModuleCat.restrictScalars φ.hom).mapHomologicalComplex c).obj F) :
    (((Scheme.Modules.restrictFunctor (Spec.map φ)).mapHomologicalComplex c).obj
      (((tilde.functor A).mapHomologicalComplex c).obj E)) ⟶
      ((tilde.functor B).mapHomologicalComplex c).obj F where
  f i := tensorResolutionSemilinearMap φ (a.f i)
  comm' i j hij := by
    symm
    change (Scheme.Modules.restrictFunctor (Spec.map φ)).map (tilde.map (E.d i j)) ≫
        tensorResolutionSemilinearMap φ (a.f j) =
      tensorResolutionSemilinearMap φ (a.f i) ≫ tilde.map (F.d i j)
    rw [tensorResolutionSemilinearMap_precomp, tensorResolutionSemilinearMap_postcomp]
    congr 1
    exact (a.comm i j).symm

/-- Restricting an affine associated sheaf is sheafified extension of scalars,
with the comparison determined by the common adjunction. -/
noncomputable def tensorResolutionSemilinearIso {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)] :
    tilde.functor A ⋙ Scheme.Modules.restrictFunctor (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor B :=
  (tensorResolutionSemilinearAdjunction φ).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := B)))

/-- The adjoint construction agrees with scalar extension followed by sheafification. -/
theorem tensorResolutionSemilinearMap_eq {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)]
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (f : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N) :
    tensorResolutionSemilinearMap φ f =
      (tensorResolutionSemilinearIso φ).hom.app M ≫
        tilde.map (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M N).symm f) := by
  apply ((tensorResolutionSemilinearAdjunction φ).homEquiv M (tilde N)).injective
  simp only [tensorResolutionSemilinearMap, Equiv.apply_symm_apply]
  rw [Adjunction.homEquiv_naturality_right]
  dsimp only [tensorResolutionSemilinearIso]
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  let β := ((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M N).symm f
  apply ModuleCat.hom_ext
  ext m
  have hβ := congrArg ModuleCat.Hom.hom
    (((ModuleCat.extendRestrictScalarsAdj φ.hom).homEquiv M N).apply_symm_apply f)
  change tilde.toOpen N ⊤ (f m) =
    (tilde.map β).app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
        (((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M) m))
  rw [show (tilde.map β).app ⊤
      (tilde.toOpen ((ModuleCat.extendScalars φ.hom).obj M) ⊤
        (((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M) m)) =
      tilde.toOpen N ⊤ (β (((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M) m)) from
    congr($(tilde.toOpen_map_app β ⊤)
      (((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M) m))]
  exact congrArg (fun n : N ↦ tilde.toOpen N ⊤ n) (DFunLike.congr_fun hβ m).symm

/-- Scalar extension for an affine open immersion is exact. -/
theorem tensorResolutionExtendScalars_preservesHomology {A B : CommRingCat.{u}}
    (φ : A ⟶ B) [IsOpenImmersion (Spec.map φ)] :
    (ModuleCat.extendScalars.{u, u, u} φ.hom).PreservesHomology := by
  let TA := tilde.functor A
  let TB := tilde.functor B
  let L := ModuleCat.extendScalars.{u, u, u} φ.hom
  let R := Scheme.Modules.restrictFunctor (Spec.map φ)
  have : TA.PreservesHomology := tilde_preservesHomology A
  have : PreservesFiniteLimits TA := Functor.preservesFiniteLimits_of_preservesHomology TA
  have : PreservesFiniteLimits (TA ⋙ R) := inferInstance
  have : PreservesFiniteLimits (L ⋙ TB) :=
    preservesFiniteLimits_of_natIso (tensorResolutionSemilinearIso φ)
  have : PreservesFiniteLimits L := preservesFiniteLimits_of_reflects_of_preserves L TB
  infer_instance

end AlgebraicGeometry
