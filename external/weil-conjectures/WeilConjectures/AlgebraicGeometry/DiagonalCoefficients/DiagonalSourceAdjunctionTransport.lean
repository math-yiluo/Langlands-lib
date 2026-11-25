/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteComparison
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement

/-! # Exact adjunction transport on single objects

Source: diagonal tower coefficient changes (1), exact scalar and finite-realization adjunctions.
(blueprint: lem-diagonal-source-adjunction-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

section OrdinaryTransport

variable {C D K : Type*} [Category C] [Category D] [Category K]

private theorem equivalence_forget_transpose (e : C ≌ D) (U : D ⥤ K) (V : C ⥤ K)
    (α : e.functor ⋙ U ≅ V) {M : C} {N : D} (f : e.functor.obj M ⟶ N) :
    V.map (e.toAdjunction.homEquiv _ _ f) ≫
        (α.inv.app (e.inverse.obj N) ≫ U.map (e.counitIso.hom.app N)) =
      α.inv.app M ≫ U.map f := by
  rw [Adjunction.homEquiv_apply, Functor.map_comp]
  have hn := α.inv.naturality (e.inverse.map f)
  have hu := α.inv.naturality (e.unitIso.hom.app M)
  dsimp only [Functor.comp_map] at hn hu
  simp only [Category.assoc]
  erw [reassoc_of% hn, reassoc_of% hu, ← U.map_comp]
  have hc := e.counitIso.hom.naturality f
  dsimp only [Functor.comp_map, Functor.id_map] at hc
  rw [hc]
  simp only [← U.map_comp]
  have ht : e.functor.map (e.unitIso.hom.app M) ≫
      (e.counitIso.hom.app (e.functor.obj M) ≫ f) = f := by
    erw [← Category.assoc, e.functor_unitIso_comp, Category.id_comp]
  exact congrArg (fun k ↦ α.inv.app M ≫ U.map k) ht

private theorem equivalence_forget_inverse_naturality
    (e : C ≌ D) (U : D ⥤ K) (V : C ⥤ K) (α : e.functor ⋙ U ≅ V)
    {M N : D} (f : M ⟶ N) :
    V.map (e.inverse.map f) ≫
        (α.inv.app (e.inverse.obj N) ≫ U.map (e.counitIso.hom.app N)) =
      (α.inv.app (e.inverse.obj M) ≫ U.map (e.counitIso.hom.app M)) ≫ U.map f := by
  have hn := α.inv.naturality (e.inverse.map f)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  simp only [Category.assoc, ← U.map_comp]
  erw [e.counitIso.hom.naturality f]
  rfl

end OrdinaryTransport

section ExactTransport

variable {C D K : Type*} [Category C] [Category D] [Category K]
  [Abelian C] [Abelian D] [Abelian K]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory K]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem equivalence_counit_single (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] (N : D) :
    e.functor.mapDerivedCategory.map ((e.inverse.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
        e.mapDerivedCategory.counitIso.hom.app ((DerivedCategory.singleFunctor D 0).obj N) =
      (e.functor.mapDerivedCategorySingleFunctor 0).hom.app (e.inverse.obj N) ≫
        (DerivedCategory.singleFunctor D 0).map (e.counitIso.hom.app N) := by
  rw [← cancel_epi
    (e.functor.mapDerivedCategory.map ((e.inverse.mapDerivedCategorySingleFunctor 0).hom.app N))]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  change (Functor.mapDerivedCategoryCompIso e.inverse e.functor).hom.app _ ≫
      (Functor.mapDerivedCategoryNatIso e.counitIso).hom.app _ ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app _ = _
  rw [SheafExactDegreeZero.derived_id_single,
    Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor e.inverse e.functor N]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]

private theorem equivalence_homEquiv_single (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] (M : C) (N : D)
    (f : e.functor.obj M ⟶ N) :
    e.mapDerivedCategory.toAdjunction.homEquiv _ _
        ((e.functor.mapDerivedCategorySingleFunctor 0).hom.app M ≫
          (DerivedCategory.singleFunctor D 0).map f) =
      (DerivedCategory.singleFunctor C 0).map (e.toAdjunction.homEquiv _ _ f) ≫
        (e.inverse.mapDerivedCategorySingleFunctor 0).inv.app N := by
  apply (e.mapDerivedCategory.toAdjunction.homEquiv _ _).symm.injective
  simp only [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply, Functor.map_comp,
    Category.assoc]
  change _ = e.functor.mapDerivedCategory.map
      ((DerivedCategory.singleFunctor C 0).map (e.toAdjunction.homEquiv _ _ f)) ≫
    e.functor.mapDerivedCategory.map ((e.inverse.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
      e.mapDerivedCategory.counitIso.hom.app ((DerivedCategory.singleFunctor D 0).obj N)
  rw [equivalence_counit_single]
  have hn := (e.functor.mapDerivedCategorySingleFunctor 0).hom.naturality
    (e.toAdjunction.homEquiv _ _ f)
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn, ← Functor.map_comp]
  exact congrArg (fun k ↦ (e.functor.mapDerivedCategorySingleFunctor 0).hom.app M ≫
    (DerivedCategory.singleFunctor D 0).map k)
      ((e.toAdjunction.homEquiv _ _).symm_apply_apply f).symm

private theorem composite_homEquiv_single
    (R : D ⥤ C) (S : K ⥤ D) [R.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    {F : DerivedCategory C ⥤ DerivedCategory D}
    {G : DerivedCategory D ⥤ DerivedCategory K}
    (a : F ⊣ R.mapDerivedCategory) (b : G ⊣ S.mapDerivedCategory)
    (M : C) (N : D) (P : K)
    (f : F.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor D 0).obj N)
    (g : G.obj ((DerivedCategory.singleFunctor D 0).obj N) ⟶
      (DerivedCategory.singleFunctor K 0).obj P)
    (v : M ⟶ R.obj N) (w : N ⟶ S.obj P)
    (hf : a.homEquiv _ _ f = (DerivedCategory.singleFunctor C 0).map v ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N)
    (hg : b.homEquiv _ _ g = (DerivedCategory.singleFunctor D 0).map w ≫
      (S.mapDerivedCategorySingleFunctor 0).inv.app P) :
    ((a.comp b).ofNatIsoRight (Functor.mapDerivedCategoryCompIso S R)).homEquiv _ _
        (G.map f ≫ g) =
      (DerivedCategory.singleFunctor C 0).map (v ≫ R.map w) ≫
        ((S ⋙ R).mapDerivedCategorySingleFunctor 0).inv.app P := by
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change a.homEquiv _ _ (b.homEquiv _ _ (G.map f ≫ g)) ≫
    (Functor.mapDerivedCategoryCompIso S R).hom.app _ = _
  rw [Adjunction.homEquiv_naturality_left, hg,
    Adjunction.homEquiv_naturality_right, hf]
  rw [← cancel_mono (((S ⋙ R).mapDerivedCategorySingleFunctor 0).hom.app P)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor S R P]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [Category.comp_id, Category.comp_id]
  have hn := (R.mapDerivedCategorySingleFunctor 0).inv.naturality w
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app, Functor.map_comp]
  erw [Category.comp_id]

/-- Exact single comparisons commute with a scalar adjunction followed by an equivalence.
Source: coefficient changes (1). (blueprint: lem-diagonal-source-adjunction-transport).
Proof: transpose the finite-equivalence endpoint by the counit identity, then compose
the two adjunction transposes and use exact composition-single naturality. -/
theorem finite_homEquiv_single
    (R : D ⥤ C) [R.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {F : DerivedCategory C ⥤ DerivedCategory D}
    (a : F ⊣ R.mapDerivedCategory) (e : D ≌ K)
    [e.functor.Additive] [e.inverse.Additive]
    (M : C) (N : D) (P : K)
    (f : F.obj ((DerivedCategory.singleFunctor C 0).obj M) ⟶
      (DerivedCategory.singleFunctor D 0).obj N)
    (g : e.functor.obj N ⟶ P) (v : M ⟶ R.obj N)
    (hf : a.homEquiv _ _ f = (DerivedCategory.singleFunctor C 0).map v ≫
      (R.mapDerivedCategorySingleFunctor 0).inv.app N) :
    ((a.comp e.mapDerivedCategory.toAdjunction).ofNatIsoRight
        (Functor.mapDerivedCategoryCompIso e.inverse R)).homEquiv _ _
        (e.functor.mapDerivedCategory.map f ≫
          (e.functor.mapDerivedCategorySingleFunctor 0).hom.app N ≫
            (DerivedCategory.singleFunctor K 0).map g) =
      (DerivedCategory.singleFunctor C 0).map
          (v ≫ R.map (e.toAdjunction.homEquiv _ _ g)) ≫
        ((e.inverse ⋙ R).mapDerivedCategorySingleFunctor 0).inv.app P := by
  exact composite_homEquiv_single R e.inverse a e.mapDerivedCategory.toAdjunction
    M N P f _ v _ hf (equivalence_homEquiv_single e N P g)

private theorem right_comparison_single
    (R' : K ⥤ C) (H : K ⥤ D) (R : D ⥤ C)
    [R'.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (s : R' ≅ H ⋙ R) (P : K) :
    (R'.mapDerivedCategorySingleFunctor 0).inv.app P ≫
        (Functor.mapDerivedCategoryNatIso s).hom.app
          ((DerivedCategory.singleFunctor K 0).obj P) ≫
        (Functor.mapDerivedCategoryCompIso H R).inv.app
          ((DerivedCategory.singleFunctor K 0).obj P) ≫
        R.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app P) =
      (DerivedCategory.singleFunctor C 0).map (s.hom.app P) ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app (H.obj P) := by
  rw [← cancel_mono ((R.mapDerivedCategorySingleFunctor 0).hom.app (H.obj P))]
  rw [Category.assoc, Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem single_comparison_square
    (R' : K ⥤ C) (H : K ⥤ D) (R : D ⥤ C)
    [R'.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (s : R' ≅ H ⋙ R) (M : C) (N : D) (P : K)
    (v : M ⟶ R'.obj P) (w : M ⟶ R.obj N) (m : N ⟶ H.obj P)
    (h : v ≫ s.hom.app P = w ≫ R.map m) :
    ((DerivedCategory.singleFunctor C 0).map v ≫
      (R'.mapDerivedCategorySingleFunctor 0).inv.app P) ≫
        (Functor.mapDerivedCategoryNatIso s ≪≫
          (Functor.mapDerivedCategoryCompIso H R).symm).hom.app
            ((DerivedCategory.singleFunctor K 0).obj P) ≫
        R.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app P) =
      ((DerivedCategory.singleFunctor C 0).map w ≫
        (R.mapDerivedCategorySingleFunctor 0).inv.app N) ≫
          R.mapDerivedCategory.map ((DerivedCategory.singleFunctor D 0).map m) := by
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  simp only [Category.assoc, Iso.symm_hom]
  rw [right_comparison_single]
  have hn := (R.mapDerivedCategorySingleFunctor 0).inv.naturality m
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, h]

omit [Abelian C] [Abelian D] [Abelian K]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory K] in
private theorem mate_postcompose
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ K} {R' : K ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (H : K ⥤ D) (s : R' ≅ H ⋙ R)
    {M : C} {N : K} (f : L'.obj M ⟶ N) :
    a.homEquiv _ _ ((UniformizerSquareData.restrictionMate a b H s).app M ≫ H.map f) =
      b.homEquiv _ _ f ≫ s.hom.app N := by
  rw [Adjunction.homEquiv_naturality_right]
  unfold UniformizerSquareData.restrictionMate
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Equiv.apply_symm_apply]
  have hn := s.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn]
  simp only [← Category.assoc, Adjunction.homEquiv_unit]

end ExactTransport

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
  HasDerivedCategory.standard DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.ofIsGrothendieckAbelian

attribute [local semireducible] UniformizerSquareData.scalarAdjunction
  ScalarCompatibility.scalarAdjunction

section EndpointNormalization

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  {a : R ⟶ S} [IsMonHom a] {X : Scheme.{u}} {M : Modules R X} {N : Modules S X}
  {m : M.X ⟶ N.X} (e : Endpoint a M N m)

private theorem endpoint_scalar_normalization :
    (UniformizerSquareData.scalarAdjunction a X).homEquiv _ _ e.iso.hom =
      (DerivedCategory.singleFunctor _ 0).map e.semilinear.hom ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N := by
  exact e.normalization

private theorem endpoint_composite_scalar_normalization :
    (ScalarCompatibility.scalarAdjunction a X).homEquiv _ _ e.iso.hom =
      (DerivedCategory.singleFunctor _ 0).map e.semilinear.hom ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N := by
  exact e.normalization

end EndpointNormalization

section NamedFiniteSource

attribute [local instance] UniformizerSquareData.inverse_additive
  comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local semireducible] UniformizerSquareData.finiteAdjunction

private theorem realized_iso_transpose
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {X : Scheme.{u}}
    (H : Modules R X ⥤ C) [H.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    {L : DerivedCategory C ⥤ DerivedCategory (Modules R X)}
    (a : L ⊣ H.mapDerivedCategory) (M : C) (N : Modules R X)
    (d : L.obj ((DerivedCategory.singleFunctor C 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj N)
    (v : M ⟶ H.obj N)
    (hd : a.homEquiv _ _ d.hom = (DerivedCategory.singleFunctor C 0).map v ≫
      (H.mapDerivedCategorySingleFunctor 0).inv.app N)
    {A : Type (u + 1)} [CommRing A] (e : FiniteRealization R A X)
    (P : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (c : e.F.obj N ≅ P) :
    ((a.comp (UniformizerSquareData.finiteAdjunction e)).ofNatIsoRight
      (Functor.mapDerivedCategoryCompIso e.F.asEquivalence.inverse H)).homEquiv _ _
        (finiteSourceIso e d c).hom =
      (DerivedCategory.singleFunctor C 0).map
          (v ≫ H.map (e.F.asEquivalence.toAdjunction.homEquiv _ _ c.hom)) ≫
        ((e.F.asEquivalence.inverse ⋙ H).mapDerivedCategorySingleFunctor 0).inv.app P := by
  let : e.F.asEquivalence.functor.Additive := inferInstanceAs e.F.Additive
  exact finite_homEquiv_single H a e.F.asEquivalence M N P d.hom c.hom v hd

end NamedFiniteSource

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
