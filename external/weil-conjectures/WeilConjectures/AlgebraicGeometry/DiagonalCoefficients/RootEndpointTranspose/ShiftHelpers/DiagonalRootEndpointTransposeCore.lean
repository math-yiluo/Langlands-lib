/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.FiniteRealization.DiagonalRootRouteInsertions
import all WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor

/-! # Exact-single transposition and the scalar adjunction shift structures

Source: the exact functor single comparisons and adjunction triangle identities.
(blueprint: lem-diagonal-root-endpoint-transpose-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients.RootEndpointTranspose
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
attribute [local irreducible] Functor.mapDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors
  DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf

section ExactAdjunctions

variable {C D K : Type*} [Category C] [Category D] [Category K]
  [Abelian C] [Abelian D] [Abelian K]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory K]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open CategoryTheory.Functor
variable (C)
omit [HasDerivedCategory C] in
private lemma target_complexId_shift :
    NatTrans.CommShift (mapHomologicalComplexIdIso C (.up ℤ)).hom ℤ where
  shift_comm n := by
    ext K i
    dsimp [mapHomologicalComplexIdIso]
    simp only [Functor.commShiftIso_id_hom_app, HomologicalComplex.id_f]
    change (𝟙 (K.X (i + n)) ≫ 𝟙 _) = 𝟙 _ ≫ 𝟙 _
    rfl

omit [HasDerivedCategory C] in
private lemma target_homotopyId_shift :
    NatTrans.CommShift (mapHomotopyCategoryIdIso C (.up ℤ)).hom ℤ := by
  have := target_complexId_shift C
  have he : whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (mapHomotopyCategoryIdIso C (.up ℤ)).hom =
      ((𝟭 C).mapHomotopyCategoryFactors (.up ℤ)).hom ≫
        whiskerRight (mapHomologicalComplexIdIso C (.up ℤ)).hom
          (HomotopyCategory.quotient C (.up ℤ)) ≫
        (HomotopyCategory.quotient C (.up ℤ)).leftUnitor.hom ≫
        (HomotopyCategory.quotient C (.up ℤ)).rightUnitor.inv := by
    ext K
    simp only [comp_obj, id_obj, whiskerLeft_app, mapHomotopyCategoryIdIso_hom_app,
      NatTrans.comp_app, whiskerRight_app, leftUnitor_hom_app, rightUnitor_inv_app,
      Category.comp_id]
    exact (Category.id_comp _).symm
  have : NatTrans.CommShift (whiskerLeft (HomotopyCategory.quotient C (.up ℤ))
      (mapHomotopyCategoryIdIso C (.up ℤ)).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ (HomotopyCategory.quotient C (.up ℤ))
    (fun X ↦ by
      obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
      exact ⟨K, 𝟙 _, inferInstance⟩)

private lemma target_derivedId_shift :
    NatTrans.CommShift (mapDerivedCategoryIdIso C).hom ℤ := by
  have := target_homotopyId_shift C
  have he : whiskerLeft DerivedCategory.Qh (mapDerivedCategoryIdIso C).hom =
      (𝟭 C).mapDerivedCategoryFactorsh.hom ≫
        whiskerRight (mapHomotopyCategoryIdIso C (.up ℤ)).hom DerivedCategory.Qh ≫
        DerivedCategory.Qh.leftUnitor.hom ≫ DerivedCategory.Qh.rightUnitor.inv := by
    have h := congr_arg Iso.hom (mapDerivedCategoryIdIso_factorsh C)
    rw [← cancel_mono DerivedCategory.Qh.rightUnitor.hom]
    simpa only [Iso.trans_hom, isoWhiskerLeft_hom, isoWhiskerRight_hom, Category.assoc,
      Iso.inv_hom_id, Category.comp_id] using h
  have : NatTrans.CommShift (whiskerLeft DerivedCategory.Qh
      (mapDerivedCategoryIdIso C).hom) ℤ := by
    rw [he]
    infer_instance
  exact NatTrans.CommShift.of_whiskerLeft _ DerivedCategory.Qh
    (fun X ↦ ⟨_, (DerivedCategory.Qh.objObjPreimageIso X).inv, inferInstance⟩)

variable {C}

/-- The exact derived equivalence transpose on single objects is the ordinary transpose.
Source: coefficient changes (1), finite realization
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: compute the derived counit on a single object by the composition, identity and
natural-isomorphism comparisons; inverse transposition then uses the ordinary triangle. -/
theorem equivalence_single_transpose (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive]
    {M : C} {N : D} (i : e.functor.obj M ⟶ N) :
    e.mapDerivedCategory.toAdjunction.homEquiv _ _
        ((e.functor.mapDerivedCategorySingleFunctor 0).hom.app M ≫
          (DerivedCategory.singleFunctor D 0).map i) =
      (DerivedCategory.singleFunctor C 0).map
        (e.unitIso.hom.app M ≫ e.inverse.map i) ≫
          (e.inverse.mapDerivedCategorySingleFunctor 0).inv.app N := by
  have hc : e.mapDerivedCategory.toAdjunction.counit.app
      ((DerivedCategory.singleFunctor D 0).obj N) =
        e.functor.mapDerivedCategory.map
          ((e.inverse.mapDerivedCategorySingleFunctor 0).hom.app N) ≫
        (e.functor.mapDerivedCategorySingleFunctor 0).hom.app (e.inverse.obj N) ≫
          (DerivedCategory.singleFunctor D 0).map (e.counitIso.hom.app N) := by
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso e.inverse e.functor).inv.app
      ((DerivedCategory.singleFunctor D 0).obj N))).mp
    change _ ≫ ((Functor.mapDerivedCategoryCompIso e.inverse e.functor).hom.app _ ≫
      (Functor.mapDerivedCategoryNatIso e.counitIso).hom.app _ ≫
        (Functor.mapDerivedCategoryIdIso D).hom.app _) = _
    rw [Iso.inv_hom_id_app_assoc, SheafExactDegreeZero.derived_id_single,
      Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor]
    rw [reassoc_of% Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor]
  apply (e.mapDerivedCategory.toAdjunction.homEquiv _ _).symm.injective
  simp only [Equiv.symm_apply_apply]
  erw [Adjunction.homEquiv_counit, hc]
  change _ = e.functor.mapDerivedCategory.map
    ((DerivedCategory.singleFunctor C 0).map
      (e.unitIso.hom.app M ≫ e.inverse.map i) ≫
        (e.inverse.mapDerivedCategorySingleFunctor 0).inv.app N) ≫ _
  simp only [Functor.map_comp, Category.assoc]
  rw [← e.functor.mapDerivedCategory.map_comp_assoc
    ((e.inverse.mapDerivedCategorySingleFunctor 0).inv.app N)]
  rw [Iso.inv_hom_id_app, e.functor.mapDerivedCategory.map_id, Category.id_comp]
  erw [(e.functor.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc]
  erw [(e.functor.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  have hi : e.functor.map (e.unitIso.hom.app M) ≫
      e.functor.map (e.inverse.map i) ≫ e.counitIso.hom.app N = i := by
    have hn := e.counitIso.hom.naturality i
    change e.functor.map (e.inverse.map i) ≫ e.counitIso.hom.app N =
      e.counitIso.hom.app (e.functor.obj M) ≫ i at hn
    rw [hn, ← Category.assoc]
    exact (congrArg (fun f ↦ f ≫ i) (e.functor_unitIso_comp M)).trans (Category.id_comp i)
  rw [hi]
  rfl

/-- Degree-zero endpoint normalization composes along the actual scalar adjunctions.
Source: coefficient changes (1), successive coefficient extension
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: expand composite transposition, use each normalization and exact-single
naturality, and cancel the collected-right composition comparison. -/
theorem composite_single_transpose
    (R : D ⥤ C) (S : K ⥤ D)
    [R.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    {F : DerivedCategory C ⥤ DerivedCategory D}
    {G : DerivedCategory D ⥤ DerivedCategory K}
    (a : F ⊣ R.mapDerivedCategory) (b : G ⊣ S.mapDerivedCategory)
    {M : C} {N : D} {P : K}
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
  change a.homEquiv _ _ (b.homEquiv _ _ (G.map f ≫ g)) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, hg,
    Adjunction.homEquiv_naturality_right, hf]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (R.mapDerivedCategorySingleFunctor 0).inv.naturality w
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← reassoc_of% hn]
  simp only [← Functor.map_comp_assoc]
  congr 1
  apply (cancel_mono (((S ⋙ R).mapDerivedCategorySingleFunctor 0).hom.app P)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  change _ ≫ _ ≫ (Functor.mapDerivedCategoryCompIso S R).hom.app _ ≫ _ = _
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor S R P]
  simp only [Iso.hom_inv_id_app_assoc]
  rw [← R.mapDerivedCategory.map_comp_assoc]
  simp only [Iso.inv_hom_id_app]
  erw [R.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app]
  rfl

/-- Transport along a shift-compatible right isomorphism preserves adjunction shifts.
Source: coefficient changes (1), collected exact restrictions
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: the new unit is the original unit followed by the whiskered isomorphism;
both factors commute with shifts, and unit compatibility implies counit compatibility. -/
theorem rightIso_commShift
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F : C ⥤ D} {R S : D ⥤ C}
    [F.CommShift ℤ] [R.CommShift ℤ] [S.CommShift ℤ]
    (a : F ⊣ R) (e : R ≅ S) [NatTrans.CommShift e.hom ℤ]
    (ha : a.CommShift ℤ) :
    (a.ofNatIsoRight e).CommShift ℤ := by
  let := ha
  apply Adjunction.CommShift.mk'
  change NatTrans.CommShift (a.unit ≫ Functor.whiskerLeft F e.hom) ℤ
  infer_instance

/-- The actual derived equivalence adjunction respects the exact shift structures.
Source: coefficient changes (1), finite realization
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: descend shift compatibility of the identity comparison from complexes through
homotopy and derived localization. The derived equivalence counit is a composite of
this comparison with the shift-compatible composition and counit comparisons. -/
theorem equivalence_commShift (e : C ≌ D)
    [e.functor.Additive] [e.inverse.Additive] :
    @Adjunction.CommShift (DerivedCategory C) (DerivedCategory D)
      _ _ e.functor.mapDerivedCategory e.inverse.mapDerivedCategory
      e.mapDerivedCategory.toAdjunction ℤ _ _ _
      (Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt e.functor)
      (Functor.instCommShiftDerivedCategoryMapDerivedCategoryInt e.inverse) := by
  let csF : e.mapDerivedCategory.functor.CommShift ℤ :=
    (inferInstance : e.functor.mapDerivedCategory.CommShift ℤ)
  let csG : e.mapDerivedCategory.inverse.CommShift ℤ :=
    (inferInstance : e.inverse.mapDerivedCategory.CommShift ℤ)
  have := target_derivedId_shift D
  apply Equivalence.CommShift.mk'' e.mapDerivedCategory ℤ
  change NatTrans.CommShift
    ((Functor.mapDerivedCategoryCompIso e.inverse e.functor).hom ≫
      (Functor.mapDerivedCategoryNatIso e.counitIso).hom ≫
        (Functor.mapDerivedCategoryIdIso D).hom) ℤ
  infer_instance

end ExactAdjunctions

open UniformizerSquareData
namespace ShiftHelpers

attribute [local semireducible] scalarAdjunction ScalarCompatibility.scalarAdjunction
  finiteAdjunction cyclicAdjunction quotientAdjunction

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits inverse_additive
attribute [local instance 100001]
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] derivedScalars quotientLine quotientLineMap cyclicLine cyclicLineMap
  Functor.leftDerivedFunctor Mod.derivedExtendMapDerivedCategoryAdjunction
attribute [local semireducible] UniformizerSquareData.cyclicEndpoints
  UniformizerSquareData.quotientEndpoints

/-- The named scalar adjunction has exactly the supplied endpoint normalization.
Source: coefficient changes (1), scalar units
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: unfold the named adjunction and its left functor and use the endpoint field. -/
theorem scalarEndpoint_transpose
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X : Scheme.{u}}
    {M : Modules R X} {N : Modules S X} {m : M.X ⟶ N.X}
    (e : Endpoint a M N m) :
    (scalarAdjunction a X).homEquiv _ _ e.iso.hom =
      (DerivedCategory.singleFunctor _ 0).map e.semilinear.hom ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N := by
  unfold scalarAdjunction derivedScalars
  exact e.normalization

/-- The scalar compatibility adjunction has exactly the supplied endpoint normalization.
Source: coefficient changes (1), scalar units
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: unfold the named adjunction and its left functor and use the endpoint field. -/
theorem compatibilityEndpoint_transpose
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] {X : Scheme.{u}}
    {M : Modules R X} {N : Modules S X} {m : M.X ⟶ N.X}
    (e : Endpoint a M N m) :
    (ScalarCompatibility.scalarAdjunction a X).homEquiv _ _ e.iso.hom =
      (DerivedCategory.singleFunctor _ 0).map e.semilinear.hom ≫
        ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N := by
  unfold ScalarCompatibility.scalarAdjunction derivedScalars
  exact e.normalization

/-- The finite adjunction transposes a realized line to its ordinary root insertion.
Source: coefficient changes (1), finite realization
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: use the derived equivalence transpose and unfold the ordinary root insertion. -/
theorem finiteEndpoint_transpose
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) (M : Modules R X)
    {N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B)} (i : e.F.obj M ≅ N) :
    (finiteAdjunction e).homEquiv _ _
      ((e.F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
        (DerivedCategory.singleFunctor _ 0).map i.hom) =
      (DerivedCategory.singleFunctor _ 0).map (e.rootInsertion M i) ≫
        (e.F.asEquivalence.inverse.mapDerivedCategorySingleFunctor 0).inv.app N := by
  let : e.F.asEquivalence.functor.Additive := inferInstanceAs e.F.Additive
  unfold finiteAdjunction FiniteRealization.rootInsertion
  exact equivalence_single_transpose e.F.asEquivalence i.hom

/-- Scalar extension has the shift structure induced by its actual adjunction.
Source: coefficient changes (1), derived scalar extension
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: unfold the named scalar adjunction and its left shift structure, then apply
the compatibility theorem for the shift induced by an adjunction. -/
theorem scalarAdjunction_commShift
    {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (a : R ⟶ S) [IsMonHom a] (X : Scheme.{u}) :
    (scalarAdjunction a X).CommShift ℤ := by
  unfold scalarAdjunction scalarCommShift derivedScalars
  exact (@Mod.derivedExtendMapDerivedCategoryAdjunction
    (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) _ _ _ _ _ _ _ _
    (condensedRingObj R X) (condensedRingObj S X) _ _
    (isCommMonObj_condensedRingObj R X) (isCommMonObj_condensedRingObj S X)
    (coefficientMap a X) _).commShift_of_rightAdjoint ℤ

/-- The finite realization adjunction respects the exact derived shifts.
Source: coefficient changes (1), finite realization
(blueprint: lem-diagonal-root-endpoint-transpose-core).
Proof: apply compatibility of the actual derived equivalence adjunction to the
finite realization equivalence. -/
theorem finiteAdjunction_commShift
    {R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj R] [IsCommMonObj R] {B : Type (u + 1)} [CommRing B]
    {X : Scheme.{u}} (e : FiniteRealization R B X) :
    (finiteAdjunction e).CommShift ℤ := by
  let : e.F.asEquivalence.functor.Additive := inferInstanceAs e.F.Additive
  unfold finiteAdjunction
  exact equivalence_commShift e.F.asEquivalence

end ShiftHelpers

end AlgebraicGeometry.ProEtale.DiagonalCoefficients.RootEndpointTranspose
