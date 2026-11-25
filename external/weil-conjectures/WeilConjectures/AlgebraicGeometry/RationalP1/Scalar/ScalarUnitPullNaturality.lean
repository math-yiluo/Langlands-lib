/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.RationalP1.FlatCoefficientExchange
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
import all Mathlib.Logic.Small.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarUnitCoherence
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryCounit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarUnitPush
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceSingleNormalization
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Finite.DiagonalFiniteScalarSquares

/-! # Scalar compatibility of coefficient units under pullback -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances
namespace AlgebraicGeometry.ProEtale.RationalP1

local instance instEssentiallySmallProfinite_scalarUnitPullNaturality
    : EssentiallySmall.{u + 1} Profinite.{u} := essentiallySmallSelf.{0} _
open DiagonalCoefficients CondensedRing
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory derivedPullIso derivedComapLowerStarIso
  CondensedRing.derivedUpperStarLowerStarAdjunction
  Mod.derivedExtendMapDerivedCategoryAdjunction

set_option allowUnsafeReducibility true in
attribute [local reducible] derivedScalars moduleObjectDerivedPullback
  moduleObjectDerivedPushforward

-- The proof helpers below use their own instance context; the public statements are
-- elaborated after this section, in the context of the module.
section ProofHelpers
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
attribute [local implicit_reducible] ProEtale.sheafMonoidalCategory
  ProEtale.sheafBraidedCategory ProEtale.sheafSymmetricCategory
  GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  Sheaf.symmetricCategory Sheaf.braidedCategory
  Localization.Monoidal.instSymmetricCategoryLocalizedMonoidal
  CategoryTheory.Monoidal.functorCategorySymmetric
attribute [-instance] isCommMonObj_condensedRingObj

section MateCalculus
universe a₁ a₂ a₃ a₄ v₁ v₂ v₃ v₄
variable {A : Type a₁} {B : Type a₂} {A' : Type a₃} {B' : Type a₄}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} A'] [Category.{v₄} B']
  {E₁ : A ⥤ B} {Res₁ : B ⥤ A} (adj₁ : E₁ ⊣ Res₁)
  {E₂ : A' ⥤ B'} {Res₂ : B' ⥤ A'} (adj₂ : E₂ ⊣ Res₂)
  {U₁ : A' ⥤ A} {L₁ : A ⥤ A'} (adjR : U₁ ⊣ L₁)
  {U₂ : B' ⥤ B} {L₂ : B ⥤ B'} (adjS : U₂ ⊣ L₂)
  (e : L₂ ⋙ Res₂ ≅ Res₁ ⋙ L₁)

private theorem scalar_push_pull_counit (K : A) :
    U₂.map ((Adjunction.pushHomOfComapIso adj₁ adj₂ e).app K) ≫
        adjS.counit.app (E₁.obj K) =
      (Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e).inv.app (L₁.obj K) ≫
        E₁.map (adjR.counit.app K) := by
  have h := iterated_mateEquiv_conjugateEquiv_symm adjR adjS adj₂ adj₁
    (TwoSquare.mk Res₁ L₂ L₁ Res₂ e.inv)
  have hh := mateEquiv_counit_symm adjR adjS
    (TwoSquare.mk L₁ E₁ E₂ L₂ (Adjunction.pushHomOfComapIso adj₁ adj₂ e)) K
  change U₂.map ((Adjunction.pushHomOfComapIso adj₁ adj₂ e).app K) ≫
      adjS.counit.app (E₁.obj K) =
    ((mateEquiv adjR adjS).symm
      ((mateEquiv adj₁ adj₂).symm (TwoSquare.mk Res₁ L₂ L₁ Res₂ e.inv))).app
        (L₁.obj K) ≫ E₁.map (adjR.counit.app K) at hh
  rw [h] at hh
  exact hh

private theorem pull_endpoint_of_push
    {M : A'} {M' : B'} {N : A} {N' : B}
    (m : E₂.obj M ⟶ M') (b : U₁.obj M ⟶ N) (b' : U₂.obj M' ⟶ N')
    (n : E₁.obj N ⟶ N')
    (hp : E₂.map (adjR.homEquiv _ _ b) ≫
        (Adjunction.pushHomOfComapIso adj₁ adj₂ e).app N ≫ L₂.map n =
      m ≫ adjS.homEquiv _ _ b') :
    (Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e).hom.app M ≫
        U₂.map m ≫ b' = E₁.map b ≫ n := by
  let α := Adjunction.pullIsoOfComapIso adj₁ adj₂ adjR adjS e
  have hl : (adjS.homEquiv _ _).symm
      (E₂.map (adjR.homEquiv _ _ b) ≫
        (Adjunction.pushHomOfComapIso adj₁ adj₂ e).app N ≫ L₂.map n) =
      α.inv.app M ≫ E₁.map b ≫ n := by
    rw [Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_naturality_right_symm, Adjunction.homEquiv_counit,
      scalar_push_pull_counit adj₁ adj₂ adjR adjS e]
    simp only [← Category.assoc]
    rw [show U₂.map (E₂.map (adjR.homEquiv _ _ b)) ≫ α.inv.app (L₁.obj N) =
        α.inv.app M ≫ E₁.map (U₁.map (adjR.homEquiv _ _ b)) from
      α.inv.naturality (adjR.homEquiv _ _ b)]
    have hb := (adjR.homEquiv M N).symm_apply_apply b
    change U₁.map ((adjR.homEquiv M N) b) ≫ adjR.counit.app N = b at hb
    simp only [Category.assoc, ← CategoryTheory.Functor.map_comp, hb]
  have ht := congrArg (adjS.homEquiv (E₂.obj M) N').symm hp
  rw [hl, Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply] at ht
  change α.hom.app M ≫ U₂.map m ≫ b' = E₁.map b ≫ n
  apply (cancel_epi (α.inv.app M)).1
  simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using ht.symm

private theorem exact_single_map
    {C D : Type a₁} [Category.{v₁} C] [Category.{v₁} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{v₂} C] [HasDerivedCategory.{v₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {M : C} {N : D} (f : F.obj M ⟶ N) :
    F.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj
          ((HomologicalComplex.single C (.up ℤ) 0).obj M)) ≫
      DerivedCategory.Qh.map (F.mapHomotopyCategorySingleHom f) =
    (F.mapDerivedCategorySingleFunctor 0).hom.app M ≫
      (DerivedCategory.singleFunctor D 0).map f := by
  rw [Functor.mapHomotopyCategorySingleHom, Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc DerivedCategory.Qh
      ((F.mapHomotopyCategoryFactors _).inv.app _),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hq {P Q : CochainComplex D ℤ} (g : P ⟶ Q) :
      DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map g) =
        DerivedCategory.Q.map g := by
    have h := DerivedCategory.quotientCompQhIso_hom_naturality g
    have hi : ∀ K : CochainComplex D ℤ,
        (DerivedCategory.quotientCompQhIso D).hom.app K = 𝟙 _ := fun _ ↦ rfl
    erw [hi, hi, Category.comp_id, Category.id_comp] at h
    exact h
  have hC : ∀ P : CochainComplex C ℤ,
      (DerivedCategory.quotientCompQhIso C).hom.app P = 𝟙 _ := fun _ ↦ rfl
  have hDi : ∀ P : CochainComplex D ℤ,
      (DerivedCategory.quotientCompQhIso D).inv.app P = 𝟙 _ := fun _ ↦ rfl
  erw [hC, hDi, F.mapDerivedCategory.map_id, Category.id_comp, Category.id_comp]
  simp only [hq]
  erw [Functor.mapDerivedCategorySingleFunctor_hom_app_eq, Category.assoc]
  rfl

end MateCalculus

@[instance_reducible]
private def scalar_unit_sheaf_symmetric (Z : Scheme.{u}) :
    SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
  { sheafSymmetricCategory Z with toBraidedCategory := sheafBraidedCategory Ab Z }

private local instance (priority := 40000) scalar_unit_comm_braided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _ _
      (sheafBraidedCategory Ab Z)
      (condensedRingObj Λ Z) (Functor.monObjObj Λ) := by
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    scalar_unit_sheaf_symmetric Z
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint Z)

private local instance (priority := 40000) scalar_unit_comm_sym
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    @IsCommMonObj (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) _ _
      (scalar_unit_sheaf_symmetric Z).toBraidedCategory
      (condensedRingObj Λ Z) (Functor.monObjObj Λ) := by
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    scalar_unit_sheaf_symmetric Z
  exact Functor.isCommMonObj_obj (F := upperStarFromPoint Z)

private local instance (priority := 40000) scalar_module_braided
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    BraidedCategory (Modules Λ Z) := by
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    scalar_unit_sheaf_symmetric Z
  let : IsCommMonObj (condensedRingObj Λ Z) := scalar_unit_comm_sym Λ Z
  exact Mod.braidedCategory

private local instance (priority := 40000) scalar_module_closed
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Z : Scheme.{u}) :
    MonoidalClosed (Modules Λ Z) := by
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology Z) Ab.{u + 1}) :=
    scalar_unit_sheaf_symmetric Z
  let : IsCommMonObj (condensedRingObj Λ Z) := scalar_unit_comm_sym Λ Z
  exact Mod.monoidalClosed

section UnitComparison
attribute [-instance] scalar_unit_comm_sym
attribute [local instance 20001] ProEtale.sheafSymmetricCategory

-- Compare the two native unit structures with their dependent tensor instances.
attribute [-instance] internalMonoidal internalTensorCommShift in
private theorem native_unit_comparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    HEq (secondTraceUnitIso Λ Y)
      (CondensedRing.leftDerivedUpperStarUnitIso Λ (ProjectiveLine Y ↘ Y)) := by
  unfold secondTraceUnitIso secondTracePullMonoidal internalMonoidal
    internalTensorBundle nativeTensorBundle moduleObjectDerivedPullback
  rfl

attribute [local instance 50000] scalar_unit_comm_braided

-- Normalize the native module-object tensor instances and derived-functor comparisons.
private theorem native_single_unit_inv
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (DerivedCategory.singleFunctorObjUnitIso (Modules Λ X)).inv = 𝟙 _ := by
  let : BraidedCategory (Modules Λ X) := scalar_module_braided Λ X
  let : MonoidalClosed (Modules Λ X) := scalar_module_closed Λ X
  change ((𝟙 _ ≫ (DerivedCategory.Qh (C := Modules Λ X)).map (𝟙 _)) ≫ 𝟙 _) ≫ 𝟙 _ = 𝟙 _
  simp

-- Normalize the native module-object tensor instances and derived-functor comparisons.
private theorem native_single_unit_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (X : Scheme.{u}) :
    (DerivedCategory.singleFunctorObjUnitIso (Modules Λ X)).hom = 𝟙 _ := by
  let : BraidedCategory (Modules Λ X) := scalar_module_braided Λ X
  let : MonoidalClosed (Modules Λ X) := scalar_module_closed Λ X
  have h := (DerivedCategory.singleFunctorObjUnitIso (Modules Λ X)).inv_hom_id
  erw [native_single_unit_inv, Category.id_comp] at h
  exact h

private theorem scalar_unit_pull_formula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (scalarUnitPullIso Λ Y).hom =
      (moduleObjectDerivedPullback Λ (ProjectiveLine Y ↘ Y)).map (singleUnitIso Λ Y).hom ≫
        (secondTraceUnitIso Λ Y).hom ≫
        (singleUnitIso Λ (ProjectiveLine Y)).symm.hom := by
  unfold scalarUnitPullIso
  rfl

-- Normalize the unit comparison before applying the derived adjunction.
attribute [-instance] internalMonoidal internalTensorCommShift in
private theorem scalar_unit_pull_native_hom
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    HEq (scalarUnitPullIso Λ Y).hom
      (CondensedRing.leftDerivedUpperStarUnitIso Λ (ProjectiveLine Y ↘ Y)).hom := by
  generalize hU : secondTraceUnitIso Λ Y = U
  have hu_global := native_unit_comparison Λ Y
  rw [hU] at hu_global
  let : BraidedCategory (Modules Λ Y) := scalar_module_braided Λ Y
  let : BraidedCategory (Modules Λ (ProjectiveLine Y)) :=
    scalar_module_braided Λ (ProjectiveLine Y)
  let : MonoidalClosed (Modules Λ Y) := scalar_module_closed Λ Y
  let : MonoidalClosed (Modules Λ (ProjectiveLine Y)) :=
    scalar_module_closed Λ (ProjectiveLine Y)
  rw [scalar_unit_pull_formula]
  have hY := (singleUnit_existsUnique Λ Y).exists.choose_spec
  have hP := (singleUnit_existsUnique Λ (ProjectiveLine Y)).exists.choose_spec
  unfold singleUnitIso internalMonoidal internalTensorBundle nativeTensorBundle at hY hP ⊢
  erw [eq_of_heq hY, eq_of_heq hP]
  simp only [Iso.symm_hom]
  erw [native_single_unit_hom, native_single_unit_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  unfold internalMonoidal internalTensorBundle nativeTensorBundle
    moduleObjectDerivedPullback at U hu_global
  have hu' : U = CondensedRing.leftDerivedUpperStarUnitIso Λ (ProjectiveLine Y ↘ Y) :=
    eq_of_heq hu_global
  erw [hU, hu']
  exact HEq.rfl

-- Normalize the native module-object tensor instances and derived-functor comparisons.
attribute [-instance] internalMonoidal internalTensorCommShift in
private theorem scalar_unit_pull_adjunct
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (Y : Scheme.{u}) :
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)).homEquiv
        _ _ (scalarUnitPullIso Λ Y).hom =
      coefficientUnitPush Λ Y
        (canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ (ProjectiveLine Y ↘ Y))) := by
  let : BraidedCategory (Modules Λ Y) := scalar_module_braided Λ Y
  let : BraidedCategory (Modules Λ (ProjectiveLine Y)) :=
    scalar_module_braided Λ (ProjectiveLine Y)
  let : MonoidalClosed (Modules Λ Y) := scalar_module_closed Λ Y
  let : MonoidalClosed (Modules Λ (ProjectiveLine Y)) :=
    scalar_module_closed Λ (ProjectiveLine Y)
  erw [eq_of_heq (scalar_unit_pull_native_hom Λ Y)]
  let ad := CondensedRing.derivedUpperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y)
  let ad' := (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (CondensedRing.upperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y))).ofNatIsoLeft
          (Functor.leftDerivedFunctorIsoMapDerivedCategory
            (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y))).symm
  have ha : ad = ad' := by
    dsimp [ad, ad']
    unfold CondensedRing.derivedUpperStarLowerStarAdjunction
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y)).leftDerivedFunctorIsoMapDerivedCategory
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
        (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y))).symm
  change ad.homEquiv _ _ _ = _
  erw [ha, Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp only [Iso.symm_hom]
  erw [CondensedRing.leftDerivedUpperStarUnitIso_hom_eq,
    ← Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_app_Qh]
  erw [Category.assoc, Iso.inv_hom_id_app_assoc]
  have h := DiagonalTrace.adjunct_single
    (CondensedRing.upperStarLowerStarAdjunction Λ (ProjectiveLine Y ↘ Y))
    (Mod.regular (condensedRingObj Λ Y))
    (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
    (Functor.Monoidal.εIso (CondensedRing.upperStar Λ (ProjectiveLine Y ↘ Y))).inv
  rw [DiagonalTrace.rightSingle_eq] at h
  erw [exact_single_map]
  unfold coefficientUnitPush coefficientOrdinaryUnit singlePushComparison
  coefficient_finish h

end UnitComparison

-- The four module-object categories carry large dependent instance arguments.
private theorem scalar_unit_pull_naturality_aux
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    (Y : Scheme.{u})
    (cY : Endpoint a (Mod.regular (condensedRingObj Λ Y))
      (Mod.regular (condensedRingObj Λ' Y)) (coefficientMap a Y))
    (cP : Endpoint a (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y))) :
    PullEndpointSquare (derivedPullIso a (ProjectiveLine Y ↘ Y)).hom
      cY.iso.hom (scalarUnitPullIso Λ Y).hom (scalarUnitPullIso Λ' Y).hom cP.iso.hom := by
  -- Reuse the normalized direct-image square and transpose it through the
  -- geometric adjunctions using the canonical scalar mate comparison.
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) :=
    scalar_unit_sheaf_symmetric Y
  let : SymmetricCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine Y)) Ab.{u + 1}) :=
    scalar_unit_sheaf_symmetric (ProjectiveLine Y)
  let : IsCommMonObj (condensedRingObj Λ Y) := scalar_unit_comm_sym Λ Y
  let : IsCommMonObj (condensedRingObj Λ (ProjectiveLine Y)) :=
    scalar_unit_comm_sym Λ (ProjectiveLine Y)
  let : IsCommMonObj (condensedRingObj Λ' Y) := scalar_unit_comm_sym Λ' Y
  let : IsCommMonObj (condensedRingObj Λ' (ProjectiveLine Y)) :=
    scalar_unit_comm_sym Λ' (ProjectiveLine Y)
  let q := ProjectiveLine Y ↘ Y
  let R := canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ q)
  let R' := canonicalDiagonalRightDerived (CondensedRing.lowerStar Λ' q)
  let s : RestrictionSquare a q R R' :=
    { iso := derivedComapLowerStarIso a q
      normalization := by
        intro P
        have h := canonicalSquare_normalization
          (CondensedRing.lowerStar Λ' q) (CondensedRing.lowerStar Λ q)
          (Mod.comap (coefficientMap a (ProjectiveLine Y)))
          (Mod.comap (coefficientMap a Y)) (comapLowerStarIso a q) P
        unfold derivedComapLowerStarIso
        coefficient_finish h }
  have hp := scalar_unit_push a Y R R' s cY cP
  rw [← scalar_unit_pull_adjunct Λ Y, ← scalar_unit_pull_adjunct Λ' Y] at hp
  have h := pull_endpoint_of_push
    (Mod.derivedExtendMapDerivedCategoryAdjunction
      (coefficientMap a (ProjectiveLine Y)))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a Y))
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ q)
    (CondensedRing.derivedUpperStarLowerStarAdjunction Λ' q)
    (derivedComapLowerStarIso a q)
    cY.iso.hom (scalarUnitPullIso Λ Y).hom (scalarUnitPullIso Λ' Y).hom cP.iso.hom
    (by coefficient_finish hp)
  unfold PullEndpointSquare
  unfold derivedPullIso
  coefficient_finish h

end ProofHelpers

/-- The scalar/pullback comparison respects the normalized coefficient-unit endpoints.
This equation has no direct image, exchange map, Tate line, or Chern adjunct. -/
theorem scalar_unit_pull_naturality
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    (Y : Scheme.{u})
    (cY : Endpoint a (Mod.regular (condensedRingObj Λ Y))
      (Mod.regular (condensedRingObj Λ' Y)) (coefficientMap a Y))
    (cP : Endpoint a (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y))) :
    PullEndpointSquare (derivedPullIso a (ProjectiveLine Y ↘ Y)).hom
      cY.iso.hom (scalarUnitPullIso Λ Y).hom (scalarUnitPullIso Λ' Y).hom cP.iso.hom :=
  scalar_unit_pull_naturality_aux a Y cY cP

/-- The unit square in native functor notation. -/
theorem scalar_unit_pull_naturality_explicit
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a]
    [∀ S : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a S))]
    (Y : Scheme.{u})
    (cY : Endpoint a (Mod.regular (condensedRingObj Λ Y))
      (Mod.regular (condensedRingObj Λ' Y)) (coefficientMap a Y))
    (cP : Endpoint a (Mod.regular (condensedRingObj Λ (ProjectiveLine Y)))
      (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))
      (coefficientMap a (ProjectiveLine Y))) :
    (derivedPullIso a (ProjectiveLine Y ↘ Y)).hom.app (unit Λ Y) ≫
        (moduleObjectDerivedPullback Λ' (ProjectiveLine Y ↘ Y)).map cY.iso.hom ≫
          (scalarUnitPullIso Λ' Y).hom =
      (derivedScalars a (ProjectiveLine Y)).map (scalarUnitPullIso Λ Y).hom ≫ cP.iso.hom := by
  have h := scalar_unit_pull_naturality a Y cY cP
  unfold PullEndpointSquare at h
  coefficient_finish h

end AlgebraicGeometry.ProEtale.RationalP1
