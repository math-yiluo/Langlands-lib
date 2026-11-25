/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportCoefficientChange
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonFiniteLevel
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
import WeilConjectures.AlgebraicGeometry.Etale.Proper.EtaleProperCoefficientTensorUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Ordinary-etale coefficient comparison for compact support

Source: Stacks Project, Tags 0GL5, 0GL6 and 07A6
(blueprint: lemma-sp-reduction--1).
These are universal tensor presentations on the ordinary-etale site. The existing
pro-etale presentations and their normalized comparisons are imported unchanged.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Etale

/-- The inverse mate of the canonical restriction/inverse-image identification on
sheaves. Source: Stacks Tags 03S2 and 0GL6
(blueprint: lemma-sp-reduction--1). -/
def coefficientRestrictionOpenMap
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    Sheaf.restrictScalars X.smallEtaleTopology φ ⋙
        openImmersionLowerShriek (ModuleCat.{u + 1} A) j ⟶
      openImmersionLowerShriek (ModuleCat.{u + 1} B) j ⋙
        Sheaf.restrictScalars Z.smallEtaleTopology φ :=
  (mateEquiv (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)).symm
      (asIso (upperStarRestrictScalars φ j)).inv

/-- The open coefficient mate is invertible. Source: Stacks Tags 03S2 and 0GL6
(blueprint: lemma-sp-reduction--1).
Proof: on the open both composites are the same module with restricted scalars;
off the open both are zero. The identity comparison has inverse the same identity.
Its transpose is the restriction/inverse-image identification, since both transposes
are the open unit. Thus it is the displayed mate, not an arbitrary isomorphism. -/
theorem coefficientRestrictionOpenMap_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    IsIso (coefficientRestrictionOpenMap φ j) := by
  have hopen (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      IsIso ((j)^*[ModuleCat.{u + 1} A].map
        ((coefficientRestrictionOpenMap φ j).app F)) := by
    have h := unit_mateEquiv_symm
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) j)
      (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) j)
      (asIso (upperStarRestrictScalars φ j)).inv F
    change _ = _ ≫ (j)^*[ModuleCat.{u + 1} A].map
      ((coefficientRestrictionOpenMap φ j).app F) at h
    dsimp only [Functor.id_obj] at h
    have hi : IsIso ((openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) j).unit.app
          ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F) ≫
        (j)^*[ModuleCat.{u + 1} A].map
          ((coefficientRestrictionOpenMap φ j).app F)) := by
      rw [← h]
      infer_instance
    exact (isIso_comp_left_iff _ _).mp hi
  have happ (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      IsIso ((coefficientRestrictionOpenMap φ j).app F) := by
    refine Scheme.isIso_of_isIso_sheafFiber_map _ fun x ↦ ?_
    let t := Z.algClosurePoint x
    by_cases ht : t.base (IsLocalRing.closedPoint _) ∈ Set.range j.base
    · have h := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map
        (ModuleCat.{u + 1} A) j _ (hopen F)
        (IsOpenImmersion.lift j t (Scheme.range_base_subset_of_closedPoint_mem t ht))
      rw [IsOpenImmersion.lift_fac] at h
      exact h
    · have hd : Disjoint (Set.range j.base) (Set.range t.base) := by
        rw [Set.disjoint_right]
        rintro _ ⟨p, rfl⟩
        simpa only [Subsingleton.elim p (IsLocalRing.closedPoint _)] using ht
      have h₁ := isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
        (ModuleCat.{u + 1} A) j t hd
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj F)
      have h₂ := ((Sheaf.restrictScalars _ φ).map_isZero
        (isZero_upperStar_openImmersionLowerShriek_of_disjoint_range
          (ModuleCat.{u + 1} B) j t hd F)).of_iso
        ((asIso (upperStarRestrictScalars φ t)).app
          ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).obj F))
      have hi : IsIso ((t)^*[ModuleCat.{u + 1} A].map
          ((coefficientRestrictionOpenMap φ j).app F)) :=
        ⟨⟨h₂.to_ _, h₁.eq_of_src _ _, h₂.eq_of_src _ _⟩⟩
      have h := isIso_uliftSheafFiber_comp_map_of_isIso_upperStar_map
        (ModuleCat.{u + 1} A) t _ hi (𝟙 _)
      rw [Category.id_comp] at h
      exact h
  exact NatIso.isIso_of_isIso_app _

/-- The open restriction comparison descends termwise to bounded-below complexes.
Source: Stacks Tag 0GL6 (blueprint: lemma-sp-reduction--1). -/
def coefficientRestrictionOpenPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :=
  letI := coefficientRestrictionOpenMap_isIso φ j
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (asIso (coefficientRestrictionOpenMap φ j)) ≪≫
    Functor.mapDerivedCategoryPlusCompIso _ _

/-- The canonical proper/open scalar restriction comparison, with its direction
fixed by the open unit and the direct-image resolution map.
Source: Stacks Tag 0GL6 (blueprint: lemma-sp-reduction--1). -/
def compactSupportCoefficientRestrictionPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ≅
      rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c ⋙
        (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategoryPlus :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (coefficientRestrictionOpenPlus φ c.i) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (rightDerivedLowerStarRestrictScalars φ c.g)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- A bounded-below presentation of the actual derived tensor, retaining its universal
arrow in the ambient derived category. Source: Stacks Tags 06YY and 07A6
(blueprint: lemma-sp-reduction--1). -/
structure CoefficientTensorModel
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B) (T : Scheme.{u})
    (K : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) where
  obj : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B))
  unit : K ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).mapDerivedCategoryPlus.obj obj
  universal : Sheaf.IsDerivedBaseChange unit.hom

set_option backward.isDefEq.respectTransparency false in
/-- Scalar extension of a morphism, uniquely specified by the universal arrows.
Source: Stacks Tag 07A6 (blueprint: lemma-sp-reduction--1). -/
def CoefficientTensorModel.map
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B} {T : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ T K) (N : CoefficientTensorModel φ T L) (f : K ⟶ L) :
    M.obj ⟶ N.obj :=
  ObjectProperty.homMk ((Equiv.ofBijective _ (M.universal N.obj.obj)).symm
    (f.hom ≫ N.unit.hom))

/-- The canonical B-linear comparison is the unique arrow with the proper/open
restriction adjunct. Source: Stacks Tags 0GL5, 0GL6 and 07A6
(blueprint: lemma-sp-reduction--1). -/
def compactSupportCoefficientComparisonPlus
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (M : CoefficientTensorModel φ X K)
    (N : CoefficientTensorModel φ Y
      ((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).obj K)) :
    N.obj ⟶
      (rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} B) c).obj M.obj :=
  ObjectProperty.homMk ((Equiv.ofBijective _ (N.universal _)).symm
    (((rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c).map M.unit ≫
      (compactSupportCoefficientRestrictionPlus φ c).hom.app M.obj).hom))

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.ProEtale

private local instance fixedSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _

end AlgebraicGeometry.ProEtale
