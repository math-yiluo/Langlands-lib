/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.FiniteReduction.System.FiniteReductionConstructibility
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothDualityBaseChangeCompat
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
import WeilConjectures.SixFunctors.Etale.Derived.Stability.UpperShriek
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientUnitCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarBaseChange
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.CoefficientExchange
import Mathlib.CategoryTheory.NatIso
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensorSymmetryInvolutive

/-! # Exceptional coefficient comparisons

Source: blueprint main-20261015, sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-compatibilities.proof.md, (2)--(3); Stacks 0GL6 and 0F7L
(blueprint: lem-pur-exceptional-coefficient-comparison).

All scalar functors are the published left adjoints to exact scalar restriction.
The scalar/pullback identification and the proper coefficient map are the recorded
`scalarPullbackIso` and `scalarMate` of lem-pur-etale-scalar-mate-projection.
The comparison for compact support is constructed from its open and proper parts.
The auxiliary tensor and pullback identifications are fixed by their ordinary
adjunctions and their computation on cochain representatives.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u u' v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
namespace ExceptionalCoefficients
variable {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compactSupport_isIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    IsIso (compactSupportMap φ c M) := by
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : CompactSpace c.Z := QuasiCompact.compactSpace_of_compactSpace c.g
  have : IsNoetherian c.Z := ⟨⟩
  have := (properFiniteCoefficientExtension φ c.g).1
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  unfold compactSupportMap
  infer_instance

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Scalar transport of the dualizing complex, obtained by evaluating the exceptional
mate at the coefficient unit and then identifying that unit after extension of scalars.
Source: blueprint compatibilities (3)
(blueprint: def-pur-exceptional-coefficient-tensor-maps). -/
def dualizingScalarMap [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] :
    (scalarExtension φ X).obj (dualizingComplex A f) ⟶
      dualizingComplex B f :=
  mateMap φ f (𝟙_ (DerivedCategoryModule A Y)) ≫
    (rightDerivedUpperShriek B f).map (unitIso φ Y).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem dualizingScalarMap_eq [Finite A] [Finite B] {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] :
    dualizingScalarMap φ f = mateMap φ f (𝟙_ (DerivedCategoryModule A Y)) ≫
      (rightDerivedUpperShriek B f).map (unitIso φ Y).hom := by
  rfl

attribute [irreducible] dualizingScalarMap

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Scalar transport of the smooth tensor domain, using the canonical tensorator,
pullback balancing and c at the coefficient unit. Source: blueprint compatibilities (3)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def tensorDomainMap [Finite A] [Finite B] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (K : DerivedCategoryModule A Y) :
    (scalarExtension φ X).obj
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj
        ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj K)).obj
          (dualizingComplex A f)) ⟶
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).obj (dualizingComplex B f) :=
  compactScalarProjectionTarget φ f K (dualizingComplex A f) ≫
    ((derivedTensor (ModuleCat.{u + 1} B) X).obj
      ((upperStar (ModuleCat.{u + 1} B) f).leftDerivedFunctor.obj
        ((scalarExtension φ Y).obj K))).map
      (dualizingScalarMap φ f)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- The mixed square on the actual Cartesian pullback. Both paths have source
S_X' g'^* G_A K and target G'_B g^* S_Y K; beta is the recorded counit transpose.
Source: Stacks 0F7L and blueprint compatibilities (2)
(blueprint: lem-pur-exceptional-coefficient-comparison). -/
def BaseChangeCompatibility [Finite A] [Finite B] {X Y Y' : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] (g : Y' ⟶ Y)
    (K : DerivedCategoryModule A Y) : Prop :=
  (scalarExtension φ (pullback f g)).map
      ((rightDerivedUpperShriekBaseChangeMap A (IsPullback.of_hasPullback f g)).app K) ≫
      mateMap φ (pullback.snd f g)
        ((upperStar (ModuleCat.{u + 1} A) g).leftDerivedFunctor.obj K) ≫
      (rightDerivedUpperShriek B (pullback.snd f g)).map
        ((scalarPullbackIso φ g).inv.app K) =
    (scalarPullbackIso φ (pullback.fst f g)).inv.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (upperStar (ModuleCat.{u + 1} B) (pullback.fst f g)).leftDerivedFunctor.map
        (mateMap φ f K) ≫
      (rightDerivedUpperShriekBaseChangeMap B (IsPullback.of_hasPullback f g)).app
        ((scalarExtension φ Y).obj K)

attribute [-instance] CategoryTheory.catToReflQuiver in
private def compactSupportIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ≅
      scalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c := by
  let (M : DerivedCategoryModule A X) : IsIso (compactSupportMap φ c M) :=
    compactSupport_isIso φ c M
  exact NatIso.ofComponents (fun M ↦ asIso (compactSupportMap φ c M))
    (fun h ↦ compactScalarMap_naturality φ c h)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compactSupportIso_hom [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) : (compactSupportIso φ c).hom = compactScalarMap φ c := by
  rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compactSupportIso_hom_app [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    (compactSupportIso φ c).hom.app M = compactSupportMap φ c M := by
  rfl

attribute [irreducible] compactSupportIso

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparisonInverse_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] {f : X ⟶ Y}
    (c : Compactification f) (M : DerivedCategoryModule A X) :
    comparisonInverse φ c M = (compactSupportIso φ c).inv.app M := by
  have := compactSupport_isIso φ c M
  simp only [comparisonInverse, dite_eq_left this]
  simpa only [compactSupportIso_hom_app] using
    (NatIso.inv_hom_app (compactSupportIso φ c) M)

attribute [-instance] CategoryTheory.catToReflQuiver in
private def chosenCompactSupportIso [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙ scalarExtension φ Y ≅
      scalarExtension φ X ⋙ rightDerivedLowerShriek (ModuleCat.{u + 1} B) f :=
  compactSupportIso φ (HasCompactification.compactification f)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem chosenCompactSupportIso_hom [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f] :
    (chosenCompactSupportIso φ f).hom = compactScalarChosenMap φ f := by
  exact compactSupportIso_hom φ (HasCompactification.compactification f)

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem comparisonInverse_chosen_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A X) :
    comparisonInverse φ (HasCompactification.compactification f) M =
      (chosenCompactSupportIso φ f).inv.app M := by
  exact comparisonInverse_eq φ (HasCompactification.compactification f) M

attribute [irreducible] chosenCompactSupportIso

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mateMap_eq [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule A Y) :
    mateMap φ f K =
      (mateEquiv (rightDerivedUpperShriekAdjunction A f)
        (rightDerivedUpperShriekAdjunction B f)
        (TwoSquare.mk _ _ _ _
          (compactSupportIso φ (HasCompactification.compactification f)).inv)).app K := by
  apply ((rightDerivedUpperShriekAdjunction
    B f).homEquiv _ _).symm.injective
  rw [mateMap, Equiv.symm_apply_apply, Adjunction.homEquiv_counit, mateEquiv_counit]
  rw [comparisonInverse_eq]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mate_cocycle_at
    {C₁ D₁ C₂ D₂ C₃ D₃ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Category C₃] [Category D₃]
    {P₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {P₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    {P₃ : C₃ ⥤ D₃} {R₃ : D₃ ⥤ C₃}
    (a₁ : P₁ ⊣ R₁) (a₂ : P₂ ⊣ R₂) (a₃ : P₃ ⊣ R₃)
    {S : C₁ ⥤ C₂} {T : D₁ ⥤ D₂} {U : C₂ ⥤ C₃} {V : D₂ ⥤ D₃}
    {W : C₁ ⥤ C₃} {Z : D₁ ⥤ D₃}
    (α : TwoSquare S P₁ P₂ T) (β : TwoSquare U P₂ P₃ V)
    (γ : TwoSquare W P₁ P₃ Z) (eX : S ⋙ U ≅ W) (eY : T ⋙ V ≅ Z)
    (K : D₁)
    (hc : P₃.map (eX.hom.app (R₁.obj K)) ≫ γ.app (R₁.obj K) =
      β.app (S.obj (R₁.obj K)) ≫ V.map (α.app (R₁.obj K)) ≫
        eY.hom.app (P₁.obj (R₁.obj K))) :
    U.map ((mateEquiv a₁ a₂ α).app K) ≫
        (mateEquiv a₂ a₃ β).app (T.obj K) ≫ R₃.map (eY.hom.app K) =
      eX.hom.app (R₁.obj K) ≫ (mateEquiv a₁ a₃ γ).app K := by
  apply (a₃.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [show P₃.map (R₃.map (eY.hom.app K)) ≫ a₃.counit.app _ =
    a₃.counit.app _ ≫ eY.hom.app K from a₃.counit.naturality _]
  slice_lhs 2 3 => rw [mateEquiv_counit]
  slice_lhs 1 2 => exact β.naturality _
  simp only [Functor.comp_map, Category.assoc]
  slice_lhs 2 3 => rw [← V.map_comp, mateEquiv_counit, V.map_comp]
  simp only [Category.assoc]
  slice_lhs 3 4 => exact eY.hom.naturality (a₁.counit.app K)
  slice_lhs 1 3 => exact hc.symm
  rw [mateEquiv_counit]
  exact Category.assoc _ _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mateMap_counit [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y] (f : X ⟶ Y) [HasCompactification f]
    (K : DerivedCategoryModule A Y) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map (mateMap φ f K) ≫
        (rightDerivedUpperShriekAdjunction B f).counit.app
          ((scalarExtension φ Y).obj K) =
      (chosenCompactSupportIso φ f).inv.app
        ((rightDerivedUpperShriek A f).obj K) ≫
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app K) := by
  rw [← comparisonInverse_chosen_eq]
  exact (rightDerivedUpperShriekAdjunction B f).homEquiv
    _ ((scalarExtension φ Y).obj K) |>.symm_apply_apply _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem mate_unit_evaluation
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {P : C ⥤ D} {G : D ⥤ C} {P' : C' ⥤ D'} {G' : D' ⥤ C'}
    (a : P ⊣ G) (a' : P' ⊣ G') (S : C ⥤ C') (T : D ⥤ D')
    (b : P ⋙ T ≅ S ⋙ P') (c : ∀ K, S.obj (G.obj K) ⟶ G'.obj (T.obj K))
    (hc : ∀ K, P'.map (c K) ≫ a'.counit.app (T.obj K) =
      b.inv.app (G.obj K) ≫ T.map (a.counit.app K))
    {I : D} {I' : D'} (e : T.obj I ⟶ I') :
    b.hom.app (G.obj I) ≫ P'.map (c I ≫ G'.map e) ≫ a'.counit.app I' =
      T.map (a.counit.app I) ≫ e := by
  have hn := a'.counit.naturality e
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn, reassoc_of% (hc I)]
  exact Iso.hom_inv_id_app_assoc b _ _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem tensor_unit_counit [Finite A] [Finite B]
    {X Y : Scheme.{u}} [IsNoetherian Y]
    (f : X ⟶ Y) [HasCompactification f] :
    (chosenCompactSupportIso φ f).hom.app
        (dualizingComplex A f) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f).map
        (dualizingScalarMap φ f) ≫
      (rightDerivedUpperShriekAdjunction B f).counit.app
        (𝟙_ (DerivedCategoryModule B Y)) =
      (scalarExtension φ Y).map
        ((rightDerivedUpperShriekAdjunction A f).counit.app
        (𝟙_ (DerivedCategoryModule A Y))) ≫ (unitIso φ Y).hom := by
  rw [dualizingScalarMap_eq]
  exact mate_unit_evaluation
    (rightDerivedUpperShriekAdjunction A f)
    (rightDerivedUpperShriekAdjunction B f)
    (scalarExtension φ X) (scalarExtension φ Y)
    (chosenCompactSupportIso φ f)
    (mateMap φ f) (mateMap_counit φ f) (unitIso φ Y).hom

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem compact_scalar_exchange_left [Finite A] [Finite B]
    {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f']
    [HasCompactification f] [HasCompactification f']
    (sq : IsPullback h f' f g)
    (M : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (hQM : ∃ N : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)),
      N.obj = (scalarExtension φ X).obj M.obj) :
    (upperStar (ModuleCat.{u + 1} B) g).leftDerivedFunctor.map
        ((compactScalarChosenMap φ f).app M.obj) ≫
      (rightDerivedLowerShriekBaseChangeMap B sq).app ((scalarExtension φ X).obj M.obj) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
        ((scalarPullbackIso φ h).hom.app M.obj) =
      (scalarPullbackIso φ g).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M.obj) ≫
      (scalarExtension φ Y').map ((rightDerivedLowerShriekBaseChangeMap A sq).app M.obj) ≫
      (compactScalarChosenMap φ f').app
        ((upperStar (ModuleCat.{u + 1} A) h).leftDerivedFunctor.obj M.obj) := by
  have hh := compactScalarChosenMap_baseChange φ sq M hQM
  simp only [properOpenCoefficientPullbackIso, unboundedEtaleCompactSupportBaseChange,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] at hh
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) g).inv.naturality
    ((compactScalarChosenMap φ f).app M.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map] at hh hn ⊢
  erw [reassoc_of% hn] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp] at hh
  have hb := (compactScalarChosenMap φ f').naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hb
  dsimp only [rightDerivedLowerShriek, rightDerivedLowerShriekOfCompactification,
    Functor.comp_obj, Functor.comp_map] at hb
  simp only [Functor.map_comp, Category.assoc] at hh
  erw [hb] at hh
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc] at hh
  apply (cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} B) g).inv.app _)).1
  apply (cancel_mono ((rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
    ((scalarExtension φ X').map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M.obj)))).1
  simpa only [Category.assoc, rightDerivedLowerShriek,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map] using hh

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exactFaithful_reflects_plus
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory.{w} C]
    [Category D] [Abelian D] [HasDerivedCategory.{w} D]
    (U : C ⥤ D) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [U.Faithful] (M : _root_.DerivedCategory C)
    (hM : _root_.DerivedCategory.TStructure.t.plus (U.mapDerivedCategory.obj M)) :
    _root_.DerivedCategory.TStructure.t.plus M := by
  obtain ⟨n, hn⟩ := hM
  refine ⟨n, (_root_.DerivedCategory.isGE_iff _ n).mpr (fun i hi ↦ ?_)⟩
  have hz := (_root_.DerivedCategory.isGE_iff _ n).mp hn i hi
  have hz' : IsZero (U.obj ((_root_.DerivedCategory.homologyFunctor C i).obj M)) :=
    hz.of_iso ((U.mapDerivedCategoryHomologyFunctorIso i).app M)
  apply (IsZero.iff_id_eq_zero _).mpr
  apply U.map_injective
  exact hz'.eq_of_src _ _

private theorem finiteTor_tensor_plus_onSite
    (C : Type v) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [SymmetricCategory C]
    [Abelian.HasFunctorialFlatResolution C] (T : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf T.smallEtaleTopology C))
    (hM : DerivedCategory.finiteTorAmplitude C T M)
    (N : Sheaf T.smallEtaleTopology C) :
    _root_.DerivedCategory.TStructure.t.plus
      (((derivedTensor C T).obj M).obj ((_root_.DerivedCategory.singleFunctor _ 0).obj N)) := by
  obtain ⟨a, b, htor⟩ := hM
  exact ⟨a, (htor N).1⟩

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem scalar_extension_plus_of_finiteTor
    (T : Scheme.{u}) (M : DerivedCategoryModule A T)
    (hM : DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} A) T M) :
    _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ T).obj M) := by
  let U := Sheaf.restrictScalars T.smallEtaleTopology φ
  have ht := finiteTor_tensor_plus_onSite (ModuleCat.{u + 1} A) T M hM
    (scalarCoefficientSheaf φ T)
  have hres : _root_.DerivedCategory.TStructure.t.plus
      (U.mapDerivedCategory.obj ((scalarExtension φ T).obj M)) :=
    _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
      ((scalarTensorIso φ T).app M).symm ht
  exact exactFaithful_reflects_plus U _ hres

end ExceptionalCoefficients

end AlgebraicGeometry.Etale
