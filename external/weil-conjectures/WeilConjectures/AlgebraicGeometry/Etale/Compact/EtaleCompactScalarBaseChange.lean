/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarExchangeSquare
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectImageScalarExchange

/-! # Scalar extension and compactly supported base change -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem open_scalar_exchange_forward
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {U' U T' T : Scheme.{u}} {h : U' ⟶ U} {j' : U' ⟶ T'}
    {j : U ⟶ T} {g : T' ⟶ T} [IsOpenImmersion j] [IsOpenImmersion j']
    (sq : IsPullback h j' j g) (M : DerivedCategoryModule A U) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((ExceptionalCoefficients.openIso φ j).hom.app M) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} B) sq).inv.app ((scalarExtension φ U).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j').mapDerivedCategory.map
        ((properOpenCoefficientPullbackIso φ h).hom.app M) =
      (properOpenCoefficientPullbackIso φ g).hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
      (scalarExtension φ T').map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} A) sq).inv.app M) ≫
      (ExceptionalCoefficients.openIso φ j').hom.app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) := by
  have hh := properOpenCoefficientOpenInverse_baseChange φ sq M
  simp only [← compactScalarOpen_normalization] at hh
  have hi := IsIso.inv_eq_inv.mpr hh
  simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_inv_app,
    NatIso.inv_hom_app, Category.assoc] using hi

private theorem compact_scalar_exchange_raw
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian Y] [IsNoetherian Y']
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y' ⟶ Y} {h : X' ⟶ X}
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (sq : IsPullback h f' f g) (c : Compactification f)
    (M : DerivedCategoryModule A X) :
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((compactScalarMap φ c).app M) ≫
      (unboundedEtaleCompactSupportExchange B sq c).app ((scalarExtension φ X).obj M) ≫
      (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B)
        (c.ofIsPullback sq)).map ((properOpenCoefficientPullbackIso φ h).hom.app M) =
      (properOpenCoefficientPullbackIso φ g).hom.app
        ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).obj M) ≫
      (scalarExtension φ Y').map ((unboundedEtaleCompactSupportExchange A sq c).app M) ≫
      (compactScalarMap φ (c.ofIsPullback sq)).app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) := by
  let psq : ChosenCartesianSquare (pullback.fst c.g g) (pullback.snd c.g g) c.g g :=
    { toCommSq := (IsPullback.of_hasPullback c.g g).toCommSq
      isoPullback := Iso.refl _
      hom_fst := Category.id_comp _
      hom_snd := Category.id_comp _ }
  have hp := exactDerivedBaseChangeMap_scalarExtension φ _ _ _ _ psq
    ((openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory.obj M)
  have ho := open_scalar_exchange_forward φ (c.isPullback_i_ofIsPullback sq) M
  have hn := (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) psq.toCommSq).naturality
    ((ExceptionalCoefficients.openIso φ c.i).hom.app M)
  have hm := (scalarMate φ (c.ofIsPullback sq).g).naturality
    ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} A) (c.isPullback_i_ofIsPullback sq)).inv.app M)
  simp only [unboundedEtaleCompactSupport_exchange_normalization,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc]
  dsimp only [compactScalarMap, ExceptionalCoefficients.compactSupportMap,
    rightDerivedLowerShriekOfCompactification, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hm
  dsimp only [Compactification.ofIsPullback, rightDerivedLowerStar] at ho hm hp hn ⊢
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp]
  erw [ho]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hp, reassoc_of% hm]

private theorem chosen_exchange_app
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {h : X' ⟶ X}
    [HasCompactification f] [HasCompactification f'] [QuasiCompact f']
    (sq : IsPullback h f' f g) (M : DerivedCategoryModule A X) :
    (unboundedEtaleCompactSupportBaseChange A sq).app M =
      (unboundedEtaleCompactSupportExchange A sq
        (HasCompactification.compactification f)).app M ≫
      (rightDerivedLowerShriekIso A
        ((HasCompactification.compactification f).ofIsPullback sq)).hom.app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M) := by
  simp only [unboundedEtaleCompactSupportBaseChange,
    unboundedEtaleCompactSupportExchange, rightDerivedLowerShriekBaseChangeMap,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc]
  erw [← (rightDerivedLowerShriekIso A
    ((HasCompactification.compactification f).ofIsPullback sq)).hom.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) h).hom.app M)]
  rfl

/-- Scalar extension respects compactly supported exchange when the source input
and its scalar extension are bounded below.
Source: Stacks 0F7L, 0GL6, 03S6 and 07A7
(blueprint: lem-pur-compact-scalar-base-change).
Proof: on a compactification expand exchange as proper exchange followed by inverse
open exchange. The proper scalar square and the open scalar square paste by
naturality, giving the square for the base-changed compactification. Exact inverse
image preserves the two bounded-below inputs. The scalar/pullback comparison supplies
the scalar bound after inverse image. Coefficient refinement coherence then transfers
the result from the base-changed compactification to the chosen compactification.
The normalization of exact compact-support exchange supplies the asserted maps. -/
theorem compactScalarChosenMap_baseChange
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X X' Y Y' : Scheme.{u}}
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
    (upperStar (ModuleCat.{u + 1} B) g).mapDerivedCategory.map
        ((compactScalarChosenMap φ f).app M.obj) ≫
      (unboundedEtaleCompactSupportBaseChange B sq).app ((scalarExtension φ X).obj M.obj) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} B) f').map
        ((properOpenCoefficientPullbackIso φ h).hom.app M.obj) =
      (properOpenCoefficientPullbackIso φ g).hom.app
        ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).obj M.obj) ≫
      (scalarExtension φ Y').map ((unboundedEtaleCompactSupportBaseChange A sq).app M.obj) ≫
      (compactScalarChosenMap φ f').app
        ((upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategory.obj M.obj) := by
  let c := HasCompactification.compactification f
  let d := c.ofIsPullback sq
  let e := HasCompactification.compactification f'
  let M' := (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus.obj M
  obtain ⟨N, hN⟩ := hQM
  have hpre : _root_.DerivedCategory.TStructure.t.plus
      ((upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategory.obj
        ((scalarExtension φ X).obj M.obj)) := by
    rw [← hN]
    exact ((upperStar (ModuleCat.{u + 1} B) h).mapDerivedCategoryPlus.obj N).property
  have hpost := _root_.DerivedCategory.TStructure.t.plus.prop_of_iso
    ((properOpenCoefficientPullbackIso φ h).app M.obj) hpre
  have hQM' : ∃ N' : _root_.DerivedCategory.Plus
      (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} B)),
      N'.obj = (scalarExtension φ X').obj M'.obj := ⟨⟨_, hpost⟩, rfl⟩
  have hc := (compactScalarMap_coherence φ f' d).2.2 e M' hQM'
  have hn := (rightDerivedLowerShriekIso B d).hom.naturality
    ((properOpenCoefficientPullbackIso φ h).hom.app M.obj)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [chosen_exchange_app, Category.assoc]
  erw [← hn]
  erw [reassoc_of% (compact_scalar_exchange_raw φ sq c M.obj)]
  change _ = _
  erw [← hc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
