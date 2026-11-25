/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerOrdinaryProperOpenArrows
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionSquare
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
-- Vertical uses singleAlpha_restriction_normalized; horizontal uses singleAlpha_restriction.
-- Both restriction identities must coexist when these dependency branches are imported.
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaVerticalModules
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaHorizontalModules
import all WeilConjectures.AlgebraicGeometry.StrictTower.ProperOpenAlphaBaseChangeModules

/-! # Intrinsic clopen alpha commutes with pasting and pullback before derivation

Source: Stacks Project, Tags 0F7C, 0F7D, 0F7F, 09AH and 09BN, with the arbitrary-ring
underived strict-tower refinement in the blueprint.
(blueprint: lem-cbc-proper-open-alpha-pasting)

Each law includes equality on module sheaves, on strict towers, on their unbounded
complexes, and on their ordinary unbounded derived categories. The two ordinary paths
are written with all inverse-image and open-extension compositors inserted.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

/-- The alphaVerticalPasted ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaVerticalPasted {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j) :
    moduleJ B j ⋙ modulePullback B (p₁ ≫ p₂) ⟶
      (modulePullback B r₂ ⋙ modulePullback B r₁) ⋙ moduleJ B k :=
  Functor.whiskerLeft (moduleJ B j) (moduleGComp B p₁ p₂).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (singleAlpha B i r₂ p₂ j h₂) (modulePullback B p₁) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback B r₂) (singleAlpha B k r₁ p₁ i h₁) ≫
    (Functor.associator _ _ _).inv

/-- The alphaVerticalOuter ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaVerticalOuter {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    moduleJ B j ⋙ modulePullback B (p₁ ≫ p₂) ⟶
      (modulePullback B r₂ ⋙ modulePullback B r₁) ⋙ moduleJ B k :=
  singleAlpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h ≫
    Functor.whiskerRight (moduleGComp B r₁ r₂).hom (moduleJ B k)

/-- The alphaHorizontalOuter ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaHorizontalOuter {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper q]
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) :
    (moduleJ B i ⋙ moduleJ B j) ⋙ modulePullback B q ⟶
      modulePullback B r ⋙ moduleJ B (k ≫ l) :=
  Functor.whiskerRight (openBetaModuleJComp B i j).hom (modulePullback B q) ≫
    singleAlpha B (k ≫ l) r q (i ≫ j) h

/-- The alphaHorizontalPasted ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaHorizontalPasted {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j) :
    (moduleJ B i ⋙ moduleJ B j) ⋙ modulePullback B q ⟶
      modulePullback B r ⋙ moduleJ B (k ≫ l) :=
  (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (moduleJ B i) (singleAlpha B l p q j h₂) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (singleAlpha B k r p i h₁) (moduleJ B l) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback B r) (openBetaModuleJComp B k l).hom

/-- The alphaCubeOriginal ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaCubeOriginal {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i)
    (wk : d ≫ k = k₁ ≫ a)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) :
    moduleJ B i ⋙ (modulePullback B b ⋙ modulePullback B p₁) ⟶
      (modulePullback B c ⋙ modulePullback B r₁) ⋙ moduleJ B k₁ :=
  Functor.whiskerLeft (moduleJ B i) (moduleSquareG B a p₁ p b wp).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (singleAlpha B k r p i h) (modulePullback B a) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback B r) (openBetaModule B d k₁ k a wk sk).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (moduleSquareG B d r₁ r c wr).inv (moduleJ B k₁)

/-- The alphaCubeChanged ordinary path, with the canonical compositors inserted.
Source: Stacks, Tags 0F7C, 0F7D and 0F7F
(blueprint: lem-cbc-proper-open-alpha-pasting). -/
def alphaCubeChanged {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (b : T₁ ⟶ T) (c : S₁ ⟶ S)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wi : c ≫ i = i₁ ≫ b)
    (si : IsPullback c i₁ i b) :
    moduleJ B i ⋙ (modulePullback B b ⋙ modulePullback B p₁) ⟶
      (modulePullback B c ⋙ modulePullback B r₁) ⋙ moduleJ B k₁ :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (openBetaModule B c i₁ i b wi si).hom (modulePullback B p₁) ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (modulePullback B c) (singleAlpha B k₁ r₁ p₁ i₁ h₁) ≫
    (Functor.associator _ _ _).inv

attribute [local irreducible] G J

/-- Intrinsic alpha obeys vert pasting at the four specified levels.
Source: Stacks, Tag 0F7C, and the underived strict-tower refinement, proof steps 1--7
(blueprint: lem-cbc-proper-open-alpha-pasting).
Proof: First detect equality of maps to open extension on module sheaves: the image of
their difference restricts to zero both on the open and its closed complement.
Exact inverse image and the open/closed short exact sequence force that image to vanish.
The inverse-transpose definition of beta gives its restriction normalization through
the specified open units. The clopen projector restricts to the identity, so intrinsic
alpha restricts to the canonical inverse-image square identification followed by
inverse image of the inverse open unit. All detection opens are quasi-compact.
For vertical pasting, restrict along k and use p₁k = ir₁. The second square reduces
the input to r₁* r₂* of the original module. The first alpha is then the identity
under its open-unit identification. The inverse-image compositor identifies this
with the restriction of intrinsic outer alpha. Detection gives the module equation.
Naturality makes the module transformations commute with all tower transitions,
then with all differentials on unbounded complexes. Termwise application gives the
second and third equations. Apply exact-derived-transformation pasting to the finite
diagram. Exactness of inverse image and open extension and the localization
specification of alpha identify its localized cells with the recorded intrinsic
alpha, beta and compositors. This gives the last equation in the ordinary unbounded
derived category; no derived-evaluation faithfulness or coefficient finiteness is used. -/
theorem alpha_vertical_beforeDerivation {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (i : C ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C) (r₂ : C ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
    [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) :
    alphaVerticalPasted B k i j r₁ r₂ p₁ p₂ h₁ h₂ =
      alphaVerticalOuter B k j r₁ r₂ p₁ p₂ h ∧
    NatTrans.mapHomologicalComplex
        (alphaVerticalPasted B k i j r₁ r₂ p₁ p₂ h₁ h₂) (.up ℤ) =
      NatTrans.mapHomologicalComplex
        (alphaVerticalOuter B k j r₁ r₂ p₁ p₂ h) (.up ℤ) ∧
    (Functor.whiskeringRight ℕᵒᵖ (Modules B E) (Modules B B₀)).map
        (alphaVerticalPasted B k i j r₁ r₂ p₁ p₂ h₁ h₂) =
      (Functor.whiskeringRight ℕᵒᵖ (Modules B E) (Modules B B₀)).map
        (alphaVerticalOuter B k j r₁ r₂ p₁ p₂ h) ∧
    NatTrans.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ (Modules B E) (Modules B B₀)).map
          (alphaVerticalPasted B k i j r₁ r₂ p₁ p₂ h₁ h₂)) (.up ℤ) =
      NatTrans.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ (Modules B E) (Modules B B₀)).map
          (alphaVerticalOuter B k j r₁ r₂ p₁ p₂ h)) (.up ℤ) ∧
    ∀ N : Derived B E,
      (gComp B p₁ p₂).hom.app ((J B j).obj N) ≫
          (G B p₁).map ((alpha B i r₂ p₂ j h₂).app N) ≫
          (alpha B k r₁ p₁ i h₁).app ((G B r₂).obj N) =
        (alpha B k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app N ≫
          (J B k).map ((gComp B r₁ r₂).hom.app N) := by
  have hm : alphaVerticalPasted B k i j r₁ r₂ p₁ p₂ h₁ h₂ =
      alphaVerticalOuter B k j r₁ r₂ p₁ p₂ h := by
    apply NatTrans.ext
    funext M
    simpa only [alphaVerticalPasted, alphaVerticalOuter, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc] using
      singleAlpha_vertical B k i j r₁ r₂ p₁ p₂ h₁ h₂ h M
  refine ⟨hm, ?_, ?_, ?_, vertical_derived B k i j r₁ r₂ p₁ p₂ h₁ h₂ h⟩
  all_goals rw [hm]

/-- Intrinsic alpha obeys horiz pasting at the four specified levels.
Source: Stacks, Tag 0F7D, and the underived strict-tower refinement, proof steps 1--7
(blueprint: lem-cbc-proper-open-alpha-pasting).
Proof: First detect equality of maps to open extension on module sheaves: the image of
their difference restricts to zero both on the open and its closed complement.
Exact inverse image and the open/closed short exact sequence force that image to vanish.
The inverse-transpose definition of beta gives its restriction normalization through
the specified open units. The clopen projector restricts to the identity, so intrinsic
alpha restricts to the canonical inverse-image square identification followed by
inverse image of the inverse open unit. All detection opens are quasi-compact.
For horizontal pasting, restrict along lk. The second alpha reduces q* j! i! to
p* i!; the open unit for l and then the first alpha reduce this to r*. The
unit-preserving open compositor identifies the successive open units with the
outer open unit. Detection along lk identifies the pasted and intrinsic outer maps.
Naturality makes the module transformations commute with all tower transitions,
then with all differentials on unbounded complexes. Termwise application gives the
second and third equations. Apply exact-derived-transformation pasting to the finite
diagram. Exactness of inverse image and open extension and the localization
specification of alpha identify its localized cells with the recorded intrinsic
alpha, beta and compositors. This gives the last equation in the ordinary unbounded
derived category; no derived-evaluation faithfulness or coefficient finiteness is used. -/
theorem alpha_horizontal_beforeDerivation {A C E B₀ D F : Scheme.{u}}
    (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C) (p : B₀ ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
    [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
    [IsProper r] [IsProper p] [IsProper q]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) :
    alphaHorizontalOuter B k l i j r q h =
      alphaHorizontalPasted B k l i j r p q h₁ h₂ ∧
    NatTrans.mapHomologicalComplex
        (alphaHorizontalOuter B k l i j r q h) (.up ℤ) =
      NatTrans.mapHomologicalComplex
        (alphaHorizontalPasted B k l i j r p q h₁ h₂) (.up ℤ) ∧
    (Functor.whiskeringRight ℕᵒᵖ (Modules B C) (Modules B E)).map
        (alphaHorizontalOuter B k l i j r q h) =
      (Functor.whiskeringRight ℕᵒᵖ (Modules B C) (Modules B E)).map
        (alphaHorizontalPasted B k l i j r p q h₁ h₂) ∧
    NatTrans.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ (Modules B C) (Modules B E)).map
          (alphaHorizontalOuter B k l i j r q h)) (.up ℤ) =
      NatTrans.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ (Modules B C) (Modules B E)).map
          (alphaHorizontalPasted B k l i j r p q h₁ h₂)) (.up ℤ) ∧
    ∀ N : Derived B C,
      (G B q).map ((jComp B i j).hom.app N) ≫
          (alpha B (k ≫ l) r q (i ≫ j) h).app N =
        (alpha B l p q j h₂).app ((J B i).obj N) ≫
          (J B l).map ((alpha B k r p i h₁).app N) ≫
          (jComp B k l).hom.app ((G B r).obj N) := by
  have hm : alphaHorizontalOuter B k l i j r q h =
      alphaHorizontalPasted B k l i j r p q h₁ h₂ := by
    apply NatTrans.ext
    funext M
    simpa only [alphaHorizontalOuter, alphaHorizontalPasted, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc] using
      singleAlpha_horizontal B k l i j r p q h₁ h₂ h M
  refine ⟨hm, ?_, ?_, ?_, horizontal_derived B k l i j r p q h₁ h₂ h⟩
  all_goals rw [hm]

/-- Intrinsic alpha obeys cube pasting at the four specified levels.
Source: Stacks, Tag 0F7F, and the underived strict-tower refinement, proof steps 1--7
(blueprint: lem-cbc-proper-open-alpha-pasting).
Proof: First detect equality of maps to open extension on module sheaves: the image of
their difference restricts to zero both on the open and its closed complement.
Exact inverse image and the open/closed short exact sequence force that image to vanish.
The inverse-transpose definition of beta gives its restriction normalization through
the specified open units. The clopen projector restricts to the identity, so intrinsic
alpha restricts to the canonical inverse-image square identification followed by
inverse image of the inverse open unit. All detection opens are quasi-compact.
For base change, restrict along k₁. The original-alpha route reduces through
ak₁ = kd to d* r*, then through rd = cr₁ to r₁* c*. The beta for k is exactly
the open-unit identification. On the changed-alpha route the beta for i first gives
that same open-unit identification, and intrinsic alpha for Q₁ reduces to r₁* c*.
The initial square identification for hp₁ = pa makes the starting comparisons equal.
Detection gives the cube equation without proper direct-image base change.
Naturality makes the module transformations commute with all tower transitions,
then with all differentials on unbounded complexes. Termwise application gives the
second and third equations. Apply exact-derived-transformation pasting to the finite
diagram. Exactness of inverse image and open extension and the localization
specification of alpha identify its localized cells with the recorded intrinsic
alpha, beta and compositors. This gives the last equation in the ordinary unbounded
derived category; no derived-evaluation faithfulness or coefficient finiteness is used. -/
theorem alpha_baseChange_beforeDerivation {V W S T V₁ W₁ S₁ T₁ : Scheme.{u}}
    (k : V ⟶ W) (i : S ⟶ T) (r : V ⟶ S) (p : W ⟶ T)
    (k₁ : V₁ ⟶ W₁) (i₁ : S₁ ⟶ T₁) (r₁ : V₁ ⟶ S₁) (p₁ : W₁ ⟶ T₁)
    (a : W₁ ⟶ W) (b : T₁ ⟶ T) (c : S₁ ⟶ S) (d : V₁ ⟶ V)
    [IsOpenImmersion k] [IsOpenImmersion i]
    [IsOpenImmersion k₁] [IsOpenImmersion i₁]
    [QuasiCompact k] [QuasiCompact i] [QuasiCompact k₁] [QuasiCompact i₁]
    [IsProper r] [IsProper p] [IsProper r₁] [IsProper p₁]
    (h : k ≫ p = r ≫ i) (h₁ : k₁ ≫ p₁ = r₁ ≫ i₁)
    (wk : d ≫ k = k₁ ≫ a) (wi : c ≫ i = i₁ ≫ b)
    (wp : a ≫ p = p₁ ≫ b) (wr : d ≫ r = r₁ ≫ c)
    (sk : IsPullback d k₁ k a) (si : IsPullback c i₁ i b)
    (sp : IsPullback a p₁ p b) (sr : IsPullback d r₁ r c) :
    alphaCubeOriginal B k i r p k₁ i₁ r₁ p₁ a b c d h wk wp wr sk =
      alphaCubeChanged B k i r p k₁ i₁ r₁ p₁ b c h₁ wi si ∧
    NatTrans.mapHomologicalComplex
        (alphaCubeOriginal B k i r p k₁ i₁ r₁ p₁ a b c d h wk wp wr sk) (.up ℤ) =
      NatTrans.mapHomologicalComplex
        (alphaCubeChanged B k i r p k₁ i₁ r₁ p₁ b c h₁ wi si) (.up ℤ) ∧
    (Functor.whiskeringRight ℕᵒᵖ (Modules B S) (Modules B W₁)).map
        (alphaCubeOriginal B k i r p k₁ i₁ r₁ p₁ a b c d h wk wp wr sk) =
      (Functor.whiskeringRight ℕᵒᵖ (Modules B S) (Modules B W₁)).map
        (alphaCubeChanged B k i r p k₁ i₁ r₁ p₁ b c h₁ wi si) ∧
    NatTrans.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ (Modules B S) (Modules B W₁)).map
          (alphaCubeOriginal B k i r p k₁ i₁ r₁ p₁ a b c d h wk wp wr sk)) (.up ℤ) =
      NatTrans.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ (Modules B S) (Modules B W₁)).map
          (alphaCubeChanged B k i r p k₁ i₁ r₁ p₁ b c h₁ wi si)) (.up ℤ) ∧
    ∀ N : Derived B S,
      (squareG B a p₁ p b wp).hom.app ((J B i).obj N) ≫
          (G B a).map ((alpha B k r p i h).app N) ≫
          (beta B d k₁ k a wk sk).hom.app ((G B r).obj N) ≫
          (J B k₁).map ((squareG B d r₁ r c wr).inv.app N) =
        (G B p₁).map ((beta B c i₁ i b wi si).hom.app N) ≫
          (alpha B k₁ r₁ p₁ i₁ h₁).app ((G B c).obj N) := by
  have hm : alphaCubeOriginal B k i r p k₁ i₁ r₁ p₁ a b c d h wk wp wr sk =
      alphaCubeChanged B k i r p k₁ i₁ r₁ p₁ b c h₁ wi si := by
    apply NatTrans.ext
    funext M
    simpa only [alphaCubeOriginal, alphaCubeChanged, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id,
      Category.assoc] using
      singleAlpha_baseChange B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si sp sr M
  refine ⟨hm, ?_, ?_, ?_, cube_derived B k i r p k₁ i₁ r₁ p₁ a b c d h h₁ wk wi wp wr sk si sp sr⟩
  all_goals rw [hm]

end AlgebraicGeometry.ProEtale.StrictTower
