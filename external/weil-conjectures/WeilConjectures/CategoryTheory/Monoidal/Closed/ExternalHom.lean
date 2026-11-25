/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Functor
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!

# The external Hom pairing

Let `P : C₁ ⥤ C` and `Q : C₂ ⥤ C` be lax monoidal functors into a braided monoidal category, for
monoidal closed `C₁`, `C₂`. Write `A ⊠ B = P A ⊗ Q B`. The *external Hom pairing*
```
(E₁ ⊠ E₂) ⊗ (RHom(E₁, L₁) ⊠ RHom(E₂, L₂))
  ≅ (P E₁ ⊗ P RHom(E₁, L₁)) ⊗ (Q E₂ ⊗ Q RHom(E₂, L₂))
  ⟶ P (E₁ ⊗ RHom(E₁, L₁)) ⊗ Q (E₂ ⊗ RHom(E₂, L₂)) ⟶ L₁ ⊠ L₂
```
(`CategoryTheory.externalHomPairing`) is the middle-four interchange, the monoidal structures of
`P` and `Q` and the two evaluations; its transpose is the external Hom map `β` of blueprint
`lemma-external-duality-trace-morphism` (iii).

For `E₁ = 𝟙` the pairing reduces, through `M ≅ RHom(𝟙, M)` and `𝟙 ⊠ N ≅ Q N`, to the braiding
followed by the evaluation in the second factor
(`CategoryTheory.externalHomPairing_unit`). This is how the Künneth–Verdier map
`κ = RHom(1, α) ∘ β` of blueprint `lemma-external-duality-trace-morphism` (iv) unfolds.

-/

@[expose] public section

open CategoryTheory MonoidalCategory MonoidalClosed Functor.LaxMonoidal

namespace CategoryTheory

variable {C₁ C₂ C : Type*} [Category C₁] [MonoidalCategory C₁] [MonoidalClosed C₁]
  [Category C₂] [MonoidalCategory C₂] [MonoidalClosed C₂]
  [Category C] [MonoidalCategory C] [BraidedCategory C]
  (P : C₁ ⥤ C) (Q : C₂ ⥤ C) [P.Monoidal] [Q.LaxMonoidal]

/-- The *external Hom pairing*
`(P E₁ ⊗ Q E₂) ⊗ (P RHom(E₁, L₁) ⊗ Q RHom(E₂, L₂)) ⟶ P L₁ ⊗ Q L₂`: the middle-four
interchange, the monoidal structures of `P` and `Q` and the two evaluations. -/
noncomputable def externalHomPairing (E₁ L₁ : C₁) (E₂ L₂ : C₂) :
    (P.obj E₁ ⊗ Q.obj E₂) ⊗ (P.obj ((ihom E₁).obj L₁) ⊗ Q.obj ((ihom E₂).obj L₂)) ⟶
      P.obj L₁ ⊗ Q.obj L₂ :=
  tensorμ _ _ _ _ ≫ (μ P _ _ ⊗ₘ μ Q _ _) ≫
    (P.map ((ihom.ev E₁).app L₁) ⊗ₘ Q.map ((ihom.ev E₂).app L₂))

/-- The *external Hom map* `β : RHom(E₁, L₁) ⊠ RHom(E₂, L₂) ⟶ RHom(E₁ ⊠ E₂, L₁ ⊠ L₂)`
(blueprint `lemma-external-duality-trace-morphism` (iii)), the transpose of the external Hom
pairing. -/
noncomputable def externalHomMap [MonoidalClosed C] (E₁ L₁ : C₁) (E₂ L₂ : C₂) :
    P.obj ((ihom E₁).obj L₁) ⊗ Q.obj ((ihom E₂).obj L₂) ⟶
      (ihom (P.obj E₁ ⊗ Q.obj E₂)).obj (P.obj L₁ ⊗ Q.obj L₂) :=
  curry (externalHomPairing P Q E₁ L₁ E₂ L₂)

/-- The identification `Q N ≅ 𝟙 ⊠ N = P 𝟙 ⊗ Q N`. -/
noncomputable def unitExternalMap (N : C₂) : Q.obj N ⟶ P.obj (𝟙_ C₁) ⊗ Q.obj N :=
  (λ_ _).inv ≫ (ε P ▷ Q.obj N)

instance (N : C₂) : IsIso (unitExternalMap P Q N) := by
  rw [unitExternalMap]
  infer_instance

/-- **The external Hom pairing at the unit**: through `M ≅ RHom(𝟙, M)` and `Q N ≅ 𝟙 ⊠ N`, the
external Hom pairing for `(E₁, L₁) = (𝟙, M)` and `(E₂, L₂) = (N, W)` is the braiding moving
`Q N` past `P M`, the monoidal structure of `Q` and the evaluation `N ⊗ RHom(N, W) ⟶ W`; that is,
the following diagram commutes, with `H = RHom(N, W)`:
```
Q N ⊗ (P M ⊗ Q H) ───── braid ─────▶ P M ⊗ (Q N ⊗ Q H) ── μ, ev ──▶ P M ⊗ Q W
        │                                                             ▲
        │ M ≅ RHom(𝟙, M), Q N ≅ P 𝟙 ⊗ Q N                              │ pairing
        ▼                                                             │
(P 𝟙 ⊗ Q N) ⊗ (P RHom(𝟙, M) ⊗ Q H) ───────────────────────────────────┘
```
-/
@[reassoc]
lemma externalHomPairing_unit (M : C₁) (N W : C₂) :
    Q.obj N ◁ (P.map (unitNatIso.hom.app M) ▷ Q.obj ((ihom N).obj W)) ≫
        unitExternalMap P Q N ▷ _ ≫ externalHomPairing P Q (𝟙_ C₁) M N W =
      (α_ _ _ _).inv ≫ (β_ (Q.obj N) (P.obj M)).hom ▷ _ ≫ (α_ _ _ _).hom ≫
        P.obj M ◁ μ Q N ((ihom N).obj W) ≫ P.obj M ◁ Q.map ((ihom.ev N).app W) := by
  -- the factor `P` collapses to the left unitor of `P M`
  have hP : (ε P ⊗ₘ P.map (unitNatIso.hom.app M)) ≫ μ P (𝟙_ C₁) ((ihom (𝟙_ C₁)).obj M) ≫
      P.map ((ihom.ev (𝟙_ C₁)).app M) = (λ_ (P.obj M)).hom := by
    rw [tensorHom_def, Category.assoc, μ_natural_right_assoc, ← P.map_comp,
      whiskerLeft_unitNatIso_hom_app_ihom_ev_app, left_unitality]
    rfl
  -- move `ε` and `P (M ≅ RHom(𝟙, M))` through the interchange
  have h₂ := tensorμ_natural (ε P) (𝟙 (Q.obj N)) (P.map (unitNatIso.hom.app M))
    (𝟙 (Q.obj ((ihom N).obj W)))
  simp only [tensorHom_id, id_whiskerRight, tensorHom_def (ε P ▷ Q.obj N)] at h₂
  dsimp only [Functor.id_obj] at h₂ ⊢
  rw [externalHomPairing, unitExternalMap, comp_whiskerRight, Category.assoc,
    whisker_exchange_assoc, whisker_exchange_assoc, reassoc_of% h₂,
    ← tensorHom_id (ε P ⊗ₘ P.map (unitNatIso.hom.app M)), tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom, Category.id_comp, Category.assoc, hP, tensorHom_def,
    leftUnitor_inv_whiskerRight_tensorμ_leftUnitor_assoc, MonoidalCategory.whiskerLeft_comp]

/-- **The Künneth–Verdier map is `RHom(1, α) ∘ β`** (abstract form of blueprint
`lemma-external-duality-trace-morphism` (iv)): the transpose of the braiding, the monoidal structure
of `Q`, the evaluation `N ⊗ RHom(N, W) ⟶ W` and a map `a : P M ⊗ Q W ⟶ Z` is, through
`M ≅ RHom(𝟙, M)` and `Q N ≅ 𝟙 ⊠ N`, the external Hom map for `(𝟙, M)` and `(N, W)` followed by
`RHom(1, a)`; that is, the following diagram commutes, where `κ` is the transpose of
`Q N ⊗ (P M ⊗ Q RHom(N, W)) ⟶ P M ⊗ Q W ⟶ Z` as in `externalHomPairing_unit`:
```
P M ⊗ Q RHom(N, W) ───────────── κ ─────────────▶ RHom(Q N, Z)
        │                                              ▲
        │ M ≅ RHom(𝟙, M)                               │ RHom(1, a)
        ▼                                              │
P RHom(𝟙, M) ⊗ Q RHom(N, W)                   RHom(Q N, P M ⊗ Q W)
        │                                              ▲
        │ β                                            │ Q N ≅ P 𝟙 ⊗ Q N
        ▼                                              │
RHom(P 𝟙 ⊗ Q N, P M ⊗ Q W) ────────────────────────────┘
```
-/
lemma curry_eq_externalHomMap_comp [MonoidalClosed C] (M : C₁) (N W : C₂) {Z : C}
    (a : P.obj M ⊗ Q.obj W ⟶ Z) :
    curry ((α_ _ _ _).inv ≫ (β_ (Q.obj N) (P.obj M)).hom ▷ _ ≫ (α_ _ _ _).hom ≫
        P.obj M ◁ μ Q N ((ihom N).obj W) ≫ P.obj M ◁ Q.map ((ihom.ev N).app W) ≫ a) =
      (P.map (unitNatIso.hom.app M) ▷ _ ≫ externalHomMap P Q (𝟙_ C₁) M N W ≫
        (pre (unitExternalMap P Q N)).app _) ≫ (ihom _).map a := by
  refine (curry_eq_iff _ _).2 ?_
  rw [uncurry_natural_right, uncurry_natural_left, uncurry_pre_app, externalHomMap,
    uncurry_curry, ← externalHomPairing_unit_assoc]
  simp only [Category.assoc]

end CategoryTheory
