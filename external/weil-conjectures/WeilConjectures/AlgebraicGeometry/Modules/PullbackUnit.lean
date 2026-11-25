/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import Mathlib.Tactic.IrreducibleDef

/-!
# The unit of the pullback-pushforward adjunction on sections

For a morphism of schemes `f : Y ⟶ X` and an `𝒪_X`-module `M`, the unit of the adjunction
`f^* ⊣ f_*` gives maps `Γ(M, U) ⟶ Γ(f^* M, f ⁻¹ᵁ U)`. We record how these maps behave under
composition of morphisms and under restriction along open immersions, and that morphisms out of
`f^* M` are determined by their values on the image of these maps.

## Implementation details

`AlgebraicGeometry.modulesPseudofunctor` keeps only the pullback part of
`AlgebraicGeometry.Scheme.Modules.pseudofunctor`, which is the shape required by
`CategoryTheory.Pseudofunctor.DescentData`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite CategoryTheory.Bicategory
  CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y Z : Scheme.{u}}

/-- The unit of `pullback f ⊣ pushforward f`, on sections. -/
noncomputable abbrev pullbackUnit (f : Y ⟶ X) (M : X.Modules) :
    M ⟶ (pushforward f).obj ((pullback f).obj M) :=
  (pullbackPushforwardAdjunction f).unit.app M

/-- The unit of `pullback f ⊣ pushforward f` on sections over `U`, with its codomain written as
sections of `f^* M`. -/
noncomputable abbrev pullbackUnitApp (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    Γ(M, U) ⟶ Γ((pullback f).obj M, f ⁻¹ᵁ U) :=
  (pullbackUnit f M).app U

set_option backward.isDefEq.respectTransparency.types false in
/-- The units of the pullback-pushforward adjunctions compose, up to `pullbackComp`:

```
  Γ(M, U) ───── η_f ─────▶ Γ(f^* M, f⁻¹ U)
     │                            │
  η_(g ≫ f)                      η_g
     ▼                            ▼
  Γ((g ≫ f)^* M, ⋯) ──(pullbackComp g f).inv──▶ Γ(g^* f^* M, g⁻¹ f⁻¹ U)
``` -/
lemma pullbackUnit_comp_app (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens) :
    (pullbackUnit (g ≫ f) M).app U ≫ ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) =
      (pullbackUnit f M).app U ≫ (pullbackUnit g ((pullback f).obj M)).app (f ⁻¹ᵁ U) := by
  have h := unit_conjugateEquiv ((pullbackPushforwardAdjunction f).comp
    (pullbackPushforwardAdjunction g)) (pullbackPushforwardAdjunction (g ≫ f))
    (pullbackComp g f).inv M
  rw [conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have := congr_arg (fun φ ↦ Hom.app φ U) h
  simpa using this.symm

lemma pullbackUnit_comp_app_apply (g : Z ⟶ Y) (f : Y ⟶ X) (M : X.Modules) (U : X.Opens)
    (m : Γ(M, U)) :
    ((pullbackComp g f).inv.app M).app ((g ≫ f) ⁻¹ᵁ U) ((pullbackUnit (g ≫ f) M).app U m) =
      (pullbackUnit g ((pullback f).obj M)).app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m) :=
  congr($(pullbackUnit_comp_app g f M U) m)

/-- Naturality of the unit on sections. -/
lemma pullbackUnit_naturality_apply (f : Y ⟶ X) {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (m : Γ(M, U)) :
    ((pullback f).map φ).app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m) =
      (pullbackUnit f N).app U (φ.app U m) :=
  congr($(((pullbackPushforwardAdjunction f).unit.naturality φ).symm).app U m)

/-- Two morphisms out of `f^* M` agree if they agree on the image of the unit. -/
lemma pullback_hom_ext (f : Y ⟶ X) {M : X.Modules} {P : Y.Modules}
    {φ ψ : (pullback f).obj M ⟶ P}
    (h : ∀ (U : X.Opens) (m : Γ(M, U)),
      φ.app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m) = ψ.app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m)) :
    φ = ψ := by
  apply ((pullbackPushforwardAdjunction f).homEquiv _ _).injective
  ext U m
  simp only [Adjunction.homEquiv_unit, Hom.comp_app, pushforward_map_app]
  exact h U m

section OpenImmersion

variable (j : Y ⟶ X) [IsOpenImmersion j]

set_option backward.isDefEq.respectTransparency.types false in
/-- Along an open immersion, the unit of the pullback-pushforward adjunction is the unit of the
restriction adjunction followed by the comparison `restrictFunctorIsoPullback`. -/
lemma pullbackUnit_eq_of_isOpenImmersion (M : X.Modules) :
    pullbackUnit j M = (restrictAdjunction j).unit.app M ≫
      (pushforward j).map ((restrictFunctorIsoPullback j).hom.app M) :=
  ((restrictAdjunction j).unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction j) M).symm

/-- Along an open immersion, the unit of the pullback-pushforward adjunction is bijective on
sections over opens contained in the range. -/
lemma bijective_pullbackUnit_app_of_isOpenImmersion (M : X.Modules) {U : X.Opens}
    (hU : U ≤ j.opensRange) : Function.Bijective ((pullbackUnit j M).app U) := by
  rw [pullbackUnit_eq_of_isOpenImmersion, Hom.comp_app, restrictAdjunction_unit_app_app]
  have : j ''ᵁ (j ⁻¹ᵁ U) = U := le_antisymm (j.image_preimage_le U) (by
    intro x hx
    obtain ⟨y, rfl⟩ := hU hx
    exact ⟨y, hx, rfl⟩)
  have : IsIso (homOfLE (j.image_preimage_le U)) :=
    ⟨homOfLE (by rw [this]), Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  exact (ConcreteCategory.bijective_of_isIso
    (((pushforward j).map ((restrictFunctorIsoPullback j).hom.app M)).app U)).comp
    (ConcreteCategory.bijective_of_isIso (M.presheaf.map (homOfLE (j.image_preimage_le U)).op))

end OpenImmersion

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open Scheme.Modules

/-- The pseudofunctor sending a scheme `X` to its category `X.Modules` of sheaves of
modules and a morphism to the pullback functor. -/
noncomputable abbrev modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat :=
  Scheme.Modules.pseudofunctor.comp Adj.forget₁

variable {X Y Z : Scheme.{u}}

lemma modulesPseudofunctor_mapComp_hom_app (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules) :
    (modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app M =
      (pullbackComp g f).inv.app M :=
  rfl

lemma modulesPseudofunctor_mapComp_inv_app (f : Y ⟶ X) (g : Z ⟶ Y) (M : X.Modules) :
    (modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app M =
      (pullbackComp g f).hom.app M :=
  rfl

/-- The comparison `mapComp'` of `modulesPseudofunctor` on the image of the unit:

```
  Γ((g ≫ f)^* M) ─── mapComp'.hom ───▶ Γ(g^* f^* M)
        ▲                                   ▲
   η_(g ≫ f)                               η_g
        │                                   │
     Γ(M) ─────────────── η_f ─────────▶ Γ(f^* M)
``` -/
lemma modulesPseudofunctor_mapComp'_hom_app_pullbackUnit (f : Y ⟶ X) (g : Z ⟶ Y)
    (M : X.Modules) (U : X.Opens) (m : Γ(M, U)) :
    ((modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc).hom.toNatTrans.app
      M).app ((g ≫ f) ⁻¹ᵁ U) ((pullbackUnit (g ≫ f) M).app U m) =
      (pullbackUnit g ((pullback f).obj M)).app (f ⁻¹ᵁ U) ((pullbackUnit f M).app U m) := by
  have : modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc =
      modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  rw [this, modulesPseudofunctor_mapComp_hom_app]
  exact pullbackUnit_comp_app_apply g f M U m

/-- `pullHom` of `modulesPseudofunctor` in terms of `pullbackComp`. -/
lemma modulesPseudofunctor_pullHom_eq {X₁ X₂ Y Y' : Scheme.{u}} {M₁ : X₁.Modules}
    {M₂ : X₂.Modules} {f₁ : Y ⟶ X₁} {f₂ : Y ⟶ X₂}
    (φ : (pullback f₁).obj M₁ ⟶ (pullback f₂).obj M₂) (g : Y' ⟶ Y) :
    pullHom (F := modulesPseudofunctor) φ g (g ≫ f₁) (g ≫ f₂) =
      (pullbackComp g f₁).inv.app M₁ ≫ (pullback g).map φ ≫ (pullbackComp g f₂).hom.app M₂ := by
  have h₁ : modulesPseudofunctor.mapComp' f₁.op.toLoc g.op.toLoc (g ≫ f₁).op.toLoc =
      modulesPseudofunctor.mapComp f₁.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  have h₂ : modulesPseudofunctor.mapComp' f₂.op.toLoc g.op.toLoc (g ≫ f₂).op.toLoc =
      modulesPseudofunctor.mapComp f₂.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  dsimp only [pullHom]
  rw [h₁, h₂]
  rfl

/-- The comparison `mapComp'` of `modulesPseudofunctor` on global sections in the image of the
unit, for a factorization `g ≫ f = fg`: the square of the previous lemma with `g ≫ f`
replaced by `fg`. -/
lemma modulesPseudofunctor_mapComp'_hom_app_top (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) (m : Γ(M, ⊤)) :
    ((modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app M).app ⊤ (pullbackUnitApp fg M ⊤ m) =
      pullbackUnitApp g ((pullback f).obj M) ⊤ (pullbackUnitApp f M ⊤ m) := by
  subst h
  exact modulesPseudofunctor_mapComp'_hom_app_pullbackUnit f g M ⊤ m

/-- The comparison `mapComp'` of `modulesPseudofunctor` on global sections in the image of the
unit, for a factorization `g ≫ f = fg`, inverse direction. -/
lemma modulesPseudofunctor_mapComp'_inv_app_top (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) (m : Γ(M, ⊤)) :
    ((modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app M).app ⊤
        (pullbackUnitApp g ((pullback f).obj M) ⊤ (pullbackUnitApp f M ⊤ m)) =
      pullbackUnitApp fg M ⊤ m := by
  rw [← modulesPseudofunctor_mapComp'_hom_app_top f g fg h M m]
  have k := Cat.Hom.hom_inv_id_toNatTrans_app (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc
    fg.op.toLoc (by rw [← h]; rfl)) M
  exact congr(Hom.app (X := Z) $k ⊤ (pullbackUnitApp fg M ⊤ m))

/-- `pullbackComp` followed by `pullbackCongr`, for a factorization `g ≫ f = fg`:

```
  g^* f^* M ──(pullbackComp g f).app M──▶ (g ≫ f)^* M ──(pullbackCongr h).app M──▶ fg^* M
``` -/
noncomputable def pullbackCompOfEq (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X) (h : g ≫ f = fg)
    (M : X.Modules) : (pullback g).obj ((pullback f).obj M) ≅ (pullback fg).obj M :=
  (pullbackComp g f).app M ≪≫ (pullbackCongr h).app M

/-- The inverse comparison `mapComp'` of `modulesPseudofunctor` is `pullbackCompOfEq`:
`(mapComp' f g fg).inv.app M = (pullbackCompOfEq g f fg h M).hom : g^* f^* M ⟶ fg^* M`. -/
lemma modulesPseudofunctor_mapComp'_inv_app_eq (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) :
    (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← h]; rfl)).inv.toNatTrans.app M = (pullbackCompOfEq g f fg h M).hom := by
  subst h
  have : modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc =
      modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  rw [this, modulesPseudofunctor_mapComp_inv_app]
  simp [pullbackCompOfEq, pullbackCongr]

/-- The comparison `mapComp'` of `modulesPseudofunctor` is the inverse of `pullbackCompOfEq`:
`(mapComp' f g fg).hom.app M = (pullbackCompOfEq g f fg h M).inv : fg^* M ⟶ g^* f^* M`. -/
lemma modulesPseudofunctor_mapComp'_hom_app_eq (f : Y ⟶ X) (g : Z ⟶ Y) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) :
    (modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc fg.op.toLoc
      (by rw [← h]; rfl)).hom.toNatTrans.app M = (pullbackCompOfEq g f fg h M).inv := by
  subst h
  have : modulesPseudofunctor.mapComp' f.op.toLoc g.op.toLoc (g ≫ f).op.toLoc =
      modulesPseudofunctor.mapComp f.op.toLoc g.op.toLoc :=
    Pseudofunctor.mapComp'_eq_mapComp _ _ _
  rw [this, modulesPseudofunctor_mapComp_hom_app]
  simp [pullbackCompOfEq, pullbackCongr]

/-- `pullbackCompOfEq` on global sections in the image of the units:

```
  Γ(M) ──η_f──▶ Γ(f^* M) ──η_g──▶ Γ(g^* f^* M) ──pullbackCompOfEq──▶ Γ(fg^* M)
     └─────────────────────────── η_fg ──────────────────────────────────┘
``` -/
lemma pullbackCompOfEq_hom_app_top (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X) (h : g ≫ f = fg)
    (M : X.Modules) (m : Γ(M, ⊤)) :
    ((pullbackCompOfEq g f fg h M).hom).app ⊤
      (pullbackUnitApp g ((pullback f).obj M) ⊤ (pullbackUnitApp f M ⊤ m)) =
      pullbackUnitApp fg M ⊤ m := by
  rw [← modulesPseudofunctor_mapComp'_inv_app_eq f g fg h]
  exact modulesPseudofunctor_mapComp'_inv_app_top f g fg h M m

/-- The unit of `pullback f ⊣ pushforward f` on global sections. (This is irreducible: unfolding
it forces the kernel to identify `f ⁻¹ᵁ ⊤` with `⊤`, which is expensive for concrete `f`.) -/
noncomputable irreducible_def pullbackΓ (f : Y ⟶ X) (M : X.Modules) :
    Γ(M, ⊤) ⟶ Γ((pullback f).obj M, ⊤) :=
  (pullbackUnit f M).app ⊤

/-- `pullbackΓ` is the unit on sections over `⊤`. -/
lemma pullbackΓ_apply (f : Y ⟶ X) (M : X.Modules) (m : Γ(M, ⊤)) :
    pullbackΓ f M m = pullbackUnitApp f M ⊤ m := by
  rw [pullbackΓ_def]
  rfl

/-- Naturality of `pullbackΓ`: `(f^* φ) (η_f m) = η_f (φ m)`. -/
lemma pullbackΓ_naturality (f : Y ⟶ X) {M N : X.Modules} (φ : M ⟶ N) (m : Γ(M, ⊤)) :
    ((pullback f).map φ).app ⊤ (pullbackΓ f M m) = pullbackΓ f N (φ.app ⊤ m) := by
  rw [pullbackΓ_apply, pullbackΓ_apply]
  exact pullbackUnit_naturality_apply f φ ⊤ m

/-- `pullbackCompOfEq` on global sections in the image of the units, in terms of `pullbackΓ`:
`pullbackCompOfEq (η_g (η_f m)) = η_fg m`. -/
lemma pullbackCompOfEq_hom_app_pullbackΓ (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) (m : Γ(M, ⊤)) :
    ((pullbackCompOfEq g f fg h M).hom).app ⊤ (pullbackΓ g _ (pullbackΓ f M m)) =
      pullbackΓ fg M m := by
  rw [pullbackΓ_apply, pullbackΓ_apply, pullbackΓ_apply]
  exact pullbackCompOfEq_hom_app_top g f fg h M m

/-- The inverse of `pullbackCompOfEq` on global sections in the image of the units:
`(pullbackCompOfEq)⁻¹ (η_fg m) = η_g (η_f m)`. -/
lemma pullbackCompOfEq_inv_app_pullbackΓ (g : Z ⟶ Y) (f : Y ⟶ X) (fg : Z ⟶ X)
    (h : g ≫ f = fg) (M : X.Modules) (m : Γ(M, ⊤)) :
    ((pullbackCompOfEq g f fg h M).inv).app ⊤ (pullbackΓ fg M m) =
      pullbackΓ g _ (pullbackΓ f M m) := by
  rw [← pullbackCompOfEq_hom_app_pullbackΓ g f fg h M m]
  exact congr($((pullbackCompOfEq g f fg h M).hom_inv_id).app ⊤ _)

end AlgebraicGeometry
