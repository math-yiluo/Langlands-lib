/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided

/-!
# Weil equivariance of adjunction data and of duals

Let `G : C ⥤ C` be an endofunctor; in the `ℓ`-adic formalism `C = D(X, Λ)` and `G = Lg^*` is the
pullback along the geometric Frobenius `g` of `X`. A *Weil datum* on an object `M` is a morphism
`φ : G M ⟶ M`, and `u : M ⟶ N` is *equivariant* for data `φ_M`, `φ_N` if
`G u ≫ φ_N = φ_M ≫ u`. This file proves two formal equivariance statements of blueprint
`prose-10-20`.

**Adjunction data.** Let `L ⊣ R` be adjunctions `C ⇄ D` and `E ⇄ F` (`L₁ ⊣ R₁`, `L₂ ⊣ R₂`), and
let `e : L₁ ⋙ H ≅ G ⋙ L₂` be an isomorphism (in the geometric case the compact-support base
change `Ex_! : Lh^* Rf_! ≅ Rf_! Lg^*`). Its *right adjoint exchange* is the mate
`R₁ ⋙ G ⟶ H ⋙ R₂` of `e⁻¹` (`CategoryTheory.Adjunction.rightAdjointExchange`). Transporting
Weil data through `L` by `e` and through `R` by the right adjoint exchange, the unit and the
counit of the adjunction are equivariant
(`CategoryTheory.Adjunction.isWeilEquivariant_counit`,
`CategoryTheory.Adjunction.isWeilEquivariant_unit`).

**Duals.** Let `C` be monoidal closed and `G` a monoidal endofunctor. A Weil datum `φ_ω` on an
object `ω` and an invertible Weil datum `φ_A` on `A` give the *dual Weil datum* on `[A, ω]`
(`CategoryTheory.MonoidalClosed.dualWeilDatum`), the tensor-hom adjoint of
```
A ⊗ G [A, ω] ──φ_A⁻¹ ⊗ 1──▶ G A ⊗ G [A, ω] ──μ──▶ G (A ⊗ [A, ω]) ──G ev──▶ G ω ──φ_ω──▶ ω;
```
for an autoequivalence `G` it is `G [A, ω] ≅ [G A, G ω] ──[G A, φ_ω]──▶ [G A, ω] ──[φ_A⁻¹, ω]──▶
[A, ω]`, the first map being the internal-hom comparison of `G`. The evaluation
`A ⊗ [A, ω] ⟶ ω` is equivariant (`CategoryTheory.MonoidalClosed.isWeilEquivariant_ev`), and the
tensor-hom adjoint
`B ⟶ [A, ω]` of an equivariant pairing `A ⊗ B ⟶ ω` is equivariant
(`CategoryTheory.MonoidalClosed.isWeilEquivariant_curry`). No integral lattice of `φ_A` is
needed: the construction only uses `φ_A` and its inverse.

**Biduality.** If moreover `C` is braided and `G` is a braided functor, the braiding is
equivariant (`CategoryTheory.MonoidalClosed.isWeilEquivariant_braiding`), and so is the
double-dual map `A ⟶ [[A, ω], ω]` for `φ_A` and the dual of the dual Weil datum, provided the
dual Weil datum is invertible (`CategoryTheory.MonoidalClosed.isWeilEquivariant_toIhomIhom`).
-/

@[expose] public section

namespace CategoryTheory

open Category MonoidalCategory CategoryTheory.Functor

/-- A morphism `u : M ⟶ N` is *equivariant* for Weil data `φ_M : G M ⟶ M` and `φ_N : G N ⟶ N`
if `G u ≫ φ_N = φ_M ≫ u`. -/
def IsWeilEquivariant {C : Type*} [Category* C] (G : C ⥤ C) {M N : C} (φM : G.obj M ⟶ M)
    (φN : G.obj N ⟶ N) (u : M ⟶ N) : Prop :=
  G.map u ≫ φN = φM ≫ u

section Transport

variable {C D : Type*} [Category* C] [Category* D] {G : C ⥤ C} {G' : D ⥤ D} (T : C ⥤ D)
  (c : G ⋙ T ≅ T ⋙ G')

/-- The Weil datum `G' T M ──c⁻¹──▶ T G M ──T φ──▶ T M` on `T M` transported from a datum
`φ : G M ⟶ M` along a functor `T` commuting with the Weil functors, `c : G ⋙ T ≅ T ⋙ G'` (for
instance a change of coefficients, or a pullback along a Frobenius-compatible morphism). -/
noncomputable def transportWeilDatum {M : C} (φ : G.obj M ⟶ M) : G'.obj (T.obj M) ⟶ T.obj M :=
  c.inv.app M ≫ T.map φ

/-- A functor commuting with the Weil functors carries equivariant morphisms to equivariant
morphisms, for the transported data. -/
lemma IsWeilEquivariant.map {M N : C} {φM : G.obj M ⟶ M} {φN : G.obj N ⟶ N} {u : M ⟶ N}
    (hu : IsWeilEquivariant G φM φN u) :
    IsWeilEquivariant G' (transportWeilDatum T c φM) (transportWeilDatum T c φN) (T.map u) := by
  have h := c.inv.naturality u
  dsimp at h
  rw [IsWeilEquivariant, transportWeilDatum, transportWeilDatum, reassoc_of% h,
    ← Functor.map_comp, hu, Functor.map_comp, Category.assoc]

/-- Equivariant morphisms compose. -/
lemma IsWeilEquivariant.comp {M N P : C} {φM : G.obj M ⟶ M} {φN : G.obj N ⟶ N}
    {φP : G.obj P ⟶ P} {u : M ⟶ N} {v : N ⟶ P} (hu : IsWeilEquivariant G φM φN u)
    (hv : IsWeilEquivariant G φN φP v) : IsWeilEquivariant G φM φP (u ≫ v) := by
  rw [IsWeilEquivariant, Functor.map_comp, Category.assoc, hv, reassoc_of% hu]

end Transport

namespace Adjunction

section Mate

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  {G : C ⥤ E} {H : D ⥤ F} (e : L₁ ⋙ H ≅ G ⋙ L₂)

/-- The *right adjoint exchange* `R₁ ⋙ G ⟶ H ⋙ R₂` of an isomorphism `e : L₁ ⋙ H ≅ G ⋙ L₂`
between adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂`: the mate of `e⁻¹`. For the compact-support base
change `Ex_! : Lh^* Rf_! ≅ Rf'_! Lg^*` it is the exceptional base change
`Lg^* Rf^! ⟶ Rf'^! Lh^*`. -/
noncomputable def rightAdjointExchange : R₁ ⋙ G ⟶ H ⋙ R₂ :=
  (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv))

/-- The right adjoint exchange is characterised by its compatibility with the counits:
```
H L₁ R₁ d ──e──▶ L₂ G R₁ d ──L₂ (exchange)──▶ L₂ R₂ H d ──ε₂──▶ H d
```
is `H ε₁`. -/
@[reassoc]
lemma hom_app_comp_map_rightAdjointExchange_app_comp_counit (d : D) :
    e.hom.app (R₁.obj d) ≫ L₂.map ((rightAdjointExchange adj₁ adj₂ e).app d) ≫
        adj₂.counit.app (H.obj d) = H.map (adj₁.counit.app d) := by
  have h := mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv) d
  calc e.hom.app (R₁.obj d) ≫ L₂.map ((rightAdjointExchange adj₁ adj₂ e).app d) ≫
        adj₂.counit.app (H.obj d)
      = e.hom.app (R₁.obj d) ≫ e.inv.app (R₁.obj d) ≫ H.map (adj₁.counit.app d) :=
        congrArg (e.hom.app (R₁.obj d) ≫ ·) h
    _ = H.map (adj₁.counit.app d) := by simp

/-- The right adjoint exchange is compatible with the units:
`G η₁ ≫ (exchange)_{L₁ c} = η₂ ≫ R₂ (e⁻¹)`. -/
@[reassoc]
lemma map_unit_app_comp_rightAdjointExchange_app (c : C) :
    G.map (adj₁.unit.app c) ≫ (rightAdjointExchange adj₁ adj₂ e).app (L₁.obj c) =
      adj₂.unit.app (G.obj c) ≫ R₂.map (e.inv.app c) :=
  unit_mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ e.inv) c

end Mate

section Weil

variable {C D : Type*} [Category* C] [Category* D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  {G : C ⥤ C} {H : D ⥤ D} (e : L ⋙ H ≅ G ⋙ L)

/-- The Weil datum `H L c ──e──▶ L G c ──L φ──▶ L c` on `L c` transported from a datum
`φ : G c ⟶ c` along `e : L ⋙ H ≅ G ⋙ L` (for `L = Rf_!` and `e = Ex_!` this is the
compact-support transport). -/
noncomputable def leftWeilDatum {c : C} (φ : G.obj c ⟶ c) : H.obj (L.obj c) ⟶ L.obj c :=
  e.hom.app c ≫ L.map φ

/-- The Weil datum `G R d ──exchange──▶ R H d ──R ψ──▶ R d` on `R d` transported from a datum
`ψ : H d ⟶ d` along the right adjoint exchange of `e`. -/
noncomputable def rightWeilDatum {d : D} (ψ : H.obj d ⟶ d) : G.obj (R.obj d) ⟶ R.obj d :=
  (rightAdjointExchange adj adj e).app d ≫ R.map ψ

/-- **The counit is Weil equivariant**: for a Weil datum `ψ` on `d`, the counit
`L R d ⟶ d` is equivariant for the transported datum on `L R d` and `ψ`. -/
lemma isWeilEquivariant_counit {d : D} (ψ : H.obj d ⟶ d) :
    IsWeilEquivariant H (leftWeilDatum e (rightWeilDatum adj e ψ)) ψ (adj.counit.app d) := by
  have h := adj.counit.naturality ψ
  dsimp at h
  rw [IsWeilEquivariant, leftWeilDatum, rightWeilDatum, Functor.map_comp, Category.assoc,
    Category.assoc, h,
    hom_app_comp_map_rightAdjointExchange_app_comp_counit_assoc]

/-- **The unit is Weil equivariant**: for a Weil datum `φ` on `c`, the unit `c ⟶ R L c` is
equivariant for `φ` and the transported datum on `R L c`. -/
lemma isWeilEquivariant_unit {c : C} (φ : G.obj c ⟶ c) :
    IsWeilEquivariant G φ (rightWeilDatum adj e (leftWeilDatum e φ)) (adj.unit.app c) := by
  have h := adj.unit.naturality φ
  dsimp at h
  rw [IsWeilEquivariant, rightWeilDatum, leftWeilDatum,
    map_unit_app_comp_rightAdjointExchange_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app_assoc, h]

end Weil

end Adjunction

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [MonoidalClosed C] (G : C ⥤ C)
  [G.Monoidal]

/-- The *dual Weil datum* on `[A, ω]` of an invertible Weil datum `φ_A : G A ≅ A` and a Weil
datum `φ_ω : G ω ⟶ ω`: the tensor-hom adjoint of
```
A ⊗ G [A, ω] ──φ_A⁻¹ ⊗ 1──▶ G A ⊗ G [A, ω] ──μ──▶ G (A ⊗ [A, ω]) ──G ev──▶ G ω ──φ_ω──▶ ω.
```
When `G` is an equivalence this is `G [A, ω] ≅ [G A, G ω] ⟶ [G A, ω] ⟶ [A, ω]`, the first map
being the internal-hom comparison of `G`. -/
noncomputable def dualWeilDatum {A ω : C} (φA : G.obj A ≅ A) (φω : G.obj ω ⟶ ω) :
    G.obj ((ihom A).obj ω) ⟶ (ihom A).obj ω :=
  curry (φA.inv ▷ G.obj ((ihom A).obj ω) ≫ LaxMonoidal.μ G A ((ihom A).obj ω) ≫
    G.map ((ihom.ev A).app ω) ≫ φω)

/-- The tensor product `G (A ⊗ B) ≅ G A ⊗ G B ──φ_A ⊗ φ_B──▶ A ⊗ B` of two Weil data. -/
noncomputable def tensorWeilDatum {A B : C} (φA : G.obj A ⟶ A) (φB : G.obj B ⟶ B) :
    G.obj (A ⊗ B) ⟶ A ⊗ B :=
  OplaxMonoidal.δ G A B ≫ φA ▷ G.obj B ≫ A ◁ φB

/-- **Evaluation is Weil equivariant**: `A ⊗ [A, ω] ⟶ ω` is equivariant for the tensor product of
`φ_A` with the dual Weil datum, and `φ_ω`. -/
lemma isWeilEquivariant_ev {A ω : C} (φA : G.obj A ≅ A) (φω : G.obj ω ⟶ ω) :
    IsWeilEquivariant G (tensorWeilDatum G φA.hom (dualWeilDatum G φA φω))
      φω ((ihom.ev A).app ω) := by
  rw [IsWeilEquivariant, tensorWeilDatum, dualWeilDatum]
  simp only [Category.assoc, whiskerLeft_curry_ihom_ev_app, hom_inv_whiskerRight_assoc,
    Monoidal.δ_μ_assoc]

/-- **The adjoint of a Weil pairing is Weil equivariant**: if `b : A ⊗ B ⟶ ω` is equivariant for
`φ_A ⊗ φ_B` and `φ_ω`, then its tensor-hom adjoint `B ⟶ [A, ω]` is equivariant for `φ_B` and
the dual Weil datum. -/
lemma isWeilEquivariant_curry {A B ω : C} (φA : G.obj A ≅ A) (φB : G.obj B ⟶ B)
    (φω : G.obj ω ⟶ ω) {b : A ⊗ B ⟶ ω}
    (hb : IsWeilEquivariant G (tensorWeilDatum G φA.hom φB) φω b) :
    IsWeilEquivariant G φB (dualWeilDatum G φA φω) (curry b) := by
  rw [IsWeilEquivariant, tensorWeilDatum] at hb
  rw [IsWeilEquivariant]
  apply uncurry_injective
  rw [uncurry_eq, uncurry_eq, MonoidalCategory.whiskerLeft_comp, Category.assoc, dualWeilDatum,
    whiskerLeft_curry_ihom_ev_app, whisker_exchange_assoc, LaxMonoidal.μ_natural_right_assoc,
    ← Functor.map_comp_assoc, whiskerLeft_curry_ihom_ev_app, hb]
  simp only [Category.assoc, MonoidalCategory.whiskerLeft_comp, whiskerLeft_curry_ihom_ev_app,
    Monoidal.μ_δ_assoc, inv_hom_whiskerRight_assoc]

/-- The dual Weil datum is the composite
`G [A, ω] ──comparison──▶ [G A, G ω] ──[G A, φ_ω]──▶ [G A, ω] ──[φ_A⁻¹, ω]──▶ [A, ω]`, the first
map being the internal-hom comparison of `G` (`CategoryTheory.Functor.LaxMonoidal.ihomComparison`).
-/
lemma dualWeilDatum_eq {A ω : C} (φA : G.obj A ≅ A) (φω : G.obj ω ⟶ ω) :
    dualWeilDatum G φA φω = (LaxMonoidal.ihomComparison G A).app ω ≫
      (ihom (G.obj A)).map φω ≫ (pre φA.inv).app ω := by
  apply uncurry_injective
  rw [dualWeilDatum, uncurry_curry]
  conv_rhs => rw [← Category.assoc, uncurry_pre_app, uncurry_natural_right,
    LaxMonoidal.ihomComparison_app_eq_curry, uncurry_curry]
  simp only [Category.assoc]

/-- For a monoidal autoequivalence `G` and an invertible Weil datum `φ_ω`, the dual Weil datum is
invertible: the internal-hom comparison of a monoidal equivalence is an isomorphism
(`CategoryTheory.isIso_mateEquiv_of_isEquivalence`). -/
instance isIso_dualWeilDatum [G.IsEquivalence] {A ω : C} (φA : G.obj A ≅ A) (φω : G.obj ω ⟶ ω)
    [IsIso φω] : IsIso (dualWeilDatum G φA φω) := by
  have : IsIso (LaxMonoidal.μTwoSquare G A) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro X
    dsimp [LaxMonoidal.μTwoSquare]
    infer_instance
  have := isIso_mateEquiv_of_isEquivalence (ihom.adjunction A) (ihom.adjunction (G.obj A))
    (LaxMonoidal.μTwoSquare G A)
  rw [dualWeilDatum_eq]
  change IsIso ((LaxMonoidal.ihomComparison G A).app ω ≫ _ ≫ _)
  infer_instance

end MonoidalClosed

namespace MonoidalClosed

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] (G : C ⥤ C)
  [G.Braided]

/-- **The braiding is Weil equivariant** for a braided functor `G`: `A ⊗ B ⟶ B ⊗ A` is
equivariant for the tensor products `φ_A ⊗ φ_B` and `φ_B ⊗ φ_A`. -/
lemma isWeilEquivariant_braiding {A B : C} (φA : G.obj A ⟶ A) (φB : G.obj B ⟶ B) :
    IsWeilEquivariant G (tensorWeilDatum G φA φB) (tensorWeilDatum G φB φA) (β_ A B).hom := by
  rw [IsWeilEquivariant, tensorWeilDatum, tensorWeilDatum, Functor.map_braiding,
    Category.assoc, Category.assoc, Monoidal.μ_δ_assoc, ← whisker_exchange]
  simp only [Category.assoc, BraidedCategory.braiding_naturality_right,
    BraidedCategory.braiding_naturality_left_assoc]

/-- **Biduality is Weil equivariant** for a braided functor `G`: for an invertible Weil datum
`φ_A` on `A` and a Weil datum `φ_ω` on `ω` such that the dual Weil datum on `[A, ω]` is
invertible (given as `ψ`), the double-dual map `A ⟶ [[A, ω], ω]` is equivariant for `φ_A` and
the dual of the dual Weil datum. -/
lemma isWeilEquivariant_toIhomIhom [MonoidalClosed C] {A ω : C} (φA : G.obj A ≅ A)
    (φω : G.obj ω ⟶ ω) (ψ : G.obj ((ihom A).obj ω) ≅ (ihom A).obj ω)
    (hψ : ψ.hom = dualWeilDatum G φA φω) :
    IsWeilEquivariant G φA.hom (dualWeilDatum G ψ φω) (toIhomIhom ω A) := by
  refine isWeilEquivariant_curry G ψ φA.hom φω ?_
  have hev := isWeilEquivariant_ev G φA φω
  rw [← hψ] at hev
  exact (isWeilEquivariant_braiding G ψ.hom φA.hom).comp hev

end MonoidalClosed

end CategoryTheory
