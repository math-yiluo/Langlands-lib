/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Conjugate adjunction transfer of the projection tensor transpose

Source: blueprint, `lem-pur-co-smooth-etale-locality`, proof Step 1, serving
`proposition-compatibility-purity-composition--1`, proof Step 1, remaining co-projection factors
(blueprint: lem-pur-adjoint-projection-tensor-transfer).

The component formulas are definitions; the theorem includes their naturality so that
its componentwise equalities also identify the corresponding natural transformations.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe uC vC uD vD

open CategoryTheory MonoidalCategory CategoryTheory.Category
  CategoryTheory.BraidedCategory

namespace CategoryTheory
namespace AdjointProjectionTensorTransfer

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
  {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
  {F S : C ⥤ D} {G T : D ⥤ C}

/-- The map `q_K`, with `W = G(1)`, formed from the symmetry, inverse projection,
and the counit at the unit. Source: blueprint, etale normalization in
`lem-pur-co-smooth-etale-locality`, Step 1
(blueprint: lem-pur-adjoint-projection-tensor-transfer). -/
def q (aF : F ⊣ G) (T : D ⥤ C)
    (P : ∀ (M : C) (K : D), F.obj M ⊗ K ≅ F.obj (M ⊗ T.obj K)) (K : D) :
    F.obj (T.obj K ⊗ G.obj (𝟙_ D)) ⟶ K :=
  F.map (β_ (T.obj K) (G.obj (𝟙_ D))).hom ≫ (P (G.obj (𝟙_ D)) K).inv ≫
    (aF.counit.app (𝟙_ D) ⊗ₘ 𝟙 K) ≫ (λ_ K).hom

/-- The same projection expression after transfer to `S`, using
`e = ε_1 ∘ d_W⁻¹` in mathematical composition order, i.e. `d_W.inv ≫ ε_1` in Lean.
Source: blueprint, etale normalization in `lem-pur-co-smooth-etale-locality`, Step 1
(blueprint: lem-pur-adjoint-projection-tensor-transfer). -/
def transferredQ (aF : F ⊣ G) (T : D ⥤ C) (d : F ≅ S)
    (p : ∀ (M : C) (K : D), S.obj M ⊗ K ≅ S.obj (M ⊗ T.obj K)) (K : D) :
    S.obj (T.obj K ⊗ G.obj (𝟙_ D)) ⟶ K :=
  S.map (β_ (T.obj K) (G.obj (𝟙_ D))).hom ≫ (p (G.obj (𝟙_ D)) K).inv ≫
    ((d.inv.app (G.obj (𝟙_ D)) ≫ aF.counit.app (𝟙_ D)) ⊗ₘ 𝟙 K) ≫ (λ_ K).hom

/-- The map `h_K = r_TK ∘ (1_TK ⊗ η)`, where `η = u ∘ (d⁻¹)^c_1`.
Source: blueprint, etale normalization in `lem-pur-co-smooth-etale-locality`, Step 1
(blueprint: lem-pur-adjoint-projection-tensor-transfer). -/
def h (aF : F ⊣ G) (aS : S ⊣ T) (d : F ≅ S)
    (u : T.obj (𝟙_ D) ≅ 𝟙_ C) (K : D) : T.obj K ⊗ G.obj (𝟙_ D) ⟶ T.obj K :=
  (𝟙 (T.obj K) ⊗ₘ ((conjugateEquiv aF aS d.inv).app (𝟙_ D) ≫ u.hom)) ≫
    (ρ_ (T.obj K)).hom

end AdjointProjectionTensorTransfer

open AdjointProjectionTensorTransfer

/-- Conjugating `d⁻¹` transports the projection/counit transpose to tensoring with
`η`, naturally in `K`. Source: blueprint, `lem-pur-co-smooth-etale-locality`, proof
Step 1, serving `proposition-compatibility-purity-composition--1`, proof Step 1, co-projection
factors (blueprint: lem-pur-adjoint-projection-tensor-transfer).

Proof: (1) Apply `def-weil-pbc-adjunction-conjugate` to `d⁻¹`; its counit equation
and injectivity of the inverse `S ⊣ T` Hom bijection give the characterization and
uniqueness. (2) Expand the Hom transposes using the units; `unit_conjugateEquiv` and
naturality of the conjugate give the Hom-transpose identity.
(3) Naturality of `d` at the symmetry and the inverted projection square identify
`q_K ∘ d_N⁻¹` in mathematical order with `transferredQ` (Lean reverses that order).
(4) The counit characterization at the unit identifies the transferred counit with
`S(ρ_1)` followed by evaluation. Naturality of `p` in `M` moves `ρ_1` through its
inverse; the assumed evaluation equation at `T(1)` reduces the expression to
`S(a_K ∘ (ρ_1 ⊗ 1) ∘ σ)` followed by evaluation.
(5) Naturality of symmetry at `(1,η)` and `σ_TK,1 ≫ λ_TK = r_TK` identify this
inside map with `h_K`. These tensor manipulations use `def-sfb-monoidal-category`.
(6) Apply the Hom bijection of `def-weil-pbc-adjunction-mate` and the identity
from (2), yielding `τ_K ≫ ρ_K = h_K` in Lean's composition order.
(7) Naturality of symmetry, inverse projection and unitors proves naturality of
`q` and `h`; naturality of the Hom bijection gives that of `τ`. Naturality of
`d⁻¹` then gives that of the transferred expression. Thus all component equations
are equations of the natural transformations they define. -/
theorem adjointProjectionTensorTransfer
    {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [SymmetricCategory C]
    {D : Type uD} [Category.{vD} D] [MonoidalCategory D] [SymmetricCategory D]
    {F S : C ⥤ D} {G T : D ⥤ C}
    (aF : F ⊣ G) (aS : S ⊣ T) (d : F ≅ S) (u : T.obj (𝟙_ D) ≅ 𝟙_ C)
    (P : ∀ (M : C) (K : D), F.obj M ⊗ K ≅ F.obj (M ⊗ T.obj K))
    (p : ∀ (M : C) (K : D), S.obj M ⊗ K ≅ S.obj (M ⊗ T.obj K))
    (hP : ∀ (M M' : C) (K K' : D) (f : M ⟶ M') (g : K ⟶ K'),
      (F.map f ⊗ₘ g) ≫ (P M' K').hom =
        (P M K).hom ≫ F.map (f ⊗ₘ T.map g))
    (hp : ∀ (M M' : C) (K K' : D) (f : M ⟶ M') (g : K ⟶ K'),
      (S.map f ⊗ₘ g) ≫ (p M' K').hom =
        (p M K).hom ≫ S.map (f ⊗ₘ T.map g))
    (hd : ∀ (M : C) (K : D),
      (P M K).hom ≫ d.hom.app (M ⊗ T.obj K) =
        (d.hom.app M ⊗ₘ 𝟙 K) ≫ (p M K).hom)
    (hev : ∀ (K : D),
      (p (T.obj (𝟙_ D)) K).hom ≫
          S.map ((u.hom ⊗ₘ 𝟙 (T.obj K)) ≫ (λ_ (T.obj K)).hom) ≫ aS.counit.app K =
        (aS.counit.app (𝟙_ D) ⊗ₘ 𝟙 K) ≫ (λ_ K).hom) :
    IsIso (conjugateEquiv aF aS d.inv) ∧
    (∀ (K : D), d.hom.app (G.obj K) ≫
      S.map ((conjugateEquiv aF aS d.inv).app K) ≫ aS.counit.app K = aF.counit.app K) ∧
    (∀ (ρ : G ⟶ T),
      (∀ (K : D), d.hom.app (G.obj K) ≫ S.map (ρ.app K) ≫ aS.counit.app K =
        aF.counit.app K) → ρ = conjugateEquiv aF aS d.inv) ∧
    (∀ (N : C) (K : D) (b : F.obj N ⟶ K),
      aS.homEquiv N K (d.inv.app N ≫ b) =
        aF.homEquiv N K b ≫ (conjugateEquiv aF aS d.inv).app K) ∧
    (∀ (K : D),
      d.inv.app (T.obj K ⊗ G.obj (𝟙_ D)) ≫ AdjointProjectionTensorTransfer.q aF T P K =
        AdjointProjectionTensorTransfer.transferredQ aF T d p K) ∧
    (∀ (K : D), AdjointProjectionTensorTransfer.transferredQ aF T d p K =
      S.map (AdjointProjectionTensorTransfer.h aF aS d u K) ≫ aS.counit.app K) ∧
    (∀ (K : D),
      aF.homEquiv (T.obj K ⊗ G.obj (𝟙_ D)) K (AdjointProjectionTensorTransfer.q aF T P K) ≫
        (conjugateEquiv aF aS d.inv).app K =
          AdjointProjectionTensorTransfer.h aF aS d u K) ∧
    (∀ (K L : D) (f : K ⟶ L),
      F.map (T.map f ⊗ₘ 𝟙 (G.obj (𝟙_ D))) ≫ AdjointProjectionTensorTransfer.q aF T P L =
        AdjointProjectionTensorTransfer.q aF T P K ≫ f) ∧
    (∀ (K L : D) (f : K ⟶ L),
      (T.map f ⊗ₘ 𝟙 (G.obj (𝟙_ D))) ≫
          aF.homEquiv (T.obj L ⊗ G.obj (𝟙_ D)) L (AdjointProjectionTensorTransfer.q aF T P L) =
        aF.homEquiv (T.obj K ⊗ G.obj (𝟙_ D)) K (AdjointProjectionTensorTransfer.q aF T P K) ≫
          G.map f) ∧
    (∀ (K L : D) (f : K ⟶ L),
      (T.map f ⊗ₘ 𝟙 (G.obj (𝟙_ D))) ≫ AdjointProjectionTensorTransfer.h aF aS d u L =
        AdjointProjectionTensorTransfer.h aF aS d u K ≫ T.map f) ∧
    (∀ (K L : D) (f : K ⟶ L),
      S.map (T.map f ⊗ₘ 𝟙 (G.obj (𝟙_ D))) ≫ d.inv.app (T.obj L ⊗ G.obj (𝟙_ D)) ≫
          AdjointProjectionTensorTransfer.q aF T P L =
        d.inv.app (T.obj K ⊗ G.obj (𝟙_ D)) ≫ AdjointProjectionTensorTransfer.q aF T P K ≫ f) := by
  let R := conjugateEquiv aF aS d.inv
  have hc (K : D) : S.map (R.app K) ≫ aS.counit.app K =
      d.inv.app (G.obj K) ≫ aF.counit.app K :=
    conjugateEquiv_counit aF aS d.inv K
  have ht (N : C) (K : D) (b : F.obj N ⟶ K) :
      aS.homEquiv N K (d.inv.app N ≫ b) = aF.homEquiv N K b ≫ R.app K := by
    rw [Adjunction.homEquiv_unit, T.map_comp, ← Category.assoc,
      ← unit_conjugateEquiv aF aS d.inv N]
    change (aF.unit.app N ≫ R.app (F.obj N)) ≫ T.map b = _
    rw [Category.assoc, ← R.naturality b, ← Category.assoc, aF.homEquiv_unit]
  have hi (M M' : C) (K K' : D) (f : M ⟶ M') (g : K ⟶ K') :
      S.map (f ⊗ₘ T.map g) ≫ (p M' K').inv =
        (p M K).inv ≫ (S.map f ⊗ₘ g) := by
    apply (cancel_epi (p M K).hom).1
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
      Iso.hom_inv_id_assoc] using
      congrArg (fun z => z ≫ (p M' K').inv) (hp M M' K K' f g).symm
  have hd' (M : C) (K : D) :
      d.inv.app (M ⊗ T.obj K) ≫ (P M K).inv =
        (p M K).inv ≫ (d.inv.app M ⊗ₘ 𝟙 K) := by
    apply (cancel_epi (d.hom.app (M ⊗ T.obj K))).1
    apply (cancel_epi (P M K).hom).1
    simp only [← Category.assoc, d.hom_inv_id_app, Category.comp_id, Iso.hom_inv_id]
    rw [hd]
    simp [Category.assoc]
  have hq (K : D) : d.inv.app (T.obj K ⊗ G.obj (𝟙_ D)) ≫ q aF T P K =
      transferredQ aF T d p K := by
    dsimp [q, transferredQ]
    rw [← d.inv.naturality_assoc, reassoc_of% hd']
    simp [Category.assoc]
  have he (K : D) : transferredQ aF T d p K =
      S.map (h aF aS d u K) ≫ aS.counit.app K := by
    have e (K : D) :
        ((S.map (R.app (𝟙_ D)) ≫ aS.counit.app (𝟙_ D)) ⊗ₘ 𝟙 K) =
          (S.map (R.app (𝟙_ D)) ⊗ₘ 𝟙 K) ≫
            (aS.counit.app (𝟙_ D) ⊗ₘ 𝟙 K) := by simp
    have ev := congrArg (fun z => (p (T.obj (𝟙_ D)) K).inv ≫ z) (hev K)
    simp only [Iso.inv_hom_id_assoc] at ev
    have pn := hi _ _ K K (R.app (𝟙_ D)) (𝟙 K)
    simp only [T.map_id] at pn
    dsimp [transferredQ]
    rw [← hc, e]
    simp only [Category.assoc]
    rw [← reassoc_of% pn]
    rw [← ev, ← S.map_comp_assoc, ← S.map_comp_assoc]
    congr 1
    apply congrArg S.map
    have hb := braiding_naturality (𝟙 (T.obj K)) (R.app (𝟙_ D) ≫ u.hom)
    have hb' := congrArg (fun z => z ≫ (λ_ (T.obj K)).hom) hb
    simp only [Category.assoc, braiding_leftUnitor] at hb'
    simpa only [h, R, Category.assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id]
      using hb'.symm
  have hn (K L : D) (f : K ⟶ L) :
      F.map (T.map f ⊗ₘ 𝟙 (G.obj (𝟙_ D))) ≫ q aF T P L = q aF T P K ≫ f := by
    have pi : F.map (𝟙 (G.obj (𝟙_ D)) ⊗ₘ T.map f) ≫
        (P (G.obj (𝟙_ D)) L).inv =
          (P (G.obj (𝟙_ D)) K).inv ≫ (𝟙 (F.obj (G.obj (𝟙_ D))) ⊗ₘ f) := by
      apply (cancel_epi (P (G.obj (𝟙_ D)) K).hom).1
      simpa using congrArg (fun z => z ≫ (P (G.obj (𝟙_ D)) L).inv)
        (hP _ _ K L (𝟙 _) f).symm
    dsimp [q]
    rw [← F.map_comp_assoc, braiding_naturality, F.map_comp, Category.assoc, reassoc_of% pi]
    simp only [Category.assoc]
    congr 2
    simp only [tensorHom_def, id_whiskerRight, whiskerLeft_id, Category.id_comp,
      Category.comp_id]
    rw [whisker_exchange_assoc]
    simp [Category.assoc]
  refine ⟨inferInstance, ?_, ?_, ht, hq, he, ?_, hn, ?_, ?_, ?_⟩
  · intro K
    rw [hc]
    simp
  · intro ρ hρ
    ext K
    apply (aS.homEquiv _ K).symm.injective
    simp only [Adjunction.homEquiv_counit]
    rw [hc]
    apply (cancel_epi (d.hom.app (G.obj K))).1
    simpa using hρ K
  · intro K
    rw [← ht, hq, he]
    exact ((aS.homEquiv _ K).eq_symm_apply).mp rfl
  · intro K L f
    rw [← aF.homEquiv_naturality_left, hn, aF.homEquiv_naturality_right]
  · intro K L f
    change (T.map f ⊗ₘ 𝟙 (G.obj (𝟙_ D))) ≫
        ((𝟙 (T.obj L) ⊗ₘ (R.app (𝟙_ D) ≫ u.hom)) ≫ (ρ_ (T.obj L)).hom) =
      ((𝟙 (T.obj K) ⊗ₘ (R.app (𝟙_ D) ≫ u.hom)) ≫ (ρ_ (T.obj K)).hom) ≫ T.map f
    calc
      _ = (𝟙 (T.obj K) ⊗ₘ (R.app (𝟙_ D) ≫ u.hom)) ≫
          (T.map f ⊗ₘ 𝟙 (𝟙_ C)) ≫ (ρ_ (T.obj L)).hom := by
        simp only [← Category.assoc, tensorHom_comp_tensorHom,
          Category.comp_id, Category.id_comp]
      _ = _ := by simp only [tensorHom_id, rightUnitor_naturality, Category.assoc]
  · intro K L f
    rw [d.inv.naturality_assoc, hn]

end CategoryTheory
