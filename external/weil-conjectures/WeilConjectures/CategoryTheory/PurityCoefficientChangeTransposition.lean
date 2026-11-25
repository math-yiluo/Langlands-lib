/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Transposition of the purity and smooth-trace coefficient equations

Source: the opening paragraph of the proof of proposition-compatibility-purity-change-coefficients.
-/

@[expose] public section

set_option autoImplicit false

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
  {F : C ⥤ D} {G J : D ⥤ C} {F' : C' ⥤ D'} {G' J' : D' ⥤ C'}
  {S : C ⥤ C'} {T : D ⥤ D'}

/-- The purity coefficient equation is equivalent to its smooth-trace equation.
The exceptional comparison is the mate of the inverse compact-support comparison;
the source arrow may be any specified arrow, including a nonflat scalar map.

Source: det-sp-purity-coefficient-change.proof.md, opening paragraph and clause (2).
(blueprint: lem-pur-coefficient-trace-transposition).

Proof: apply the injective transposition bijection for `F' ⊣ G'`. The mate's
counit equation rewrites the transpose of the first side as `b⁻¹ T(ε Fγ)`;
naturality of `b⁻¹` moves `γ` through this expression. The second transpose is
`F'(a) ε' F'(γ')`. Cancel the invertible `b` to obtain the trace equation. -/
theorem purityCoefficientChange_iff_trace
    (adj : F ⊣ G) (adj' : F' ⊣ G') (b : F ⋙ T ≅ S ⋙ F')
    (γ : J ≅ G) (γ' : J' ≅ G') (K : D)
    (a : S.obj (J.obj K) ⟶ J'.obj (T.obj K)) :
    S.map (γ.hom.app K) ≫
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ b.inv)).app K =
      a ≫ γ'.hom.app (T.obj K) ↔
    T.map (F.map (γ.hom.app K) ≫ adj.counit.app K) =
      b.hom.app (J.obj K) ≫ F'.map a ≫
        (F'.map (γ'.hom.app (T.obj K)) ≫ adj'.counit.app (T.obj K)) := by
  have h : (adj'.homEquiv _ _).symm
      (S.map (γ.hom.app K) ≫
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ b.inv)).app K) =
      b.inv.app (J.obj K) ≫ T.map (F.map (γ.hom.app K) ≫ adj.counit.app K) := by
    rw [Adjunction.homEquiv_counit, F'.map_comp, Category.assoc,
      mateEquiv_counit]
    rw [← Category.assoc]
    change ((S ⋙ F').map (γ.hom.app K) ≫ b.inv.app (G.obj K)) ≫ _ = _
    rw [b.inv.naturality, Category.assoc]
    change _ = b.inv.app (J.obj K) ≫ _
    rw [T.map_comp]
    rfl
  rw [← (adj'.homEquiv _ _).symm.injective.eq_iff, h]
  rw [Adjunction.homEquiv_counit, F'.map_comp, Category.assoc]
  rw [← cancel_epi (b.hom.app (J.obj K))]
  simp only [Iso.hom_inv_id_app_assoc]

/-- A source comparison satisfying the purity square is the conjugate of the
exceptional comparison. Source: the transposition calculation in the proof of
`proposition-compatibility-purity-change-coefficients` (blueprint:
lem-pur-coefficient-trace-transposition). Multiply the square on the right by the inverse target
purity isomorphism. -/
theorem purityCoefficientChange_source_eq
    (γ : J ≅ G) (γ' : J' ≅ G') (β : G ⋙ S ⟶ T ⋙ G') (K : D)
    (a : S.obj (J.obj K) ⟶ J'.obj (T.obj K))
    (h : S.map (γ.hom.app K) ≫ β.app K = a ≫ γ'.hom.app (T.obj K)) :
    a = S.map (γ.hom.app K) ≫ β.app K ≫ γ'.inv.app (T.obj K) := by
  rw [← Category.assoc, h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- Naturality of a source comparison follows from its purity squares.
Source: the naturality calculation in the proof of
`proposition-compatibility-purity-change-coefficients` (blueprint:
lem-pur-coefficient-trace-transposition). The preceding conjugation formula identifies the component
family with the composite of three natural transformations. Apply naturality of that composite. -/
theorem purityCoefficientChange_source_natural
    (γ : J ≅ G) (γ' : J' ≅ G') (β : G ⋙ S ⟶ T ⋙ G')
    (a : ∀ K : D, S.obj (J.obj K) ⟶ J'.obj (T.obj K))
    (h : ∀ K, S.map (γ.hom.app K) ≫ β.app K = a K ≫ γ'.hom.app (T.obj K))
    {K L : D} (v : K ⟶ L) :
    S.map (J.map v) ≫ a L = a K ≫ J'.map (T.map v) := by
  let α : J ⋙ S ⟶ T ⋙ J' :=
    Functor.whiskerRight γ.hom S ≫ β ≫ Functor.whiskerLeft T γ'.inv
  have ha : ∀ K, a K = α.app K := fun K ↦
    purityCoefficientChange_source_eq γ γ' β K (a K) (h K)
  simpa only [ha, Functor.comp_map] using α.naturality v

/-- The source comparison is invertible whenever the exceptional comparison is.
Source: the conjugation calculation in the proof of
`proposition-compatibility-purity-change-coefficients` (blueprint:
lem-pur-coefficient-trace-transposition). Use the preceding formula and closure of isomorphisms
under functors and composition. -/
theorem purityCoefficientChange_source_isIso
    (γ : J ≅ G) (γ' : J' ≅ G') (β : G ⋙ S ⟶ T ⋙ G') (K : D)
    (a : S.obj (J.obj K) ⟶ J'.obj (T.obj K)) [IsIso (β.app K)]
    (h : S.map (γ.hom.app K) ≫ β.app K = a ≫ γ'.hom.app (T.obj K)) :
    IsIso a := by
  rw [purityCoefficientChange_source_eq γ γ' β K a h]
  infer_instance

end CategoryTheory
