/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.Category

/-!
# Coefficient comparisons for unique right adjoints

Let `F ⊣ G`, `F ⊣ J`, `F' ⊣ G'` and `F' ⊣ J'` be adjunctions, and let `b : F ⋙ T ≅ S ⋙ F'`
compare the left adjoints along functors `S` and `T` (a change of coefficients). Transposing `b`
gives comparisons `G ⋙ S ⟶ T ⋙ G'` and `J ⋙ S ⟶ T ⋙ J'` of the right adjoints. They are
conjugate under the canonical isomorphisms `G ≅ J` and `G' ≅ J'` of
`Adjunction.rightAdjointUniq`. So invertibility and composition identities transfer from one
choice of right adjoints to the other (blueprint `proposition-sp-unique-adjoint`, part of
`proposition-sp-unique-adjoint`).

## Main results

- `CategoryTheory.coefficientAdjointComparison_eq_conjugate`: the conjugation formula.
- `CategoryTheory.coefficientAdjointComparison_isIso`: invertibility transfers.
- `CategoryTheory.coefficientAdjointComparison_composition`: composition identities transfer.
-/

@[expose] public section

universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆

open CategoryTheory

namespace CategoryTheory

/-- The coefficient comparison obtained by transposing a counit through a
coefficient comparison of left adjoints.
(blueprint `proposition-sp-unique-adjoint`). -/
noncomputable def coefficientAdjointComparison
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {F : C ⥤ D} {F' : C' ⥤ D'} {S : C ⥤ C'} {T : D ⥤ D'}
    {J : D ⥤ C} {J' : D' ⥤ C'}
    (a : F ⊣ J) (a' : F' ⊣ J') (b : F ⋙ T ≅ S ⋙ F') :
    J ⋙ S ⟶ T ⋙ J' :=
  (mateEquiv a a' (TwoSquare.mk S F F' T b.inv))

/-- The composition identity for coefficient comparisons, with explicit
composition isomorphisms for source and target scalar extension.
(blueprint `proposition-sp-unique-adjoint`). -/
def CoefficientComparisonComposition
    {C₀ : Type u₁} {C₁ : Type u₂} {C₂ : Type u₃}
    {D₀ : Type u₄} {D₁ : Type u₅} {D₂ : Type u₆}
    [Category.{v₁} C₀] [Category.{v₂} C₁] [Category.{v₃} C₂]
    [Category.{v₄} D₀] [Category.{v₅} D₁] [Category.{v₆} D₂]
    {J₀ : D₀ ⥤ C₀} {J₁ : D₁ ⥤ C₁} {J₂ : D₂ ⥤ C₂}
    {S₀₁ : C₀ ⥤ C₁} {S₁₂ : C₁ ⥤ C₂} {S₀₂ : C₀ ⥤ C₂}
    {T₀₁ : D₀ ⥤ D₁} {T₁₂ : D₁ ⥤ D₂} {T₀₂ : D₀ ⥤ D₂}
    (s : S₀₁ ⋙ S₁₂ ≅ S₀₂) (t : T₀₁ ⋙ T₁₂ ≅ T₀₂)
    (c₀₁ : J₀ ⋙ S₀₁ ⟶ T₀₁ ⋙ J₁)
    (c₁₂ : J₁ ⋙ S₁₂ ⟶ T₁₂ ⋙ J₂)
    (c₀₂ : J₀ ⋙ S₀₂ ⟶ T₀₂ ⋙ J₂) : Prop :=
  c₀₂ = (Functor.isoWhiskerLeft J₀ s).inv ≫
      (Functor.whiskerRight c₀₁ S₁₂ ≫ Functor.whiskerLeft T₀₁ c₁₂) ≫
      (Functor.isoWhiskerRight t J₂).hom

/-- Conjugation of a coefficient comparison by isomorphisms of right adjoints:
the right-hand side `γ'(K_{Λ'}) ∘ c(K) ∘ (γ(K)⁻¹)_{Λ'}` of the displayed formula.
(blueprint `proposition-sp-unique-adjoint`). -/
def conjugateCoefficientComparison
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {G : D ⥤ C} {J : D ⥤ C} {G' : D' ⥤ C'} {J' : D' ⥤ C'}
    {S : C ⥤ C'} {T : D ⥤ D'} (γ : G ≅ J) (γ' : G' ≅ J')
    (c : G ⋙ S ⟶ T ⋙ G') : J ⋙ S ⟶ T ⋙ J' :=
  Functor.whiskerRight γ.inv S ≫ c ≫ Functor.whiskerLeft T γ'.hom

/-- Right adjoints inherit coefficient comparisons.  The comparison `c_J` is
specified by the `J'`-transpose of the transported counit, and is conjugate to
the analogous comparison `c_f` for any other pair of right adjoints.  It
therefore preserves invertibility and composition identities.
(blueprint `proposition-sp-unique-adjoint`).
Proof (the node's steps).
1. By `proposition-sp-unique-adjoint--1` (`Adjunction.rightAdjointUniq`), `γ(K)` is the
   `J`-transpose of `ε_G(K)` and `γ'(L)` the `J'`-transpose of `ε_{G'}(L)`, so
   `ε^J(K) ∘ F(γ(K)) = ε_G(K)`, `ε^{J'}(L) ∘ F'(γ'(L)) = ε_{G'}(L)`, and hence
   `ε_G(K) ∘ F(γ(K)⁻¹) = ε^J(K)`.
2. Let `u = γ'(T K) ∘ c_f(K) ∘ S(γ(K)⁻¹)`. Its `J'`-transpose
   `ε^{J'}(T K) ∘ F'(u)` becomes, by the second counit equation and the defining
   transpose equation of `c_f`, `T(ε_G K) ∘ b(G K)⁻¹ ∘ F'(S(γ(K)⁻¹))`; naturality
   of `b` rewrites this as `T(ε_G K) ∘ T(F(γ(K)⁻¹)) ∘ b(J K)⁻¹`, and functoriality
   of `T` with the last equation of step 1 gives `T(ε^J K) ∘ b(J K)⁻¹`, the
   transpose defining `c_J(K)`.
3. The `J'`-transpose (`Adjunction.homEquiv`) is injective, so `c_J(K) = u` for
   every `K`.
4. (`coefficientAdjointComparison_isIso`, `coefficientAdjointComparison_composition`)
   `γ, γ'` are isomorphisms and `S` preserves them, so `c_J` is an isomorphism
   whenever `c_f` is; conjugating the composition identity for `c_f` the middle
   `γ'` and `γ'⁻¹` cancel and naturality of the scalar-composition isomorphisms
   moves the outer `γ`'s past them. -/
theorem coefficientAdjointComparison_eq_conjugate
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {F : C ⥤ D} {F' : C' ⥤ D'} {S : C ⥤ C'} {T : D ⥤ D'}
    {G : D ⥤ C} {J : D ⥤ C} {G' : D' ⥤ C'} {J' : D' ⥤ C'}
    (aG : F ⊣ G) (aJ : F ⊣ J) (aG' : F' ⊣ G') (aJ' : F' ⊣ J')
    (b : F ⋙ T ≅ S ⋙ F') :
    let cJ := coefficientAdjointComparison aJ aJ' b
    let cf := coefficientAdjointComparison aG aG' b
    let γ := aG.rightAdjointUniq aJ
    let γ' := aG'.rightAdjointUniq aJ'
    cJ = Functor.whiskerRight γ.inv S ≫ cf ≫
      Functor.whiskerLeft T γ'.hom := by
  dsimp only
  ext K
  apply (aJ'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  rw [Adjunction.rightAdjointUniq_hom_app_counit]
  dsimp only [coefficientAdjointComparison]
  rw [mateEquiv_counit aJ aJ' (TwoSquare.mk S F F' T b.inv) K,
    mateEquiv_counit aG aG' (TwoSquare.mk S F F' T b.inv) K]
  change b.inv.app (J.obj K) ≫ T.map (aJ.counit.app K) =
    F'.map (S.map ((aG.rightAdjointUniq aJ).inv.app K)) ≫
      b.inv.app (G.obj K) ≫ T.map (aG.counit.app K)
  have hb := b.inv.naturality ((aG.rightAdjointUniq aJ).inv.app K)
  simp only [Functor.comp_map] at hb
  rw [← Category.assoc, hb]
  simp only [Category.assoc, ← T.map_comp,
    Adjunction.rightAdjointUniq_inv_app, Adjunction.rightAdjointUniq_hom_app_counit]

/-- Conjugation by the unique right-adjoint isomorphisms preserves invertibility
of every component of a coefficient comparison: `c_J` is an isomorphism whenever
`c_f` is.
(blueprint `proposition-sp-unique-adjoint`).
Proof: by `coefficientAdjointComparison_eq_conjugate`, `c_J(K)` is the composite
of `S(γ(K)⁻¹)`, `c_f(K)` and `γ'(T K)`, isomorphisms by `proposition-sp-unique-adjoint--1`
and functoriality of `S`. -/
theorem coefficientAdjointComparison_isIso
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {F : C ⥤ D} {F' : C' ⥤ D'} {S : C ⥤ C'} {T : D ⥤ D'}
    {G : D ⥤ C} {J : D ⥤ C} {G' : D' ⥤ C'} {J' : D' ⥤ C'}
    (aG : F ⊣ G) (aJ : F ⊣ J) (aG' : F' ⊣ G') (aJ' : F' ⊣ J')
    (b : F ⋙ T ≅ S ⋙ F')
    (K : D) (hK : IsIso ((coefficientAdjointComparison aG aG' b).app K)) :
    IsIso ((coefficientAdjointComparison aJ aJ' b).app K) := by
  have := hK
  have h := congr_app (coefficientAdjointComparison_eq_conjugate aG aJ aG' aJ' b) K
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  rw [h]
  infer_instance

/-- The composition identity for right-adjoint coefficient comparisons is
obtained by conjugating the identity for the original right adjoints, the same
`γ₁` serving the extensions out of and into the middle coefficients.
(blueprint `proposition-sp-unique-adjoint`).
Proof: substitute the conjugation formulas; the adjacent `γ₁.hom` and `γ₁.inv`
cancel by functoriality of `S₁₂`, and naturality of `s` and `t` moves `γ₀.inv`
and `γ₂.hom` past the scalar-composition isomorphisms. -/
theorem coefficientAdjointComparison_composition
    {C₀ : Type u₁} {C₁ : Type u₂} {C₂ : Type u₃}
    {D₀ : Type u₄} {D₁ : Type u₅} {D₂ : Type u₆}
    [Category.{v₁} C₀] [Category.{v₂} C₁] [Category.{v₃} C₂]
    [Category.{v₄} D₀] [Category.{v₅} D₁] [Category.{v₆} D₂]
    {G₀ : D₀ ⥤ C₀} {G₁ : D₁ ⥤ C₁} {G₂ : D₂ ⥤ C₂}
    {J₀ : D₀ ⥤ C₀} {J₁ : D₁ ⥤ C₁} {J₂ : D₂ ⥤ C₂}
    {S₀₁ : C₀ ⥤ C₁} {S₁₂ : C₁ ⥤ C₂} {S₀₂ : C₀ ⥤ C₂}
    {T₀₁ : D₀ ⥤ D₁} {T₁₂ : D₁ ⥤ D₂} {T₀₂ : D₀ ⥤ D₂}
    (s : S₀₁ ⋙ S₁₂ ≅ S₀₂) (t : T₀₁ ⋙ T₁₂ ≅ T₀₂)
    (γ₀ : G₀ ≅ J₀) (γ₁ : G₁ ≅ J₁) (γ₂ : G₂ ≅ J₂)
    (c₀₁ : G₀ ⋙ S₀₁ ⟶ T₀₁ ⋙ G₁)
    (c₁₂ : G₁ ⋙ S₁₂ ⟶ T₁₂ ⋙ G₂)
    (c₀₂ : G₀ ⋙ S₀₂ ⟶ T₀₂ ⋙ G₂)
    (h : CoefficientComparisonComposition s t c₀₁ c₁₂ c₀₂) :
    CoefficientComparisonComposition s t (conjugateCoefficientComparison γ₀ γ₁ c₀₁)
      (conjugateCoefficientComparison γ₁ γ₂ c₁₂)
      (conjugateCoefficientComparison γ₀ γ₂ c₀₂) := by
  dsimp only [CoefficientComparisonComposition] at h ⊢
  rw [conjugateCoefficientComparison, h]
  ext K
  dsimp [conjugateCoefficientComparison]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, s.inv.naturality]
  simp only [Functor.comp_map, Category.assoc]
  slice_rhs 4 5 => rw [← S₁₂.map_comp, γ₁.hom_inv_id_app, S₁₂.map_id]
  simp only [Category.id_comp, Category.assoc]
  rw [γ₂.hom.naturality]

end CategoryTheory
