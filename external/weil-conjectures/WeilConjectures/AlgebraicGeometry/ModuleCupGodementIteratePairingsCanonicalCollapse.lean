/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementIteratePairingsCanonical

/-! # Collapse compatibility for the canonical recursively generated pairing -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem stalk_comp (X : Scheme.{u}) {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) (x : X) :
    (f ≫ g).stalkLinearMap x = g.stalkLinearMap x ∘ₗ f.stalkLinearMap x := by
  ext m
  obtain ⟨V, hx, s, rfl⟩ := F.presheaf.exists_germ_eq m
  simp only [Hom.stalkLinearMap_germ, LinearMap.comp_apply, Hom.comp_app,
    ConcreteCategory.comp_apply]

private def proj (X : Scheme.{u}) (F : X.Modules) (x : X) :
    moduleCup_godementObject X F ⟶ skyscraper x (F.presheaf.stalk x) :=
  CategoryTheory.Limits.Pi.π (fun y : X ↦ skyscraper y (F.presheaf.stalk y)) x

private def eval (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (moduleCup_godementObject X F).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x :=
  skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (proj X F x).stalkLinearMap x

private theorem proj_map (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) (x : X) :
    moduleCup_godementMap X f ≫ proj X G x =
      toSkyscraper (f.stalkLinearMap x ∘ₗ eval X F x) := by
  simp only [moduleCup_godementMap, proj, CategoryTheory.Limits.Pi.lift_comp_π,
    comp_toSkyscraper, eval, LinearMap.comp_assoc]

private theorem proj_multiply (X : Scheme.{u}) (F : X.Modules) (x : X) :
    moduleCup_godementMultiply X F ≫ proj X F x =
      toSkyscraper (eval X F x ∘ₗ eval X (moduleCup_godementObject X F) x) := by
  simp only [moduleCup_godementMultiply, proj, CategoryTheory.Limits.Pi.lift_comp_π,
    comp_toSkyscraper, eval, LinearMap.comp_assoc]

private theorem eval_toSkyscraper (X : Scheme.{u}) (F : X.Modules) (x : X)
    {P : X.Modules} (l : P.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) :
    skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (toSkyscraper l).stalkLinearMap x = l :=
  (skyscraperHomEquiv x (F.presheaf.stalk x) P).left_inv l

private theorem eval_map (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) (x : X) :
    eval X G x ∘ₗ (moduleCup_godementMap X f).stalkLinearMap x =
      f.stalkLinearMap x ∘ₗ eval X F x := by
  change (skyscraperStalkEval x (G.presheaf.stalk x) ∘ₗ
    (proj X G x).stalkLinearMap x) ∘ₗ (moduleCup_godementMap X f).stalkLinearMap x = _
  rw [LinearMap.comp_assoc, ← stalk_comp, proj_map, eval_toSkyscraper]

private theorem eval_multiply (X : Scheme.{u}) (F : X.Modules) (x : X) :
    eval X F x ∘ₗ (moduleCup_godementMultiply X F).stalkLinearMap x =
      eval X F x ∘ₗ eval X (moduleCup_godementObject X F) x := by
  change (skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ
    (proj X F x).stalkLinearMap x) ∘ₗ
      (moduleCup_godementMultiply X F).stalkLinearMap x = _
  rw [LinearMap.comp_assoc, ← stalk_comp, proj_multiply, eval_toSkyscraper]

private theorem map_comp (X : Scheme.{u}) {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) :
    moduleCup_godementMap X (f ≫ g) =
      moduleCup_godementMap X f ≫ moduleCup_godementMap X g := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro x
  change moduleCup_godementMap X (f ≫ g) ≫ proj X H x =
    (moduleCup_godementMap X f ≫ moduleCup_godementMap X g) ≫ proj X H x
  rw [Category.assoc, proj_map, proj_map, comp_toSkyscraper, stalk_comp,
    LinearMap.comp_assoc, LinearMap.comp_assoc, eval_map]

private theorem multiply_natural (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) :
    moduleCup_godementMultiply X F ≫ moduleCup_godementMap X f =
      moduleCup_godementMap X (moduleCup_godementMap X f) ≫
        moduleCup_godementMultiply X G := by
  apply CategoryTheory.Limits.Pi.hom_ext
  intro x
  change (moduleCup_godementMultiply X F ≫ moduleCup_godementMap X f) ≫ proj X G x =
    (moduleCup_godementMap X (moduleCup_godementMap X f) ≫
      moduleCup_godementMultiply X G) ≫ proj X G x
  rw [Category.assoc, Category.assoc, proj_map, proj_multiply, comp_toSkyscraper,
    comp_toSkyscraper]
  simp only [LinearMap.comp_assoc, eval_multiply, eval_map]
  rw [← LinearMap.comp_assoc (eval X (moduleCup_godementObject X F) x)
    ((moduleCup_godementMap X f).stalkLinearMap x), eval_map]
  rfl

private theorem collapse_zero (X : Scheme.{u}) (F : X.Modules) (n : ℕ) :
    moduleCup_godementCollapse X F n 0 =
      moduleCup_godementMultiply X (moduleCup_godementIterate X F n) := by
  cases n <;> simp [moduleCup_godementCollapse, moduleCup_godementIterate]

private theorem collapse_succ (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i : Fin (n + 1)) :
    moduleCup_godementCollapse X F (n + 1) i.succ =
      moduleCup_godementMap X (moduleCup_godementCollapse X F n i) := by
  simp only [moduleCup_godementCollapse, Fin.val_succ, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceDIte]
  congr 2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Collapse compatibility for the canonical recursively generated pairing.
Source: Banerjee, arXiv:1004.1491, §1.1.4, pp. 15–16; Stacks, Tag 0FKR.
(blueprint: new-module-cup-godement-iterate-pairings-canonical-collapse)
Proof: Induct on n. At n=0 substitute the recursion twice and p0=id; beta.multiply is exactly the
asserted equality after functoriality simplifies T(id). For n+1 split the insertion position into
zero and successor. Position zero uses beta.multiply on T^(n+1)F and T^(n+1)G followed by
T(p_(n+1)); move this latter map across multiplication by multiplication naturality. At a
successor position write each collapse as T of the lower collapse. Substitute the recursion for
both pairing terms, move the two T(collapse) maps through beta using beta.naturality, and apply T
to the induction hypothesis. Functoriality and associativity identify the resulting composites.
Naturality of T and of multiplication follows directly from their product projection formulas and
naturality of stalk evaluation. The argument uses beta.naturality and beta.multiply;
coface compatibility alone is insufficient. The cases of an empty scheme and zero sheaves are
covered by product
uniqueness. -/
theorem moduleCup_godement_iterate_pairings_collapse_of_canonical
    (X : Scheme.{u}) (F G : X.Modules) (β : ModuleCupGodementBeta X)
    (p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗
      moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n)
    (hp0 : p 0 = 𝟙 (F ⊗ G))
    (hprec : ∀ n, p (n + 1) = β.map (moduleCup_godementIterate X F n)
      (moduleCup_godementIterate X G n) ≫ moduleCup_godementMap X (p n)) :
    ∀ (n : ℕ) (i : Fin (n + 1)),
      (moduleCup_godementCollapse X F n i ⊗ₘ moduleCup_godementCollapse X G n i) ≫
        p (n + 1) = p (n + 2) ≫ moduleCup_godementCollapse X (F ⊗ G) n i := by
  have _hp0 := hp0
  intro n
  induction n with
  | zero =>
    intro i
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    rw [collapse_zero, collapse_zero, collapse_zero, hprec 1, hprec 0]
    simp only [moduleCup_godementIterate, Category.assoc]
    rw [← Category.assoc, β.multiply]
    simp only [Category.assoc, map_comp]
    rw [multiply_natural]
  | succ n ih =>
    intro i
    cases i using Fin.cases with
    | zero =>
      rw [collapse_zero, collapse_zero, collapse_zero, hprec (n + 2), hprec (n + 1)]
      simp only [moduleCup_godementIterate, Category.assoc]
      rw [← Category.assoc, β.multiply]
      simp only [Category.assoc, map_comp]
      rw [multiply_natural]
    | succ i =>
      rw [collapse_succ, collapse_succ, collapse_succ, hprec (n + 2), hprec (n + 1)]
      simp only [moduleCup_godementIterate, Category.assoc]
      rw [← Category.assoc, β.naturality]
      simp only [Category.assoc, ← map_comp]
      rw [ih i, hprec (n + 1), Category.assoc]
      rfl

end
end AlgebraicGeometry.Scheme.Modules
