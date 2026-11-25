/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

private theorem stalk_id (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (𝟙 F : F ⟶ F).stalkLinearMap x = LinearMap.id := by
  ext m
  obtain ⟨V, hx, s, rfl⟩ := F.presheaf.exists_germ_eq m
  rw [Hom.stalkLinearMap_germ]
  rfl

private theorem stalk_comp (X : Scheme.{u}) {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) (x : X) :
    (f ≫ g).stalkLinearMap x = g.stalkLinearMap x ∘ₗ f.stalkLinearMap x := by
  ext m
  obtain ⟨V, hx, s, rfl⟩ := F.presheaf.exists_germ_eq m
  simp only [Hom.stalkLinearMap_germ, LinearMap.comp_apply, Hom.comp_app,
    ConcreteCategory.comp_apply]

private def proj (X : Scheme.{u}) (F : X.Modules) (x : X) :
    moduleCup_godementObject X F ⟶ skyscraper x (F.presheaf.stalk x) :=
  Pi.π (fun y : X ↦ skyscraper y (F.presheaf.stalk y)) x

private def stalkEval (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (moduleCup_godementObject X F).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x :=
  skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (proj X F x).stalkLinearMap x

private theorem proj_unit (X : Scheme.{u}) (F : X.Modules) (x : X) :
    moduleCup_godementUnit X F ≫ proj X F x = toSkyscraper (LinearMap.id :
      F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) := by
  simp only [moduleCup_godementUnit, proj, Pi.lift_comp_π]

private theorem proj_map (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) (x : X) :
    moduleCup_godementMap X f ≫ proj X G x =
      toSkyscraper (f.stalkLinearMap x ∘ₗ stalkEval X F x) := by
  simp only [moduleCup_godementMap, proj, Pi.lift_comp_π, comp_toSkyscraper, stalkEval,
    LinearMap.comp_assoc]

private theorem eval_toSkyscraper (X : Scheme.{u}) (F : X.Modules) (x : X)
    {P : X.Modules} (l : P.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) :
    skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (toSkyscraper l).stalkLinearMap x = l :=
  (skyscraperHomEquiv x (F.presheaf.stalk x) P).left_inv l

private theorem eval_unit (X : Scheme.{u}) (F : X.Modules) (x : X) :
    stalkEval X F x ∘ₗ (moduleCup_godementUnit X F).stalkLinearMap x = LinearMap.id := by
  dsimp only [stalkEval]
  rw [LinearMap.comp_assoc, ← stalk_comp, proj_unit, eval_toSkyscraper]

private theorem eval_map (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) (x : X) :
    stalkEval X G x ∘ₗ (moduleCup_godementMap X f).stalkLinearMap x =
      f.stalkLinearMap x ∘ₗ stalkEval X F x := by
  change (skyscraperStalkEval x (G.presheaf.stalk x) ∘ₗ
    (proj X G x).stalkLinearMap x) ∘ₗ (moduleCup_godementMap X f).stalkLinearMap x = _
  rw [LinearMap.comp_assoc, ← stalk_comp, proj_map, eval_toSkyscraper]

private theorem map_id (X : Scheme.{u}) (F : X.Modules) :
    moduleCup_godementMap X (𝟙 F) = 𝟙 _ := by
  apply Pi.hom_ext
  intro x
  change moduleCup_godementMap X (𝟙 F) ≫ proj X F x = (𝟙 _ : _ ⟶ _) ≫ proj X F x
  rw [proj_map, stalk_id, LinearMap.id_comp, Category.id_comp]
  exact (skyscraperHomEquiv x (F.presheaf.stalk x) _).right_inv _

private theorem map_comp (X : Scheme.{u}) {F G H : X.Modules}
    (f : F ⟶ G) (g : G ⟶ H) :
    moduleCup_godementMap X (f ≫ g) =
      moduleCup_godementMap X f ≫ moduleCup_godementMap X g := by
  apply Pi.hom_ext
  intro x
  change moduleCup_godementMap X (f ≫ g) ≫ proj X H x =
    (moduleCup_godementMap X f ≫ moduleCup_godementMap X g) ≫ proj X H x
  rw [Category.assoc, proj_map, proj_map, comp_toSkyscraper, stalk_comp,
    LinearMap.comp_assoc, LinearMap.comp_assoc, eval_map]

private theorem unit_natural (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) :
    moduleCup_godementUnit X F ≫ moduleCup_godementMap X f =
      f ≫ moduleCup_godementUnit X G := by
  apply Pi.hom_ext
  intro x
  change (moduleCup_godementUnit X F ≫ moduleCup_godementMap X f) ≫ proj X G x =
    (f ≫ moduleCup_godementUnit X G) ≫ proj X G x
  rw [Category.assoc, Category.assoc, proj_map, proj_unit, comp_toSkyscraper,
    comp_toSkyscraper, LinearMap.id_comp, LinearMap.comp_assoc, eval_unit,
    LinearMap.comp_id]


private def iteratePairing (X : Scheme.{u}) (F G : X.Modules)
    (b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K)) :
    (n : ℕ) → (moduleCup_godementIterate X F n ⊗
      moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n)
  | 0 => 𝟙 (F ⊗ G)
  | n + 1 => b _ _ ≫ moduleCup_godementMap X (iteratePairing X F G b n)

/-- Recursive pairings from a compatible Godement tensor pairing.
Source: Banerjee, arXiv:1004.1491, §1.1.4.
(blueprint: new-module-cup-godement-iterate-pairings-from-beta)
Define p₀ as the identity and pₙ₊₁ as b followed by T(pₙ). At n = 0 the only
insertion is the unit, so the claim is the unit law and T(id) = id. For the induction
step split the insertion index into zero and successor. Index zero uses the unit law
followed by naturality of the germ map applied to pₙ₊₁. A successor insertion is
T of the preceding insertion; naturality of b moves those maps past b, functoriality
combines their image with T(pₙ₊₁), the induction hypothesis applies, and functoriality
separates the resulting composite. No multiplication law is needed. -/
theorem moduleCup_godement_iterate_pairings_from_beta (X : Scheme.{u})
    (F G : X.Modules) (b : ∀ H K : X.Modules,
      moduleCup_godementObject X H ⊗ moduleCup_godementObject X K ⟶
        moduleCup_godementObject X (H ⊗ K))
    (hnat : ∀ (H K H' K' : X.Modules) (f : H ⟶ H') (g : K ⟶ K'),
      (moduleCup_godementMap X f ⊗ₘ moduleCup_godementMap X g) ≫ b H' K' =
        b H K ≫ moduleCup_godementMap X (f ⊗ₘ g))
    (hunit : ∀ H K : X.Modules,
      (moduleCup_godementUnit X H ⊗ₘ moduleCup_godementUnit X K) ≫ b H K =
        moduleCup_godementUnit X (H ⊗ K)) :
    ∃ (p : ∀ n : ℕ, moduleCup_godementIterate X F n ⊗
        moduleCup_godementIterate X G n ⟶ moduleCup_godementIterate X (F ⊗ G) n),
      p 0 = 𝟙 (F ⊗ G) ∧
      (∀ n, p (n + 1) = b (moduleCup_godementIterate X F n)
        (moduleCup_godementIterate X G n) ≫ moduleCup_godementMap X (p n)) ∧
      (∀ (n : ℕ) (i : Fin (n + 1)),
        (moduleCup_godementInsert X F n i ⊗ₘ moduleCup_godementInsert X G n i) ≫
          p (n + 1) = p n ≫ moduleCup_godementInsert X (F ⊗ G) n i) := by
  let p := iteratePairing X F G b
  refine ⟨p, rfl, fun _ ↦ rfl, ?_⟩
  intro n
  induction n with
  | zero =>
      intro i
      have hi : i = 0 := by
        apply Fin.ext
        have := i.isLt
        omega
      subst i
      change (moduleCup_godementUnit X F ⊗ₘ moduleCup_godementUnit X G) ≫
        (b F G ≫ moduleCup_godementMap X (𝟙 (F ⊗ G))) =
          𝟙 (F ⊗ G) ≫ moduleCup_godementUnit X (F ⊗ G)
      rw [map_id, Category.comp_id, Category.id_comp]
      exact hunit F G
  | succ n ih =>
      intro i
      refine Fin.cases ?_ (fun j ↦ ?_) i
      · have ins (H : X.Modules) (k : ℕ) :
            moduleCup_godementInsert X H k 0 =
              moduleCup_godementUnit X (moduleCup_godementIterate X H k) := by
          cases k <;> simp [moduleCup_godementInsert, moduleCup_godementIterate]
        rw [ins, ins, ins]
        change (_ ⊗ₘ _) ≫ (b _ _ ≫ moduleCup_godementMap X (p (n + 1))) = _
        rw [← Category.assoc, hunit, unit_natural]
      · have ins (H : X.Modules) :
            moduleCup_godementInsert X H (n + 1) j.succ =
              moduleCup_godementMap X (moduleCup_godementInsert X H n j) := by
          simp only [moduleCup_godementInsert, Fin.val_succ, Nat.add_eq_zero_iff,
            Nat.one_ne_zero, and_false, ↓reduceDIte]
          congr 2
        rw [ins, ins, ins]
        change (_ ⊗ₘ _) ≫ (b _ _ ≫ moduleCup_godementMap X (p (n + 1))) =
          (b _ _ ≫ moduleCup_godementMap X (p n)) ≫ _
        rw [← Category.assoc, hnat, Category.assoc, ← map_comp, ih j,
          map_comp, Category.assoc]

end
end AlgebraicGeometry.Scheme.Modules
