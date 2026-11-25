/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
public import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic

/-! # Godement operators on the free simplex quiver -/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace AlgebraicTopology Simplicial
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

private def eval (X : Scheme.{u}) (F : X.Modules) (x : X) :
    (moduleCup_godementObject X F).presheaf.stalk x →ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x :=
  skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (proj X F x).stalkLinearMap x

private theorem proj_unit (X : Scheme.{u}) (F : X.Modules) (x : X) :
    moduleCup_godementUnit X F ≫ proj X F x = toSkyscraper (LinearMap.id :
      F.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) := by
  simp only [moduleCup_godementUnit, proj, Pi.lift_comp_π]

private theorem proj_map (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) (x : X) :
    moduleCup_godementMap X f ≫ proj X G x =
      toSkyscraper (f.stalkLinearMap x ∘ₗ eval X F x) := by
  simp only [moduleCup_godementMap, proj, Pi.lift_comp_π, comp_toSkyscraper, eval,
    LinearMap.comp_assoc]

private theorem proj_multiply (X : Scheme.{u}) (F : X.Modules) (x : X) :
    moduleCup_godementMultiply X F ≫ proj X F x =
      toSkyscraper (eval X F x ∘ₗ eval X (moduleCup_godementObject X F) x) := by
  simp only [moduleCup_godementMultiply, proj, Pi.lift_comp_π, comp_toSkyscraper, eval,
    LinearMap.comp_assoc]

private theorem eval_toSkyscraper (X : Scheme.{u}) (F : X.Modules) (x : X)
    {P : X.Modules} (l : P.presheaf.stalk x →ₗ[X.presheaf.stalk x] F.presheaf.stalk x) :
    skyscraperStalkEval x (F.presheaf.stalk x) ∘ₗ (toSkyscraper l).stalkLinearMap x = l :=
  (skyscraperHomEquiv x (F.presheaf.stalk x) P).left_inv l

private theorem eval_unit (X : Scheme.{u}) (F : X.Modules) (x : X) :
    eval X F x ∘ₗ (moduleCup_godementUnit X F).stalkLinearMap x = LinearMap.id := by
  dsimp only [eval]
  rw [LinearMap.comp_assoc, ← stalk_comp, proj_unit, eval_toSkyscraper]

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

private theorem multiply_natural (X : Scheme.{u}) {F G : X.Modules} (f : F ⟶ G) :
    moduleCup_godementMultiply X F ≫ moduleCup_godementMap X f =
      moduleCup_godementMap X (moduleCup_godementMap X f) ≫
        moduleCup_godementMultiply X G := by
  apply Pi.hom_ext
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

private theorem unit_multiply (X : Scheme.{u}) (F : X.Modules) :
    moduleCup_godementUnit X (moduleCup_godementObject X F) ≫
      moduleCup_godementMultiply X F = 𝟙 _ := by
  apply Pi.hom_ext
  intro x
  change (moduleCup_godementUnit X (moduleCup_godementObject X F) ≫
    moduleCup_godementMultiply X F) ≫ proj X F x = (𝟙 _ : _ ⟶ _) ≫ proj X F x
  rw [Category.assoc, proj_multiply, comp_toSkyscraper, LinearMap.comp_assoc,
    eval_unit, LinearMap.comp_id, Category.id_comp]
  exact (skyscraperHomEquiv x (F.presheaf.stalk x) _).right_inv _

private theorem map_unit_multiply (X : Scheme.{u}) (F : X.Modules) :
    moduleCup_godementMap X (moduleCup_godementUnit X F) ≫
      moduleCup_godementMultiply X F = 𝟙 _ := by
  apply Pi.hom_ext
  intro x
  change (moduleCup_godementMap X (moduleCup_godementUnit X F) ≫
    moduleCup_godementMultiply X F) ≫ proj X F x = (𝟙 _ : _ ⟶ _) ≫ proj X F x
  rw [Category.assoc, proj_multiply, comp_toSkyscraper, LinearMap.comp_assoc, eval_map,
    ← LinearMap.comp_assoc, eval_unit, LinearMap.id_comp, Category.id_comp]
  exact (skyscraperHomEquiv x (F.presheaf.stalk x) _).right_inv _

private theorem multiply_assoc (X : Scheme.{u}) (F : X.Modules) :
    moduleCup_godementMultiply X (moduleCup_godementObject X F) ≫
      moduleCup_godementMultiply X F =
    moduleCup_godementMap X (moduleCup_godementMultiply X F) ≫
      moduleCup_godementMultiply X F := by
  apply Pi.hom_ext
  intro x
  change (moduleCup_godementMultiply X (moduleCup_godementObject X F) ≫
    moduleCup_godementMultiply X F) ≫ proj X F x =
    (moduleCup_godementMap X (moduleCup_godementMultiply X F) ≫
      moduleCup_godementMultiply X F) ≫ proj X F x
  rw [Category.assoc, Category.assoc, proj_multiply, comp_toSkyscraper,
    comp_toSkyscraper]
  simp only [LinearMap.comp_assoc, eval_multiply, eval_map]
  rw [← LinearMap.comp_assoc (eval X _ x) ((moduleCup_godementMultiply X F).stalkLinearMap x),
    eval_multiply, LinearMap.comp_assoc]

private theorem insert_zero (X : Scheme.{u}) (F : X.Modules) (n : ℕ) :
    moduleCup_godementInsert X F n 0 =
      moduleCup_godementUnit X (moduleCup_godementIterate X F n) := by
  cases n <;> simp [moduleCup_godementInsert, moduleCup_godementIterate]

private theorem insert_succ (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i : Fin (n + 1)) :
    moduleCup_godementInsert X F (n + 1) i.succ =
      moduleCup_godementMap X (moduleCup_godementInsert X F n i) := by
  simp only [moduleCup_godementInsert, Fin.val_succ, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ↓reduceDIte]
  congr 2

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

private theorem insert_insert (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i j : Fin (n + 1)) (h : i ≤ j) :
    moduleCup_godementInsert X F n i ≫ moduleCup_godementInsert X F (n + 1) j.succ =
      moduleCup_godementInsert X F n j ≫
        moduleCup_godementInsert X F (n + 1) i.castSucc := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 0 := Fin.ext (by omega)
    subst i
    subst j
    simpa only [Fin.castSucc_zero, insert_zero, insert_succ, moduleCup_godementIterate] using
      unit_natural X (moduleCup_godementUnit X F)
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simpa only [insert_zero, insert_succ, Fin.castSucc_zero,
        moduleCup_godementIterate] using
        unit_natural X (moduleCup_godementInsert X F (n + 1) j)
    | succ i =>
      cases j using Fin.cases with
      | zero => simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at h; omega
      | succ j =>
        rw [Fin.succ_le_succ_iff] at h
        simpa only [insert_succ, Fin.castSucc_succ, ← map_comp] using
          congrArg (moduleCup_godementMap X) (ih i j h)

private theorem insert_collapse_self (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i : Fin (n + 1)) :
    moduleCup_godementInsert X F (n + 1) i.castSucc ≫
      moduleCup_godementCollapse X F n i = 𝟙 _ := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simpa only [Fin.castSucc_zero, insert_zero, collapse_zero, moduleCup_godementIterate]
      using unit_multiply X F
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.castSucc_zero, insert_zero, collapse_zero, moduleCup_godementIterate]
        using unit_multiply X (moduleCup_godementIterate X F (n + 1))
    | succ i =>
      simpa only [Fin.castSucc_succ, insert_succ, collapse_succ, ← map_comp, map_id,
        moduleCup_godementIterate] using
        congrArg (moduleCup_godementMap X) (ih i)

private theorem insert_collapse_succ (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i : Fin (n + 1)) :
    moduleCup_godementInsert X F (n + 1) i.succ ≫
      moduleCup_godementCollapse X F n i = 𝟙 _ := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    subst i
    simpa only [insert_succ, insert_zero, collapse_zero, moduleCup_godementIterate]
      using map_unit_multiply X F
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simpa only [insert_succ, insert_zero, collapse_zero, moduleCup_godementIterate]
        using map_unit_multiply X (moduleCup_godementIterate X F (n + 1))
    | succ i =>
      simpa only [insert_succ, collapse_succ, ← map_comp, map_id,
        moduleCup_godementIterate] using
        congrArg (moduleCup_godementMap X) (ih i)

private theorem collapse_collapse (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i j : Fin (n + 1)) (h : i ≤ j) :
    moduleCup_godementCollapse X F (n + 1) i.castSucc ≫
      moduleCup_godementCollapse X F n j =
    moduleCup_godementCollapse X F (n + 1) j.succ ≫
      moduleCup_godementCollapse X F n i := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    have hj : j = 0 := Fin.ext (by omega)
    subst i
    subst j
    simpa only [Fin.castSucc_zero, collapse_zero, collapse_succ, moduleCup_godementIterate]
      using multiply_assoc X F
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero =>
        simpa only [Fin.castSucc_zero, collapse_zero, collapse_succ, moduleCup_godementIterate]
          using multiply_assoc X (moduleCup_godementIterate X F (n + 1))
      | succ j =>
        simpa only [Fin.castSucc_zero, collapse_zero, collapse_succ, moduleCup_godementIterate]
          using multiply_natural X (moduleCup_godementCollapse X F n j)
    | succ i =>
      cases j using Fin.cases with
      | zero => simp only [Fin.le_def, Fin.val_succ, Fin.val_zero] at h; omega
      | succ j =>
        rw [Fin.succ_le_succ_iff] at h
        simpa only [Fin.castSucc_succ, collapse_succ, ← map_comp] using
          congrArg (moduleCup_godementMap X) (ih i j h)

private theorem insert_collapse_le (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (h : i ≤ j.castSucc) :
    moduleCup_godementInsert X F (n + 2) i.castSucc ≫
      moduleCup_godementCollapse X F (n + 1) j.succ =
    moduleCup_godementCollapse X F n j ≫ moduleCup_godementInsert X F (n + 1) i := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    have hi : i = 0 := Fin.ext (by simpa only [Fin.le_def, Fin.val_castSucc,
      Fin.val_zero] using Nat.eq_zero_of_le_zero h)
    subst i
    simpa only [Fin.castSucc_zero, insert_zero, collapse_succ, collapse_zero,
      moduleCup_godementIterate] using unit_natural X (moduleCup_godementMultiply X F)
  | succ n ih =>
    cases i using Fin.cases with
    | zero =>
      simpa only [Fin.castSucc_zero, insert_zero, collapse_succ, moduleCup_godementIterate]
        using unit_natural X (moduleCup_godementCollapse X F (n + 1) j)
    | succ i =>
      cases j using Fin.cases with
      | zero => simp only [Fin.le_def, Fin.val_succ, Fin.val_castSucc, Fin.val_zero] at h; omega
      | succ j =>
        have hij : i ≤ j.castSucc := by simpa only [Fin.castSucc_succ,
          Fin.succ_le_succ_iff] using h
        simpa only [Fin.castSucc_succ, insert_succ, collapse_succ, ← map_comp] using
          congrArg (moduleCup_godementMap X) (ih i j hij)

private theorem insert_collapse_gt (X : Scheme.{u}) (F : X.Modules) (n : ℕ)
    (i : Fin (n + 2)) (j : Fin (n + 1)) (h : j.castSucc < i) :
    moduleCup_godementInsert X F (n + 2) i.succ ≫
      moduleCup_godementCollapse X F (n + 1) j.castSucc =
    moduleCup_godementCollapse X F n j ≫ moduleCup_godementInsert X F (n + 1) i := by
  induction n with
  | zero =>
    have hj : j = 0 := Fin.ext (by omega)
    subst j
    have hi : i = (0 : Fin 1).succ := Fin.ext (by
      simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_zero] at h
      simp only [Fin.val_succ, Fin.val_zero]
      omega)
    subst i
    simpa only [Fin.castSucc_zero, collapse_zero, insert_succ, insert_zero,
      moduleCup_godementIterate] using (multiply_natural X (moduleCup_godementUnit X F)).symm
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp only [Fin.lt_def, Fin.val_zero] at h; omega
    | succ i =>
      cases j using Fin.cases with
      | zero =>
        simpa only [Fin.castSucc_zero, collapse_zero, insert_succ, moduleCup_godementIterate]
          using (multiply_natural X (moduleCup_godementInsert X F (n + 1) i)).symm
      | succ j =>
        have hij : j.castSucc < i := by simpa only [Fin.castSucc_succ,
          Fin.succ_lt_succ_iff] using h
        simpa only [Fin.castSucc_succ, insert_succ, collapse_succ, ← map_comp] using
          congrArg (moduleCup_godementMap X) (ih i j hij)

/-- The concrete Godement operators define a prefunctor from the simplex quiver.
Source: Stacks Project, Tags 0FKR and 08N8.
(blueprint: lem-sc-module-cup-godement-relations) -/
def moduleCup_godementQuiver (X : Scheme.{u}) (F : X.Modules) :
    FreeSimplexQuiver ⥤q X.Modules where
  obj n := moduleCup_godementIterate X F (n.len + 1)
  map f := match f with
    | .δ i => moduleCup_godementInsert X F _ i
    | .σ i => moduleCup_godementCollapse X F _ i

/-- The Godement operators respect the relations in the simplex presentation.
Source: Stacks Project, Tags 0FKR and 08N8, Lemma 14.34.2 (dual).
(blueprint: lem-sc-module-cup-godement-relations)
Proof: project each equation to every skyscraper factor. The stalk-skyscraper
adjunction identifies the projection with its linear stalk map followed by
stalk evaluation. Evaluation after the unit is the identity; evaluation after
T(f) is f on stalks after evaluation; evaluation after multiplication is two
successive evaluations. These formulas give functoriality of T, naturality of
unit and multiplication, both unit laws and associativity. Induct on the outer
iterate and split each index into zero or successor. If all indices are
successors, apply T to the identity one degree lower. If the left index is zero,
use unit or multiplication naturality; the adjacent mixed pairs use the two
unit laws, and the adjacent collapse pair uses associativity. The order bounds
exclude the impossible cases. These are exactly the six constructors of homRel,
so the lifted path functor sends each related pair to equal morphisms. Empty
products satisfy the same projection argument, with no point to check. -/
theorem moduleCup_godement_relations (X : Scheme.{u}) (F : X.Modules) :
    ∀ (a b : Paths FreeSimplexQuiver) (f g : a ⟶ b),
      FreeSimplexQuiver.homRel f g →
        (Paths.lift (moduleCup_godementQuiver X F)).map f =
          (Paths.lift (moduleCup_godementQuiver X F)).map g := by
  intro a b f g h
  cases h with
  | δ_comp_δ h =>
    simpa [Functor.map_comp, Paths.lift_toPath, Paths.of_map, moduleCup_godementQuiver,
      FreeSimplexQuiver.len, FreeSimplexQuiver.mk] using insert_insert X F _ _ _ h
  | δ_comp_σ_of_le h =>
    simpa [Functor.map_comp, Paths.lift_toPath, Paths.of_map, moduleCup_godementQuiver,
      FreeSimplexQuiver.len, FreeSimplexQuiver.mk] using insert_collapse_le X F _ _ _ h
  | δ_comp_σ_self =>
    simp only [Functor.map_comp, Paths.of_map, Paths.lift_toPath]
    change moduleCup_godementInsert X F _ _ ≫ moduleCup_godementCollapse X F _ _ = 𝟙 _
    exact insert_collapse_self X F _ _
  | δ_comp_σ_succ =>
    simp only [Functor.map_comp, Paths.of_map, Paths.lift_toPath]
    change moduleCup_godementInsert X F _ _ ≫ moduleCup_godementCollapse X F _ _ = 𝟙 _
    exact insert_collapse_succ X F _ _
  | δ_comp_σ_of_gt h =>
    simpa [Functor.map_comp, Paths.lift_toPath, Paths.of_map, moduleCup_godementQuiver,
      FreeSimplexQuiver.len, FreeSimplexQuiver.mk] using insert_collapse_gt X F _ _ _ h
  | σ_comp_σ h =>
    simpa [Functor.map_comp, Paths.lift_toPath, Paths.of_map, moduleCup_godementQuiver,
      FreeSimplexQuiver.len, FreeSimplexQuiver.mk] using collapse_collapse X F _ _ _ h

end
end AlgebraicGeometry.Scheme.Modules
