/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Exact.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace ModuleCat

variable {R : Type u} [Ring R] {J : Type} [SmallCategory J]

/-- The cone over `G : J ⥤ ModuleCat R` whose apex is the module of compatible families
`sectionsSubmodule G`, with the evaluation maps as projections. -/
def sectionsCone (G : J ⥤ ModuleCat.{w} R) : Cone G where
  pt := ModuleCat.of R (sectionsSubmodule G)
  π :=
    { app j := ofHom ((LinearMap.proj j).comp (sectionsSubmodule G).subtype)
      naturality _ _ f := by
        ext x
        exact (x.2 f).symm }

@[simp]
lemma sectionsCone_π_app_apply (G : J ⥤ ModuleCat.{w} R) (j : J)
    (x : sectionsSubmodule G) : (sectionsCone G).π.app j x = (x : ∀ j, G.obj j) j :=
  rfl

end ModuleCat

namespace CategoryTheory

/-- A sequence of elements of a tower of modules compatible with the successor transitions
is compatible with all transitions. -/
lemma tower_map_homOfLE_of_succ {R : Type u} [Ring R] {F : ℕᵒᵖ ⥤ ModuleCat.{v} R}
    (s : ∀ n : ℕ, F.obj (Opposite.op n))
    (hs : ∀ n : ℕ, F.map (homOfLE (Nat.le_add_right n 1)).op (s (n + 1)) = s n)
    {m n : ℕ} (h : n ≤ m) : F.map (homOfLE h).op (s m) = s n := by
  induction m, h using Nat.le_induction with
  | base => simp [homOfLE_refl]
  | succ m hnm ih =>
    rw [← homOfLE_comp hnm (Nat.le_add_right m 1), op_comp, Functor.map_comp,
      ModuleCat.comp_apply, hs, ih]

/-- Levelwise maps of towers of modules commuting with the successor transitions commute
with all transitions. -/
lemma tower_map_homOfLE_comm_of_succ {R : Type u} [Ring R]
    {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} {G : ℕᵒᵖ ⥤ ModuleCat.{w} R}
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x))
    {m n : ℕ} (h : n ≤ m) (x : F.obj (Opposite.op m)) :
    G.map (homOfLE h).op (α m x) = α n (F.map (homOfLE h).op x) := by
  induction m, h using Nat.le_induction with
  | base => simp [homOfLE_refl]
  | succ m hnm ih =>
    rw [← homOfLE_comp hnm (Nat.le_add_right m 1), op_comp, Functor.map_comp,
      Functor.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply, hα, ih]

/-- Every morphism `op m ⟶ op n` in `ℕᵒᵖ` is the opposite of `homOfLE`. -/
lemma nat_op_hom_eq_homOfLE {m n : ℕ} (f : Opposite.op m ⟶ Opposite.op n) :
    f = (homOfLE (leOfHom f.unop)).op :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- The element of the inverse limit of a tower of modules determined by a sequence
compatible with the successor transitions. -/
noncomputable def towerLimitMk {R : Type u} [Ring R] {F : ℕᵒᵖ ⥤ ModuleCat.{v} R}
    (s : ∀ n : ℕ, F.obj (Opposite.op n))
    (hs : ∀ n : ℕ, F.map (homOfLE (Nat.le_add_right n 1)).op (s (n + 1)) = s n) :
    ↑(limit F) :=
  limit.lift F (ModuleCat.sectionsCone F) (⟨fun j ↦ s j.unop, fun {j j'} f ↦ by
    obtain ⟨m⟩ := j
    obtain ⟨n⟩ := j'
    rw [nat_op_hom_eq_homOfLE f]
    exact tower_map_homOfLE_of_succ s hs _⟩ : ModuleCat.sectionsSubmodule F)

@[simp]
lemma limit_π_towerLimitMk {R : Type u} [Ring R] {F : ℕᵒᵖ ⥤ ModuleCat.{v} R}
    (s : ∀ n : ℕ, F.obj (Opposite.op n))
    (hs : ∀ n : ℕ, F.map (homOfLE (Nat.le_add_right n 1)).op (s (n + 1)) = s n) (n : ℕ) :
    limit.π F (Opposite.op n) (towerLimitMk s hs) = s n :=
  limit.lift_π_apply _ _ _

/-- The linear map on inverse limits of towers of modules induced by levelwise linear maps
commuting with the successor transitions. -/
noncomputable def towerLimitMap {R : Type u} [Ring R]
    {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} {G : ℕᵒᵖ ⥤ ModuleCat.{w} R}
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x)) :
    ↑(limit F) →ₗ[R] ↑(limit G) :=
  ((limit.lift G (ModuleCat.sectionsCone G)).hom : ModuleCat.sectionsSubmodule G →ₗ[R] _) ∘ₗ
    LinearMap.codRestrict (ModuleCat.sectionsSubmodule G)
      (LinearMap.pi fun j ↦ α j.unop ∘ₗ (limit.π F j).hom) fun x {j j'} f ↦ by
        obtain ⟨m⟩ := j
        obtain ⟨n⟩ := j'
        rw [nat_op_hom_eq_homOfLE f]
        exact (tower_map_homOfLE_comm_of_succ α hα _ _).trans
          (congrArg (α n) (limit.w_apply F _ x))

@[simp]
lemma limit_π_towerLimitMap {R : Type u} [Ring R]
    {F : ℕᵒᵖ ⥤ ModuleCat.{v} R} {G : ℕᵒᵖ ⥤ ModuleCat.{w} R}
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x))
    (n : ℕ) (x : ↑(limit F)) :
    limit.π G (Opposite.op n) (towerLimitMap α hα x) = α n (limit.π F (Opposite.op n) x) :=
  limit.lift_π_apply _ _ _

/-- Componentwise maps on inverse limits exist and are characterized by their
coordinate projections, under the stated naturality hypotheses.
Source: the componentwise construction in Stacks Project, Algebra Lemma 03CA.
(blueprint: new-tower-limit-induced-maps).
-/
theorem tower_limit_induced_maps
    (R : Type u) [CommRing R]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} R) (G : ℕᵒᵖ ⥤ ModuleCat.{w} R)
    (H : ℕᵒᵖ ⥤ ModuleCat.{t} R)
    (α : ∀ n : ℕ, F.obj (Opposite.op n) →ₗ[R] G.obj (Opposite.op n))
    (β : ∀ n : ℕ, G.obj (Opposite.op n) →ₗ[R] H.obj (Opposite.op n))
    (hα : ∀ (n : ℕ) (x : F.obj (Opposite.op (n + 1))),
      G.map (homOfLE (Nat.le_add_right n 1)).op (α (n + 1) x) =
        α n (F.map (homOfLE (Nat.le_add_right n 1)).op x))
    (hβ : ∀ (n : ℕ) (x : G.obj (Opposite.op (n + 1))),
      H.map (homOfLE (Nat.le_add_right n 1)).op (β (n + 1) x) =
        β n (G.map (homOfLE (Nat.le_add_right n 1)).op x)) :
    ∃ (U : ↑(limit F) →ₗ[R] ↑(limit G)) (V : ↑(limit G) →ₗ[R] ↑(limit H)),
      (∀ (n : ℕ) (x : ↑(limit F)),
        limit.π G (Opposite.op n) (U x) = α n (limit.π F (Opposite.op n) x)) ∧
      (∀ (n : ℕ) (x : ↑(limit G)),
        limit.π H (Opposite.op n) (V x) = β n (limit.π G (Opposite.op n) x)) := by
  exact ⟨towerLimitMap α hα, towerLimitMap β hβ, limit_π_towerLimitMap α hα,
    limit_π_towerLimitMap β hβ⟩

end CategoryTheory
