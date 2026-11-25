/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful

/-! # The explicit inverse system obtained by termwise pushforward

Source: Stacks Project, Cohomology of Schemes, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-system-pushforward-functor).
-/

@[expose] public section

universe v
open CategoryTheory Opposite
namespace AlgebraicGeometry
noncomputable section
set_option autoImplicit false

variable {X : Scheme.{v}} {T : ℕ → Scheme.{v}} {i : ∀ n, T n ⟶ T (n + 1)}
  (j : ∀ n, T n ⟶ X) (hi : ∀ n, i n ≫ j (n + 1) = j n)
  (ai : ∀ n, Scheme.Modules.tensorPullback (i n) ⊣ Scheme.Modules.pushforward (i n))

/-- The canonical comparison of the two ways to push a module from level `n` to `X`.
Source: Stacks, Remark 088F (blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
def thickeningPushforwardComparison (n : ℕ) :
    Scheme.Modules.pushforward (i n) ⋙ Scheme.Modules.pushforward (j (n + 1)) ≅
      Scheme.Modules.pushforward (j n) :=
  Scheme.Modules.pushforwardComp (i n) (j (n + 1)) ≪≫
    Scheme.Modules.pushforwardCongr (hi n)

/-- Push the adjoint of the pullback comparison forward to obtain an adjacent transition.
Source: Stacks, Remark 088F (blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
def thickeningPushforwardTransition (M : CoherentThickeningSystem T i) (n : ℕ) :
    (Scheme.Modules.pushforward (j (n + 1))).obj (M.term (n + 1)) ⟶
      (Scheme.Modules.pushforward (j n)).obj (M.term n) :=
  (Scheme.Modules.pushforward (j (n + 1))).map
      ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
    (thickeningPushforwardComparison j hi n).hom.app (M.term n)

/-- Naturality follows by applying the adjunction hom equivalence to compatibility.
Source: Stacks, Remark 088F (blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
theorem thickeningPushforwardTransition_naturality
    {M N : CoherentThickeningSystem T i} (u : M ⟶ N) (n : ℕ) :
    thickeningPushforwardTransition j hi ai M n ≫
        (Scheme.Modules.pushforward (j n)).map (u.app n) =
      (Scheme.Modules.pushforward (j (n + 1))).map (u.app (n + 1)) ≫
        thickeningPushforwardTransition j hi ai N n := by
  have h := congrArg ((ai n).homEquiv _ _) (u.compatibility n)
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left] at h
  dsimp only [thickeningPushforwardTransition]
  rw [Category.assoc, ← (thickeningPushforwardComparison j hi n).hom.naturality]
  simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp]
  rw [h]

/-- Termwise pushforward of a compatible family.
Source: Stacks, Remark 088F (blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
def thickeningSystemPushforwardMap {M N : CoherentThickeningSystem T i} (u : M ⟶ N) :
    Functor.ofOpSequence
      (X := fun n ↦ (Scheme.Modules.pushforward (j n)).obj (M.term n))
      (thickeningPushforwardTransition j hi ai M) ⟶
      Functor.ofOpSequence
      (X := fun n ↦ (Scheme.Modules.pushforward (j n)).obj (N.term n))
      (thickeningPushforwardTransition j hi ai N) :=
  NatTrans.ofOpSequence
    (fun n ↦ (Scheme.Modules.pushforward (j n)).map (u.app n))
    (fun n ↦ by
      simpa only [Functor.ofOpSequence_map_homOfLE_succ] using
        thickeningPushforwardTransition_naturality j hi ai u n)

/-- The explicit pushforward functor, with transitions composed from the adjacent maps.
No module data are selected from an existence theorem.
Source: Stacks, Remark 088F (blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
def thickeningSystemPushforward : CoherentThickeningSystem T i ⥤ (ℕᵒᵖ ⥤ X.Modules) where
  obj M := Functor.ofOpSequence
      (X := fun n ↦ (Scheme.Modules.pushforward (j n)).obj (M.term n))
      (thickeningPushforwardTransition j hi ai M)
  map u := thickeningSystemPushforwardMap j hi ai u
  map_id M := by
    apply NatTrans.ext
    funext n
    exact (Scheme.Modules.pushforward (j n.unop)).map_id _
  map_comp u w := by
    apply NatTrans.ext
    funext n
    exact (Scheme.Modules.pushforward (j n.unop)).map_comp _ _

/-- Evaluation of the explicit functor is termwise pushforward.
Source: Stacks, Remark 088F (blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
def thickeningSystemPushforwardEvaluation (n : ℕ) :
    thickeningSystemPushforward j hi ai ⋙
        (CategoryTheory.evaluation ℕᵒᵖ X.Modules).obj (op n) ≅
      CoherentThickeningSystem.evaluation T i n ⋙ Scheme.Modules.pushforward (j n) :=
  Iso.refl _

/-- The explicit functor has the specified adjacent transition.
Source: Stacks, Remark 088F (blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
theorem thickeningSystemPushforward_transition (M : CoherentThickeningSystem T i) (n : ℕ) :
    ((thickeningSystemPushforward j hi ai).obj M).map (homOfLE (Nat.le_succ n)).op =
      (Scheme.Modules.pushforward (j (n + 1))).map
          ((ai n).homEquiv _ _ (M.comparison n).hom) ≫
        (Scheme.Modules.pushforwardComp (i n) (j (n + 1))).hom.app (M.term n) ≫
        (Scheme.Modules.pushforwardCongr (hi n)).hom.app (M.term n) := by
  change (Functor.ofOpSequence
    (X := fun k ↦ (Scheme.Modules.pushforward (j k)).obj (M.term k))
    (thickeningPushforwardTransition j hi ai M)).map _ = _
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  rfl

/-- Termwise closed pushforward detects the compatibility of a family.
Source: Stacks, Lemma 087T and Remark 088F
(blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
theorem thickeningPushforward_compatibility [∀ n, IsClosedImmersion (j n)]
    {M N : CoherentThickeningSystem T i} (u : ∀ n, M.term n ⟶ N.term n)
    (h : ∀ n, thickeningPushforwardTransition j hi ai M n ≫
        (Scheme.Modules.pushforward (j n)).map (u n) =
      (Scheme.Modules.pushforward (j (n + 1))).map (u (n + 1)) ≫
        thickeningPushforwardTransition j hi ai N n) (n : ℕ) :
    (M.comparison n).hom ≫ u n =
      (Scheme.Modules.tensorPullback (i n)).map (u (n + 1)) ≫ (N.comparison n).hom := by
  apply ((ai n).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left]
  apply (closedImmersion_pushforward_fullyFaithful (j (n + 1))).2 _ _ |>.1
  apply (cancel_mono ((thickeningPushforwardComparison j hi n).hom.app (N.term n))).mp
  have hn := h n
  dsimp only [thickeningPushforwardTransition] at hn
  rw [Category.assoc, ← (thickeningPushforwardComparison j hi n).hom.naturality] at hn
  simpa only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp] using hn

/-- Full faithfulness is proved by uniquely lifting each component and detecting its
compatibility with the adjunction hom equivalence. No object lifting is used here.
Source: Stacks, Lemma 087T and Remark 088F
(blueprint: lem-weil-pbc-thickening-system-pushforward-functor). -/
theorem thickeningSystemPushforward_fullyFaithful [∀ n, IsClosedImmersion (j n)] :
    (thickeningSystemPushforward j hi ai).Full ∧
      (thickeningSystemPushforward j hi ai).Faithful := by
  classical
  have hbij (n : ℕ) := (closedImmersion_pushforward_fullyFaithful (j n)).2
  constructor
  · refine ⟨fun {M N} α ↦ ?_⟩
    have lifts : ∀ n, ∃ u : M.term n ⟶ N.term n,
        (Scheme.Modules.pushforward (j n)).map u = α.app (op n) :=
      fun n ↦ (hbij n _ _).2 (α.app (op n))
    choose u hu using lifts
    let w : M ⟶ N := ⟨u, fun n ↦ thickeningPushforward_compatibility j hi ai u
      (fun k ↦ by
        rw [hu k, hu (k + 1)]
        simpa only [thickeningSystemPushforward,
          Functor.ofOpSequence_map_homOfLE_succ] using
          α.naturality (homOfLE (Nat.le_succ k)).op) n⟩
    refine ⟨w, ?_⟩
    apply NatTrans.ext
    funext n
    exact hu n.unop
  · refine ⟨fun {M N} u w h ↦ ?_⟩
    have he : u.app = w.app := by
      funext n
      apply (hbij n _ _).1
      exact congrArg (fun α ↦ α.app (op n)) h
    cases u
    cases w
    cases he
    rfl

end
end AlgebraicGeometry
