/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import WeilConjectures.CategoryTheory.Sites.SemiSimplicialHypercover.Basic

/-!
# Refining a hypercover along covers of its terms

Let `U` be a semi-simplicial hypercover of a site `(C, J)`, where `C` has finite limits, and let
`π k : W k ⟶ U.obj k` be coverings (single morphisms generating covering sieves), one for each
`k`. We construct a hypercover `V` with a morphism `V ⟶ U` whose components factor through the
`π k` (`CategoryTheory.SemiSimplicialObject.refinement`). It is the relative coskeleton
construction of [Stacks, Tag 0DAX]: inductively,

* `V₀ = W₀`, and
* `V_{n + 1} = M_{n + 1}(V) ×_{M_{n + 1}(U)} W_{n + 1}`,

where `M_{n + 1}` denotes the matching object (corepresenting compatible families of faces) and
`W_{n + 1}` maps to `M_{n + 1}(U)` through `π (n + 1)` and the matching map of `U`. Since the
construction only uses finite products, equalizers and pullbacks, the terms of `V` satisfy every
property of objects which holds for the `U.obj k`, `W k` and is stable under these limits
(`CategoryTheory.SemiSimplicialObject.refinement_obj_prop`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.SemiSimplicialObject

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

namespace Refinement

variable (U : SemiSimplicialObject C) (W : ℕ → C) (π : ∀ k, W k ⟶ U.obj k)

/-- The data of the levels `n` and `n + 1` of the refinement: the objects `A = V_n` and
`B = V_{n + 1}`, the face maps between them, and the maps to `U` and to `W`. -/
structure Stage (n : ℕ) where
  /-- The object `V_n`. -/
  A : C
  /-- The object `V_{n + 1}`. -/
  B : C
  /-- The face maps `V_{n + 1} ⟶ V_n`. -/
  d : Fin (n + 2) → (B ⟶ A)
  /-- The map `V_n ⟶ U_n`. -/
  fA : A ⟶ U.obj n
  /-- The map `V_{n + 1} ⟶ U_{n + 1}`. -/
  fB : B ⟶ U.obj (n + 1)
  comm (i : Fin (n + 2)) : d i ≫ fA = fB ≫ U.δ n i
  /-- The map `V_n ⟶ W_n`. -/
  ρA : A ⟶ W n
  ρA_π : ρA ≫ π n = fA
  /-- The map `V_{n + 1} ⟶ W_{n + 1}`. -/
  ρB : B ⟶ W (n + 1)
  ρB_π : ρB ≫ π (n + 1) = fB

namespace Stage

variable {U W π} {n : ℕ} (s : Stage U W π n)

/-- The first of the two maps `∏ᵢ V_{n + 1} ⟶ ∏_{i ≤ j} V_n` whose equalizer is the matching
object `M_{n + 2}(V)`. -/
noncomputable def matchingLeft :
    ∏ᶜ (fun _ : Fin (n + 3) ↦ s.B) ⟶ ∏ᶜ (fun _ : MatchingIndex n ↦ s.A) :=
  Pi.lift fun p ↦ Pi.π _ p.1.2.succ ≫ s.d p.1.1

/-- The second of the two maps `∏ᵢ V_{n + 1} ⟶ ∏_{i ≤ j} V_n` whose equalizer is the matching
object `M_{n + 2}(V)`. -/
noncomputable def matchingRight :
    ∏ᶜ (fun _ : Fin (n + 3) ↦ s.B) ⟶ ∏ᶜ (fun _ : MatchingIndex n ↦ s.A) :=
  Pi.lift fun p ↦ Pi.π _ p.1.1.castSucc ≫ s.d p.1.2

/-- The matching object `M_{n + 2}(V)`. -/
noncomputable abbrev matching : C := equalizer s.matchingLeft s.matchingRight

/-- The projections `M_{n + 2}(V) ⟶ V_{n + 1}`. -/
noncomputable def matchingπ (i : Fin (n + 3)) : s.matching ⟶ s.B :=
  equalizer.ι s.matchingLeft s.matchingRight ≫ Pi.π _ i

@[reassoc (attr := simp)]
lemma matchingLeft_π (p : MatchingIndex n) :
    s.matchingLeft ≫ Pi.π _ p = Pi.π _ p.1.2.succ ≫ s.d p.1.1 := by
  simp [matchingLeft]

@[reassoc (attr := simp)]
lemma matchingRight_π (p : MatchingIndex n) :
    s.matchingRight ≫ Pi.π _ p = Pi.π _ p.1.1.castSucc ≫ s.d p.1.2 := by
  simp [matchingRight]

lemma matchingπ_comp_d {i j : Fin (n + 2)} (h : i ≤ j) :
    s.matchingπ j.succ ≫ s.d i = s.matchingπ i.castSucc ≫ s.d j := by
  have := equalizer.condition s.matchingLeft s.matchingRight =≫ Pi.π _ ⟨(i, j), h⟩
  simp only [Category.assoc, matchingLeft_π, matchingRight_π] at this
  simpa only [matchingπ, Category.assoc] using this

/-- The morphism to the matching object given by a compatible family. -/
noncomputable def matchingLift {T : C} (x : Fin (n + 3) → (T ⟶ s.B))
    (hx : ∀ i j : Fin (n + 2), i ≤ j → x j.succ ≫ s.d i = x i.castSucc ≫ s.d j) :
    T ⟶ s.matching :=
  equalizer.lift (Pi.lift x) (Pi.hom_ext _ _ fun p ↦ by
    simpa [matchingLeft, matchingRight] using hx p.1.1 p.1.2 p.2)

@[reassoc (attr := simp)]
lemma matchingLift_π {T : C} (x : Fin (n + 3) → (T ⟶ s.B))
    (hx : ∀ i j : Fin (n + 2), i ≤ j → x j.succ ≫ s.d i = x i.castSucc ≫ s.d j)
    (i : Fin (n + 3)) : s.matchingLift x hx ≫ s.matchingπ i = x i := by
  simp [matchingLift, matchingπ]

lemma compatible_matchingπ_comp_fB :
    U.Compatible (fun i ↦ s.matchingπ i ≫ s.fB) := by
  intro i j hij
  rw [Category.assoc, Category.assoc, ← s.comm, ← s.comm, ← Category.assoc,
    s.matchingπ_comp_d hij, Category.assoc]

/-- The map `M_{n + 2}(V) ⟶ M_{n + 2}(U)`. -/
noncomputable def toMatchingU : s.matching ⟶ U.matching (n + 1) :=
  U.matchingLift _ s.compatible_matchingπ_comp_fB

@[reassoc (attr := simp)]
lemma toMatchingU_π (i : Fin (n + 3)) :
    s.toMatchingU ≫ U.matchingπ (n + 1) i = s.matchingπ i ≫ s.fB := by
  simp [toMatchingU]

/-- The next stage: `V_{n + 2} = M_{n + 2}(V) ×_{M_{n + 2}(U)} W_{n + 2}`. -/
noncomputable def next : Stage U W π (n + 1) where
  A := s.B
  B := pullback s.toMatchingU (π (n + 2) ≫ U.toMatching (n + 1))
  d i := pullback.fst _ _ ≫ s.matchingπ i
  fA := s.fB
  fB := pullback.snd _ _ ≫ π (n + 2)
  comm i := by
    have := pullback.condition (f := s.toMatchingU) (g := π (n + 2) ≫ U.toMatching (n + 1)) =≫
      U.matchingπ (n + 1) i
    simp only [Category.assoc, toMatchingU_π, toMatching_π] at this
    simpa only [Category.assoc] using this
  ρA := s.ρB
  ρA_π := s.ρB_π
  ρB := pullback.snd _ _
  ρB_π := rfl

lemma next_d_comp_d {i j : Fin (n + 2)} (h : i ≤ j) :
    s.next.d j.succ ≫ s.d i = s.next.d i.castSucc ≫ s.d j := by
  simp only [next, Category.assoc, s.matchingπ_comp_d h]

end Stage

/-- The stage `0`: `V₀ = W₀` and `V₁ = (V₀ × V₀) ×_{U₀ × U₀} W₁`. -/
noncomputable def stageZero : Stage U W π 0 :=
  let toM : ∏ᶜ (fun _ : Fin 2 ↦ W 0) ⟶ U.matching 0 :=
    U.matchingLift (fun i ↦ Pi.π _ i ≫ π 0) (U.compatible_zero _)
  { A := W 0
    B := pullback toM (π 1 ≫ U.toMatching 0)
    d i := pullback.fst _ _ ≫ Pi.π _ i
    fA := π 0
    fB := pullback.snd _ _ ≫ π 1
    comm i := by
      have := pullback.condition (f := toM) (g := π 1 ≫ U.toMatching 0) =≫ U.matchingπ 0 i
      simp only [Category.assoc, toM, matchingLift_π, toMatching_π] at this
      simpa only [Category.assoc] using this
    ρA := 𝟙 _
    ρA_π := Category.id_comp _
    ρB := pullback.snd _ _
    ρB_π := rfl }

/-- The stages of the refinement. -/
noncomputable def stage : (n : ℕ) → Stage U W π n
  | 0 => stageZero U W π
  | n + 1 => (stage n).next

end Refinement

open Refinement

variable (U : SemiSimplicialObject C) (W : ℕ → C) (π : ∀ k, W k ⟶ U.obj k)

/-- The refinement of a semi-simplicial object `U` along morphisms `π k : W k ⟶ U.obj k`: the
relative coskeleton `V₀ = W₀`, `V_{n + 1} = M_{n + 1}(V) ×_{M_{n + 1}(U)} W_{n + 1}`. -/
noncomputable def refinement : SemiSimplicialObject C where
  obj n := (stage U W π n).A
  δ n i := (stage U W π n).d i
  δ_comp_δ n _ _ h := (stage U W π n).next_d_comp_d h

/-- The morphism from the refinement. -/
noncomputable def refinementHom : refinement U W π ⟶ U where
  app n := (stage U W π n).fA
  app_δ n i := ((stage U W π n).comm i).symm

/-- The components of the refinement factor through the `π k`. -/
noncomputable def refinementToW (n : ℕ) : (refinement U W π).obj n ⟶ W n :=
  (stage U W π n).ρA

@[reassoc (attr := simp)]
lemma refinementToW_π (n : ℕ) :
    refinementToW U W π n ≫ π n = (refinementHom U W π).app n :=
  (stage U W π n).ρA_π

section Hypercover

variable {J : GrothendieckTopology C}

omit [HasFiniteLimits C] in
/-- If `π' : W' ⟶ Z` generates a covering sieve, then every morphism `h : T ⟶ Z` lifts locally
along `π'`. -/
lemma exists_lift_mem {W' Z T : C} {π' : W' ⟶ Z}
    (hπ : Sieve.ofArrows (fun _ : Unit ↦ W') (fun _ ↦ π') ∈ J Z) (h : T ⟶ Z) :
    { arrows := fun T' g ↦ ∃ l : T' ⟶ W', l ≫ π' = g ≫ h
      downward_closed := by
        rintro T' T'' g ⟨l, hl⟩ g'
        exact ⟨g' ≫ l, by rw [Category.assoc, hl, Category.assoc]⟩ : Sieve T } ∈ J T := by
  refine J.superset_covering ?_ (J.pullback_stable h hπ)
  intro T' g hg
  obtain ⟨_, a, ha⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
  exact ⟨a, ha.symm⟩

variable {U W π}

/-- The local lifting property of the refinement, for a stage `s` and its successor. -/
lemma Refinement.Stage.liftSieve_mem (hU : U.IsHypercover J)
    (hπ : ∀ k, Sieve.ofArrows (fun _ : Unit ↦ W k) (fun _ ↦ π k) ∈ J (U.obj k))
    {n : ℕ} (s : Stage U W π n) {T : C} (x : Fin (n + 3) → (T ⟶ s.B))
    (hx : ∀ i j : Fin (n + 2), i ≤ j → x j.succ ≫ s.d i = x i.castSucc ≫ s.d j) :
    { arrows := fun T' g ↦ ∃ y : T' ⟶ s.next.B, ∀ i, y ≫ s.next.d i = g ≫ x i
      downward_closed := by
        rintro T' T'' g ⟨y, hy⟩ g'
        exact ⟨g' ≫ y, fun i ↦ (Category.assoc _ _ _).trans
          ((congrArg _ (hy i)).trans (Category.assoc _ _ _).symm)⟩ : Sieve T } ∈ J T := by
  have hxU : U.Compatible (fun i ↦ x i ≫ s.fB) := by
    intro i j hij
    rw [Category.assoc, Category.assoc, ← s.comm, ← s.comm, reassoc_of% (hx i j hij)]
  refine J.transitive (hU.liftSieve_mem _ hxU) _ fun T' g ⟨y, hy⟩ ↦ ?_
  refine J.superset_covering ?_ (exists_lift_mem (hπ (n + 2)) y)
  rintro T'' g' ⟨l, hl⟩
  refine ⟨pullback.lift (g' ≫ g ≫ s.matchingLift x hx) l ?_, fun i ↦ ?_⟩
  · refine U.matching_hom_ext fun i ↦ ?_
    simp only [Category.assoc, Stage.toMatchingU_π, Stage.matchingLift_π_assoc,
      toMatching_π, reassoc_of% hl, hy]
  · refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (g' ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (g ≫ ·) (s.matchingLift_π x hx i)))).trans (Category.assoc _ _ _).symm)

/-- The local lifting property of the refinement in degree `0`. -/
lemma Refinement.stageZero_liftSieve_mem (hU : U.IsHypercover J)
    (hπ : ∀ k, Sieve.ofArrows (fun _ : Unit ↦ W k) (fun _ ↦ π k) ∈ J (U.obj k))
    {T : C} (x : Fin 2 → (T ⟶ W 0)) :
    { arrows := fun T' g ↦ ∃ y : T' ⟶ (stageZero U W π).B,
        ∀ i, y ≫ (stageZero U W π).d i = g ≫ x i
      downward_closed := by
        rintro T' T'' g ⟨y, hy⟩ g'
        exact ⟨g' ≫ y, fun i ↦ (Category.assoc _ _ _).trans
          ((congrArg _ (hy i)).trans (Category.assoc _ _ _).symm)⟩ : Sieve T } ∈ J T := by
  refine J.transitive (hU.liftSieve_mem (fun i ↦ x i ≫ π 0) (U.compatible_zero _)) _
    fun T' g ⟨y, hy⟩ ↦ ?_
  refine J.superset_covering ?_ (exists_lift_mem (hπ 1) y)
  rintro T'' g' ⟨l, hl⟩
  refine ⟨pullback.lift (g' ≫ g ≫ Pi.lift x) l ?_, fun i ↦ ?_⟩
  · refine U.matching_hom_ext fun i ↦ ?_
    simp only [Category.assoc, matchingLift_π, Pi.lift_comp_π_assoc, toMatching_π,
      reassoc_of% hl, hy]
  · refine (pullback.lift_fst_assoc _ _ _ _).trans ?_
    exact (Category.assoc _ _ _).trans ((congrArg (g' ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (g ≫ ·) (Pi.lift_comp_π x i)))).trans (Category.assoc _ _ _).symm)

/-- The refinement of a hypercover along coverings `π k : W k ⟶ U.obj k` is a hypercover. -/
lemma IsHypercover.refinement (hU : U.IsHypercover J)
    (hπ : ∀ k, Sieve.ofArrows (fun _ : Unit ↦ W k) (fun _ ↦ π k) ∈ J (U.obj k)) :
    (refinement U W π).IsHypercover J where
  coverSieve_mem T := by
    refine J.transitive (hU.coverSieve_mem T) _ fun T' g ⟨y⟩ ↦ ?_
    refine J.superset_covering ?_ (exists_lift_mem (hπ 0) y)
    rintro T'' g' ⟨l, -⟩
    exact ⟨l⟩
  liftSieve_mem {n} T x hx := by
    cases n with
    | zero => exact Refinement.stageZero_liftSieve_mem hU hπ x
    | succ m => exact (stage U W π m).liftSieve_mem hU hπ x hx


end Hypercover

section Closure

variable (P : ObjectProperty C) [P.IsClosedUnderFiniteProducts]
  [P.IsClosedUnderLimitsOfShape WalkingParallelPair] [P.IsClosedUnderLimitsOfShape WalkingCospan]

omit [P.IsClosedUnderLimitsOfShape WalkingCospan] in
variable {U} in
lemma prop_matching (hU : ∀ k, P (U.obj k)) (n : ℕ) : P (U.matching n) := by
  cases n with
  | zero => exact P.prop_product fun _ ↦ hU 0
  | succ m =>
    refine P.prop_limit _ fun j ↦ ?_
    cases j
    · exact P.prop_product fun _ ↦ hU _
    · exact P.prop_product fun _ ↦ hU _

variable {U W π} in
lemma prop_stage (hU : ∀ k, P (U.obj k)) (hW : ∀ k, P (W k)) (n : ℕ) :
    P (stage U W π n).A ∧ P (stage U W π n).B := by
  induction n with
  | zero =>
    refine ⟨hW 0, P.prop_limit _ fun j ↦ ?_⟩
    rcases j with (_ | (_ | _))
    · exact prop_matching P hU 0
    · exact P.prop_product fun _ ↦ hW 0
    · exact hW 1
  | succ n ih =>
    refine ⟨ih.2, P.prop_limit _ fun j ↦ ?_⟩
    rcases j with (_ | (_ | _))
    · exact prop_matching P hU (n + 1)
    · refine P.prop_limit _ fun j ↦ ?_
      cases j
      · exact P.prop_product fun _ ↦ ih.2
      · exact P.prop_product fun _ ↦ ih.1
    · exact hW (n + 2)

variable {U W π} in
/-- The terms of the refinement satisfy every property of objects that holds for the terms of
`U` and the `W k` and is stable under finite products, equalizers and pullbacks. -/
lemma refinement_obj_prop (hU : ∀ k, P (U.obj k)) (hW : ∀ k, P (W k)) (n : ℕ) :
    P ((refinement U W π).obj n) :=
  (prop_stage P hU hW n).1

end Closure

end CategoryTheory.SemiSimplicialObject

namespace CategoryTheory.ObjectProperty

open Limits

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] (P : ObjectProperty C)
  [P.IsClosedUnderIsomorphisms] [P.IsClosedUnderLimitsOfShape (Discrete.{0} PEmpty)]
  [P.IsClosedUnderLimitsOfShape WalkingCospan]

/-- A property of objects which is stable under isomorphisms, terminal objects and pullbacks is
stable under all finite limits. -/
lemma isClosedUnderLimitsOfShape_of_terminal_of_pullback (J : Type) [SmallCategory J]
    [FinCategory J] : P.IsClosedUnderLimitsOfShape J := by
  have : HasTerminal P.FullSubcategory := inferInstance
  have : HasPullbacks P.FullSubcategory := inferInstance
  have : HasFiniteLimits P.FullSubcategory := hasFiniteLimits_of_hasTerminal_and_pullbacks
  have : PreservesFiniteLimits P.ι := preservesFiniteLimits_of_preservesTerminal_and_pullbacks _
  exact P.isClosedUnderLimitsOfShape_of_preservesLimitsOfShape_ι J

/-- A property of objects which is stable under isomorphisms, terminal objects and pullbacks is
stable under finite products. -/
lemma isClosedUnderFiniteProducts_of_terminal_of_pullback : P.IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape J _ := by
    have := Fintype.ofFinite J
    exact P.isClosedUnderLimitsOfShape_of_terminal_of_pullback _

end CategoryTheory.ObjectProperty
