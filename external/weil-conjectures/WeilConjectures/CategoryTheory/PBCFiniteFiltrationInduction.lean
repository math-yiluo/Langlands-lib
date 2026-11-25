/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.PBCFiltration
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Finite filtration induction

Source: the blueprint of the Weil conjectures, chapter `chap-Proper-base-change`,
unit `theorem-proper-base-change-classical-pro`, node `lem-sp-finite-filtration-induction`
(blueprint: lem-sp-finite-filtration-induction); Stacks Project, Homology,
Definition 0121 (`definition-filtered`), the paragraph defining `gr` before Lemma 05SP,
and Lemma 0127 (`lemma-characterize-strict`).
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace PBCFilteredObject

/-- The map induced by a filtered morphism on its `p`-th filtration steps.
Source: Stacks Project, Homology, Definition 0121 (3) and the diagram in Lemma 0127.
The factorization is unique because the target subobject inclusion is monic.
(blueprint: lem-sp-finite-filtration-induction) -/
noncomputable def restriction {A B : PBCFilteredObject C} (f : Hom A B) (p : ℤ) :
    (A.filtration.step p : C) ⟶ (B.filtration.step p : C) :=
  Classical.choose (f.preserves p)

private theorem restriction_arrow {A B : PBCFilteredObject C} (f : Hom A B) (p : ℤ) :
    restriction f p ≫ (B.filtration.step p).arrow =
      (A.filtration.step p).arrow ≫ f.hom :=
  Classical.choose_spec (f.preserves p)

private theorem restriction_naturality {A B : PBCFilteredObject C} (f : Hom A B) (p : ℤ) :
    Subobject.ofLE (A.filtration.step (p + 1)) (A.filtration.step p)
        (A.filtration.antitone_step (by omega)) ≫ restriction f p =
      restriction f (p + 1) ≫ Subobject.ofLE (B.filtration.step (p + 1))
        (B.filtration.step p) (B.filtration.antitone_step (by omega)) := by
  rw [← cancel_mono (B.filtration.step p).arrow]
  simp only [Category.assoc, restriction_arrow, Subobject.ofLE_arrow]
  rw [← Category.assoc, Subobject.ofLE_arrow]

/-- Existence of the map induced on the graded pieces by a filtered morphism.
Source: Stacks Project, Homology, the paragraph defining `gr` before Lemma 05SP
and the commutative diagram in Lemma 0127.

Proof (the quotient-map construction in Step 1 of the node): compose each chosen
restriction with its target inclusion. The defining equalities from `f.preserves`
and the inclusions of successive steps show that the two composites from the
`(p + 1)`-st source step to the `p`-th target step become equal after the monic
inclusion into `B.obj`. Cancel that inclusion. Thus `restriction f p` carries the
source inclusion into the target inclusion, which the target cokernel kills.
Apply the universal property of the source cokernel to obtain `g` and its equation.
The filtration steps and graded pieces are those of `def-sp-filtration`.
(blueprint: lem-sp-finite-filtration-induction). -/
theorem exists_gradedMap (A B : PBCFilteredObject C) (f : Hom A B) (p : ℤ) :
    ∃ g : A.filtration.gradedPiece p ⟶ B.filtration.gradedPiece p,
      cokernel.π (Subobject.ofLE (A.filtration.step (p + 1))
        (A.filtration.step p) (A.filtration.antitone_step (by omega))) ≫ g =
        restriction f p ≫ cokernel.π (Subobject.ofLE (B.filtration.step (p + 1))
          (B.filtration.step p) (B.filtration.antitone_step (by omega))) := by
  let iA := Subobject.ofLE (A.filtration.step (p + 1)) (A.filtration.step p)
    (A.filtration.antitone_step (by omega))
  let iB := Subobject.ofLE (B.filtration.step (p + 1)) (B.filtration.step p)
    (B.filtration.antitone_step (by omega))
  have hw : iA ≫ (restriction f p ≫ cokernel.π iB) = 0 := by
    rw [← Category.assoc, restriction_naturality, Category.assoc, cokernel.condition,
      comp_zero]
  exact ⟨cokernel.desc iA (restriction f p ≫ cokernel.π iB) hw,
    cokernel.π_desc _ _ _⟩

/-- The map induced by a filtered morphism on its graded pieces.
Source: Stacks Project, Homology, the paragraph defining `gr` before Lemma 05SP
and the commutative diagram in Lemma 0127. This is the unique map commuting with
the cokernel projections, chosen from `exists_gradedMap`.
(blueprint: lem-sp-finite-filtration-induction) -/
noncomputable def gradedMap {A B : PBCFilteredObject C} (f : Hom A B) (p : ℤ) :
    A.filtration.gradedPiece p ⟶ B.filtration.gradedPiece p :=
  Classical.choose (exists_gradedMap A B f p)

private theorem restriction_isIso_of_succ {A B : PBCFilteredObject C} (f : Hom A B)
    (p : ℤ) (hsucc : IsIso (restriction f (p + 1)))
    (hgr : IsIso (gradedMap f p)) : IsIso (restriction f p) := by
  let iA := Subobject.ofLE (A.filtration.step (p + 1)) (A.filtration.step p)
    (A.filtration.antitone_step (by omega))
  let iB := Subobject.ofLE (B.filtration.step (p + 1)) (B.filtration.step p)
    (B.filtration.antitone_step (by omega))
  let SA := ShortComplex.cokernelSequence iA
  let SB := ShortComplex.cokernelSequence iB
  have hSA : SA.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact iA
      mono_f := by dsimp [SA, ShortComplex.cokernelSequence, iA]; infer_instance }
  have hSB : SB.ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact iB
      mono_f := by dsimp [SB, ShortComplex.cokernelSequence, iB]; infer_instance }
  let φ : SA ⟶ SB :=
    { τ₁ := restriction f (p + 1)
      τ₂ := restriction f p
      τ₃ := gradedMap f p
      comm₁₂ := (restriction_naturality f p).symm
      comm₂₃ := (Classical.choose_spec (exists_gradedMap A B f p)).symm }
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃' φ hSA hSB hsucc hgr

/-- A morphism inducing isomorphisms on all graded pieces of finite filtrations
is an isomorphism, and all induced maps on filtration steps are isomorphisms.

Source: Stacks Project, Homology, Lemma 0127 (`lemma-characterize-strict`),
the descending-induction argument in the proof of (3) implies (2).

Proof:
1. Use `def-sp-filtration` to choose common bounds `n ≤ m`: decrease the two
   lower bounds to their minimum and increase the upper bounds to their maximum
   (and, if necessary, increase `m` to `n`). Steps with `p ≤ n` are whole objects;
   steps with `p ≥ m` are zero. Uniqueness of factorization through each monic
   target inclusion makes the restrictions commute with consecutive inclusions.
   The cokernel universal property then defines the graded maps. For every `p`,
   these form a commutative diagram of the short exact sequences
   `0 → F^(p+1) → F^p → gr^p → 0` and their counterparts for `B`.
2. For `p ≥ m` the restriction is a map between zero objects, hence an isomorphism.
   Descend through the finitely many integers from `m` to `n`. At each step the
   left arrow is an isomorphism by induction and the right arrow by `hgraded`.
   The short five lemma (`lem-weil-pbc-short-five-lemma`, realized by
   `CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃`) makes the middle
   restriction an isomorphism. For `p < n`, both steps are whole objects, so the
   same conclusion follows by their canonical identifications with the `n`-th steps.
3. At `n`, both inclusions into the underlying objects are isomorphisms. Their
   commutative square expresses `f.hom` as a composite of the restriction at `n`
   with these isomorphisms. Therefore `f.hom` is an isomorphism. All restrictions
   being isomorphisms says `f(F^p A) = F^p B`, so the map is strict as asserted.
(blueprint: lem-sp-finite-filtration-induction) -/
theorem finite_filtration_induction (A B : PBCFilteredObject C) (f : Hom A B)
    (hA : A.filtration.IsFinite) (hB : B.filtration.IsFinite)
    (hgraded : ∀ p : ℤ, IsIso (gradedMap f p)) :
    IsIso f.hom ∧ ∀ p : ℤ, IsIso (restriction f p) := by
  obtain ⟨nA, mA, hnA, hmA⟩ := hA
  obtain ⟨nB, mB, hnB, hmB⟩ := hB
  let m := max mA mB
  have hzero (p : ℤ) (hp : m ≤ p) : IsIso (restriction f p) := by
    have hAp : A.filtration.step p = ⊥ := by
      apply le_antisymm _ bot_le
      simpa [hmA] using A.filtration.antitone_step
        (show mA ≤ p by dsimp [m] at hp; omega)
    have hBp : B.filtration.step p = ⊥ := by
      apply le_antisymm _ bot_le
      simpa [hmB] using B.filtration.antitone_step
        (show mB ≤ p by dsimp [m] at hp; omega)
    have hAz : IsZero (A.filtration.step p : C) := by
      rw [hAp]
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    have hBz : IsZero (B.filtration.step p : C) := by
      rw [hBp]
      exact (isZero_zero C).of_iso Subobject.botCoeIsoZero
    exact isIso_of_source_target_iso_zero _ hAz.isoZero hBz.isoZero
  have hi : ∀ k : ℕ, ∀ p : ℤ, m ≤ p + k → IsIso (restriction f p) := by
    intro k
    induction k with
    | zero =>
      intro p hp
      exact hzero p (by simpa using hp)
    | succ k ih =>
      intro p hp
      exact restriction_isIso_of_succ f p (ih (p + 1) (by omega)) (hgraded p)
  have hall (p : ℤ) : IsIso (restriction f p) :=
    hi (m - p).toNat p (by omega)
  let n := min nA nB
  have hAn : A.filtration.step n = ⊤ := by
    apply top_unique
    rw [← hnA]
    exact A.filtration.antitone_step (min_le_left _ _)
  have hBn : B.filtration.step n = ⊤ := by
    apply top_unique
    rw [← hnB]
    exact B.filtration.antitone_step (min_le_right _ _)
  have : IsIso (A.filtration.step n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 hAn
  have : IsIso (B.filtration.step n).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).2 hBn
  have := hall n
  have hhom : f.hom = inv (A.filtration.step n).arrow ≫
      restriction f n ≫ (B.filtration.step n).arrow := by
    rw [restriction_arrow, IsIso.inv_hom_id_assoc]
  constructor
  · rw [hhom]
    infer_instance
  · exact hall

end PBCFilteredObject

end CategoryTheory
