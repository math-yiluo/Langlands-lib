/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 111, 14 November 2026: extract the data units M151.001, .004,
.005, .006 and .007 of NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/FilteredLiftingSequence.lean`
(lines 28–31, 46–68 and 70–89), prefix the namespace with `Langlands.NYLL` and
replace the NYLL import by the single Mathlib module the data needs. Universes,
binders, structure fields and definition bodies are unchanged. See the paired
Markdown; the LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.Algebra.Group.Hom.Defs

/-!
# Recursive correction sequences: data

The left-to-right finite products of a correction sequence, the remainder and
one-step-lift structures for a filtered commutative group, and the sequences
chosen recursively from a supplied one-step lifting hypothesis.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

/-- Left-to-right finite products of a correction sequence. -/
def filteredCorrectionProduct {A : Type u} [Monoid A] (z : Nat → A) : Nat → A
  | 0 => 1
  | d + 1 => filteredCorrectionProduct z d * z d

/-- A remainder at depth `n + i`, carrying both its filtration condition and
the condition that must be preserved by one-step lifting. -/
structure FilteredLiftState (A : Type u) (P : Nat → A → Prop)
    (R : A → Prop) (n i : Nat) where
  /-- The current remainder at relative depth `i`. -/
  value : A
  /-- The current remainder lies in filtration level `n + i`. -/
  mem : P (n + i) value
  /-- The current remainder satisfies the condition preserved by each lifting step. -/
  stable : R value

/-- One correction step `a_i = F(b_i) a_(i+1)`. -/
structure FilteredLiftStep (A : Type u) [CommGroup A]
    (P : Nat → A → Prop) (R : A → Prop) (F : A →* A)
    (n i : Nat) (s : FilteredLiftState A P R n i) where
  /-- The correction chosen at relative depth `i`. -/
  correction : A
  /-- The correction lies in the same filtration level `n + i` as the current remainder. -/
  correction_mem : P (n + i) correction
  /-- The remainder state after removing the current correction, one level deeper. -/
  next : FilteredLiftState A P R n (i + 1)
  /-- The current remainder is the image of the correction under `F` times the next remainder. -/
  equation : s.value = F correction * next.value

/-- The recursively chosen remainder sequence. -/
noncomputable def chosenFilteredLiftStateSequence
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) :
    (i : Nat) → FilteredLiftState A P R n i
  | 0 => initial
  | i + 1 =>
      (Classical.choice
        (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).next

/-- The recursively chosen correction at depth `n + i`. -/
noncomputable def chosenFilteredLiftCorrectionSequence
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (i : Nat) : A :=
  (Classical.choice
    (step i (chosenFilteredLiftStateSequence A P R F n initial step i))).correction

end

end Langlands.NYLL.LocalClassFieldTheory
