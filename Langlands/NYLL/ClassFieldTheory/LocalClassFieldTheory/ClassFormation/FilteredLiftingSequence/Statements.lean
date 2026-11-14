/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 111, 14 November 2026: extract the theorem units M151.002,
.003, .008, .010, .011 and .012 of NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/FilteredLiftingSequence.lean`
(lines 33–44, 91–99 and 113–155), as Prop-valued definitions with the
`Statement` suffix, prefix the namespace with `Langlands.NYLL`, drop the
`@[simp]` attributes, reuse the published M151 data by Lean name and replace
the NYLL import. Universes, binders and propositions are unchanged; no proof is
supplied. See the paired Markdown; the LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FilteredLiftingSequence.Definitions

/-!
# Recursive correction sequences: statements

The exact propositions of the source theorems about the left-to-right
correction products and the recursively chosen remainder and correction
sequences: the two defining equations of the product, the initial chosen
state, the filtration membership of each chosen correction, the one-step
recurrence and its iterate.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u

/-- Source M151.002: the empty correction product is the identity. -/
def filteredCorrectionProduct_zeroStatement {A : Type u} [Monoid A] (z : Nat → A) : Prop :=
  filteredCorrectionProduct z 0 = 1

/-- Source M151.003: a successor correction product appends the correction at
the preceding index. -/
def filteredCorrectionProduct_succStatement {A : Type u} [Monoid A]
    (z : Nat → A) (d : Nat) : Prop :=
  filteredCorrectionProduct z (d + 1) = filteredCorrectionProduct z d * z d

/-- Source M151.008: the chosen filtered-lift sequence starts at the supplied
initial state. -/
def chosenFilteredLiftStateSequence_zeroStatement
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) : Prop :=
  chosenFilteredLiftStateSequence A P R F n initial step 0 = initial

/-- Source M151.010: every chosen correction lies at the advertised filtration
level `n + i`. -/
def chosenFilteredLiftCorrectionSequence_memStatement
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (i : Nat) : Prop :=
  P (n + i)
    (chosenFilteredLiftCorrectionSequence A P R F n initial step i)

/-- Source M151.011: the defining one-step recurrence for the chosen
sequences, `a_i = F(b_i) * a_(i+1)`. -/
def chosenFilteredLiftStateSequence_equationStatement
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (i : Nat) : Prop :=
  (chosenFilteredLiftStateSequence A P R F n initial step i).value =
    F (chosenFilteredLiftCorrectionSequence A P R F n initial step i) *
      (chosenFilteredLiftStateSequence A P R F n initial step (i + 1)).value

/-- Source M151.012: the initial remainder equals the image under `F` of the
product of the first `d` chosen corrections, times the depth-`d` remainder. -/
def filteredLift_initial_eq_correctionProduct_mul_stateStatement
    (A : Type u) [CommGroup A] (P : Nat → A → Prop) (R : A → Prop)
    (F : A →* A) (n : Nat) (initial : FilteredLiftState A P R n 0)
    (step : ∀ i (s : FilteredLiftState A P R n i),
      Nonempty (FilteredLiftStep A P R F n i s)) (d : Nat) : Prop :=
  initial.value =
    F (filteredCorrectionProduct
        (chosenFilteredLiftCorrectionSequence A P R F n initial step) d) *
      (chosenFilteredLiftStateSequence A P R F n initial step d).value

end

end Langlands.NYLL.LocalClassFieldTheory
