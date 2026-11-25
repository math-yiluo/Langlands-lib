# Recursive correction sequences in a filtered group

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.FilteredLiftingSequence`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file isolates the dependent-choice bookkeeping of the infinite-product argument in the proof of the local class-field axiom. In a commutative group `A` with an endomorphism `F : A →* A`, a procedure that writes each remainder as `F(correction) · next remainder` is iterated to produce a sequence of corrections and a sequence of remainders. No cohomology enters: the existence of each one-step lift is an explicit parameter, supplied for the normal-basis filtration in a later file.

## Definitions

- `filteredCorrectionProduct z d`: the left-to-right product `z 0 · z 1 ⋯ z (d−1)` in a monoid, equal to `1` for `d = 0`.
- `FilteredLiftState A P R n i`: an element lying in level `n + i` of a "filtration" `P : ℕ → A → Prop` and satisfying a condition `R` that the steps preserve.
- `FilteredLiftStep A P R F n i s`: a correction `b` in level `n + i` and a next state at depth `i + 1` with `s = F(b) · next`.
- `chosenFilteredLiftStateSequence`, `chosenFilteredLiftCorrectionSequence`: from an initial state and a proof that every state admits a step, the remainders and corrections obtained by choosing a step at each depth.

## Results

- `chosenFilteredLiftCorrectionSequence_mem`: the `i`-th correction lies in level `n + i`.
- `chosenFilteredLiftStateSequence_equation`: the `i`-th remainder is `F` of the `i`-th correction times the `(i+1)`-th remainder.
- `filteredLift_initial_eq_correctionProduct_mul_state`: for every `d`, the initial remainder equals `F` of the product of the first `d` corrections times the remainder at depth `d`; proved by induction on `d` from the one-step equation.

Simp lemmas unfold both recursions at `0` and at successors.

## Points to note

The filtration is only a family of predicates: nothing requires the levels to be subgroups or nested, and no limit or convergence is taken here. The step hypothesis must hold for every state at every depth, not only for the states actually reached.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/FilteredLiftingSequence.lean`: the Lean file is the source byte for byte (SHA-256 `be26830e2d2478be859ac1898d110c3abb4a2d2ed97283963cfc42e531184839`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
