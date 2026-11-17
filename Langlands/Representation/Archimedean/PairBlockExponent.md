# Exponents of the blocks of archimedean pair presentations

Author: Worker 3657. Verified and submitted by Worker 831 from the shared Task 6818 draft.

Module `Langlands.Representation.Archimedean.PairBlockExponent` is a helper for the proofs of
Task 6818 (`7825d219-2a04-4194-9e19-95b05a84c4dc`). It proves small facts about the pair
presentations of the published module `Langlands.LocalFactor.ArchimedeanPairFactor`. The pair
`L`-factors there are the `L`-factors of block lists: `realPairBlocks xs ys` (all
`x.tensor y`, `x ∈ xs`, `y ∈ ys`) and `complexPairBlocks xs ys` (all `x.mul y`). This module
records that each block of a pair presentation comes from one block of each presentation, and
that the exponents add.

It imports `Langlands.Representation.Archimedean.RealGenericParameterReduction` (for
`realBlockExponent`) and `Langlands.LocalFactor.ArchimedeanPairFactor`. Every result uses
only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Declarations

In namespace `Langlands.LocalFactor.Archimedean`:

- `RealCharacterData.exponent_mul c d : (c.mul d).exponent = c.exponent + d.exponent`
  (`@[simp]`).
- `ComplexCharacterData.exponent_mul c d : (c.mul d).exponent = c.exponent + d.exponent`
  (`@[simp]`).
- `ComplexCharacterData.exponent_conj d : d.conj.exponent = d.exponent` (`@[simp]`).
- `ComplexCharacterData.exponent_twistReal d c :
  (d.twistReal c).exponent = d.exponent + c.exponent` (`@[simp]`).
- `mem_realPairBlocks : z ∈ realPairBlocks xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, z ∈ x.tensor y`.
- `mem_complexPairBlocks : z ∈ complexPairBlocks xs ys ↔ ∃ x ∈ xs, ∃ y ∈ ys, z = x.mul y`.

In namespace `Langlands.Archimedean`:

- `realBlockExponent_of_mem_tensor (hz : z ∈ x.tensor y) :
  realBlockExponent z = realBlockExponent x + realBlockExponent y`.
- `exists_realBlockExponent_of_mem_realPairBlocks (hz : z ∈ realPairBlocks xs ys) :
  ∃ x ∈ xs, ∃ y ∈ ys, realBlockExponent z = realBlockExponent x + realBlockExponent y`.

Here `realBlockExponent` (module `RealGenericParameterReduction`) is the real part of the
exponent of a character block or of an induced block.

## Proofs

- The four exponent lemmas hold by `rfl`. The published definitions `RealCharacterData.mul`,
  `ComplexCharacterData.mul` and `ComplexCharacterData.twistReal` set the exponent to the sum,
  and `ComplexCharacterData.conj` keeps it.
- `mem_realPairBlocks` and `mem_complexPairBlocks` unfold the definitions
  `realPairBlocks xs ys = xs.flatMap fun x => ys.flatMap x.tensor` and
  `complexPairBlocks xs ys = xs.flatMap fun x => ys.map x.mul` and use `List.mem_flatMap` and
  `List.mem_map`.
- `realBlockExponent_of_mem_tensor` goes through the four cases of `RealBlock.tensor`.
  - `character c ⊗ character d = [character (c.mul d)]`.
  - `character c ⊗ induced d = [induced (d.twistReal c)]`, and symmetrically for
    `induced d ⊗ character c`.
  - `induced d ⊗ induced e = [induced (d.mul e), induced (d.mul e.conj)]`.

  In each case the exponent lemmas give `t_z = t_x + t_y`, and taking real parts gives the
  claim. In the case `character c ⊗ induced d` the sum is in the other order, which
  commutativity of addition fixes.
- `exists_realBlockExponent_of_mem_realPairBlocks` combines the two previous results.

## Provenance

These are elementary facts about the Library's own definitions, so no literature is needed.
Mathematically they say that the exponent of a tensor product of characters of `ℝˣ` or `ℂˣ`
is the sum of the exponents. The identification of the block lists with actual tensor products
of Weil-group representations is explained in the Markdown of `ArchimedeanPairFactor` and is
not used here.
