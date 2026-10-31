# Pullback of matching Jordan–Hölder factors

This module contains the existing generic pullback helpers from
[`FactorMatchingProof`](../Tensor/FactorMatchingProof.md), relocated with their
types and implementations unchanged and made public in
`Langlands.FiniteTensor.FactorMatchingProof`.

`filtrationComp` pulls an actual filtration back along a surjective monoid
homomorphism using `subrepresentationCompOrderIso`; `gradedComp` identifies its
graded representations with the original graded representations pulled back.
`equivComp` pulls an equivariant linear equivalence back along any monoid
homomorphism.

`matching_comp` preserves the predicate `HaveSameJordanHolderFactors` under a
surjective pullback. `matching_of_comp` detects that predicate after pullback
along a monoid isomorphism by pulling back along its inverse and applying
`haveSameJordanHolderFactors_transport`. The field, group and carrier universes
remain independent, and zero-length filtrations are allowed.

The tensor-factor matching proof and the two-factor constituent commutativity
proof share these helpers. This extraction adds no mathematical result.
