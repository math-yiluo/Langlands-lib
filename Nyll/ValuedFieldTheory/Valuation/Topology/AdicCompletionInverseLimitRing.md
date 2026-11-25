# Adically complete rings as inverse limits of their quotients

Module `Nyll.ValuedFieldTheory.Valuation.Topology.AdicCompletionInverseLimitRing`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a commutative ring `R` and an ideal `I`, this file builds the projective limit `lim R/Iⁿ` as an explicit ring with the prodiscrete topology, identifies it with Mathlib's `AdicCompletion I R`, and shows that when `R` is `I`-adically complete the reduction map `R → lim R/Iⁿ` is an isomorphism of rings and, for the `I`-adic topology on `R`, a homeomorphism. A version indexed by the levels `n + 1` is given alongside.

## Main definitions and results

- `adicCompletionAlgEquiv`: for `R` `I`-adically complete, `R ≃ₐ[R] AdicCompletion I R` (Mathlib's `AdicCompletion.ofAlgEquiv`); `adicCompletion_coordinates_injective`: an element of `R` is determined by its reductions mod all `Iⁿ`; `adicCompletion_coordinates_surjective`: every point of the completion comes from an element of `R` with the same reductions.
- `adicQuotientInverseLimit I`: the ring of compatible families `(xₙ)` with `xₙ ∈ R/Iⁿ`, `n ≥ 0`, with coordinate maps, an extensionality lemma, and the topology induced from the product of discrete quotients.
- `adicCompletion_equiv_quotientInverseLimit`: `AdicCompletion I R ≃+* adicQuotientInverseLimit I`, with no completeness hypothesis.
- `adicQuotientInverseLimitEquiv`: for complete `R`, `R ≃+* lim R/Iⁿ`, coordinatewise reduction (`adicQuotientInverseLimitEquiv_apply`).
- `adicQuotientInverseLimitHomeomorph`: for complete `R`, a homeomorphism from `R` with the `I`-adic topology (as `WithTopology R I.adicTopology`) to the limit.
- `adicPositiveQuotientInverseLimit I`: the same limit over `R/Iⁿ⁺¹`; `adicQuotientInverseLimitEquivPositive` identifies it with the full one, and `adicPositiveQuotientInverseLimitEquiv` and `adicPositiveQuotientInverseLimitHomeomorph` are the corresponding isomorphism and homeomorphism.
- `DiscreteAdicQuotient I n`: a copy of `R/Iⁿ` carrying the discrete topology, used as target of continuous coordinate maps (`quotient_mk_continuous_adic`, `adicQuotientInverseLimit_discreteEval_continuous`).

## Proofs

The ring isomorphism composes Mathlib's isomorphism with the completion and the identification of the completion with compatible families. Reduction mod `Iⁿ` is continuous from the `I`-adic topology to a discrete quotient, which gives continuity in one direction; for the inverse, the cylinder set where the `n`-th coordinate is fixed maps into `x + Iⁿ`.

## Points to watch

- The limits are the library's own types, built on the compatible-family subrings of another file; their ring structure and topology are transferred along a named equivalence rather than being Mathlib's limits.
- The topology on the limit is the prodiscrete one: each `R/Iⁿ` is discrete, whatever its size.
- The homeomorphisms use the `I`-adic topology on `R`, through a `WithTopology` copy, not a topology `R` may already carry.
- The full limit keeps the trivial level `R/I⁰`; the positive version drops it and its coordinate `n` is level `n + 1`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Topology/AdicCompletionInverseLimitRing.lean`: the Lean file is the source byte for byte (SHA-256 `c98075968265ca7bca312c8630ab2ebf3800c65a206f321346915d18fadab0da`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
