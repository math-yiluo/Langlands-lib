# Gamma relations over general nonarchimedean local fields

Worker 99 adapts Worker 11's published p-adic rank-order interface to the
already published general-field JPSS relation. All declarations are in
`Langlands.RankinSelberg`. This is a derived definition unit; it does not prove
analytic existence of gamma factors or the Shahidi comparison.

## Setting and definitions

The field `F` has `Field`, `ValuativeRel`, `TopologicalSpace` and
`IsNonarchimedeanLocalField` instances. There is no characteristic restriction.
The two representations have positive ranks `r + 1` and `n + 1`, on arbitrary
algebraic complex modules in independent universes. No norm, finite dimension,
unitarity, irreducibility or admissibility is imposed by these definitions.

`IsGeneralPairGammaFactor q ψ abv ν π σ G` specializes the existing
`IsPairGammaFactor` in `GammaFactor.lean`. It installs the Borel measurable
structures of `F`, `GL_(n+1)(F)`, its upper unipotent subgroup and its
left-unipotent quotient. Its additive Haar input `ν` is measured on the Borel
structure of `F`. There are no external measurable-space choices to reconcile.

The spectral integer `q`, real absolute value `abv` and Fourier Haar measure
`ν` remain explicit. The character `ψ` has type `UnitaryAdditiveCharacter F`,
whose structure bundles continuity, values in the unit circle and nontriviality
(`toAddChar ≠ 1`), so `ψ` is nontrivial by its type and needs no separate
hypothesis. The relation itself does not assert residue normalization or
self-duality of `ν`. Consumers interpreting it as the normalized local gamma
factor must supply those hypotheses in their theorem statements. Uniqueness
below requires `1 < q`.

This is literally the published JPSS relation: it requires a compatible quotient
measure and nonzero Whittaker functionals to exist, and the gamma equation holds
for every compatible quotient measure and every pair of nonzero functionals.
The larger-rank first representation uses `ψ`; the second uses the inverse
character. The underlying equations retain their nonzero rational continuation
clause, central minus-one factor, dual integrals and the existing Fourier-pair
relation. A new gamma function, quotient measure or integral is not constructed.
As in `IsPairGammaFactor`, this unsymmetrized relation is false when `r < n`.

`IsGeneralSymmetricGammaFactor q ψ abv ν π σ G` is the preceding relation for
`(π, σ)` when `n ≤ r`, and for `(σ, π)` when `r < n`. The larger rank is thus
first, and equal ranks retain the input order. After a strict-rank swap, `σ`
uses the `ψ`-model and `π` the inverse-character model. The word “symmetric”
names this rank-order convention; it does not assert an equal-rank interchange
theorem.

## Sources and derived provenance

Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg Convolutions*,
American Journal of Mathematics 105 (1983), §2.12, printed page 403, define
the smaller-rank-first L and epsilon factors by reversing the pair.
The paragraph also discusses equal-rank symmetry, which is not proved here.
Source `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The cited page was read from the original scan (PDF page 38).

The gamma convention is derived from that L/epsilon convention: contragredients
preserve ranks, so the ratio
`ε(s, π × σ, ψ) L(1-s, π̃ × σ̃) / L(s, π × σ)` has the same ordering.
Shahidi, *Fourier transforms of intertwining operators and Plancherel measures
for GL(n)*, American Journal of Mathematics 106 (1984), printed page 68,
defines precisely this ratio as `ε'`. Source `shahidi-1984-fourier`, SHA256
`a10d5c605d94d4e85d0e5f453d6a8c233d91e3cb60d538f430d8ad900cbb6b29`.
The display was read from the original scan (PDF page 3). This provenance
explains the intended convention; the Lean definitions reuse the functional
equation relation, without assuming a theorem identifying it with separate
L and epsilon witnesses.

The Borel specializations and their proofs are internal consequences of
`GammaFactor.lean`. The conditional rank interface follows the published
`IsPadicSymmetricGammaFactor` in `PadicPairFactors.lean`; no published p-adic
declaration is changed.

## Implemented proofs

`IsGeneralPairGammaFactor.unique` installs the same Borel structures and
applies `IsPairGammaFactor.unique` with `q > 1`.
`IsGeneralPairGammaFactor.congr_equiv` similarly uses the existing
`IsPairGammaFactor.congr_equiv`. Both representations can change carrier
universes under the equivalences.

`isGeneralSymmetricGammaFactor_of_le` and
`isGeneralSymmetricGammaFactor_of_lt` reduce the defining conditional.
`IsGeneralSymmetricGammaFactor.unique` splits the same conditional and applies
pair uniqueness in the selected order.
`IsGeneralSymmetricGammaFactor.congr_equiv` also splits it and reverses the
two representation equivalences in the swapped branch.

`isGeneralPairGammaFactor_padic` specializes the topology, valuation and
local-field instances to the canonical data of a `PadicField`, with its
residue cardinality and normalized absolute value. Its equivalence with
`IsPadicPairGammaFactor` is definitional, proved by `Iff.rfl`.
`isGeneralSymmetricGammaFactor_padic` does the same for the two rank branches
and is also proved by `Iff.rfl`.

These are intrinsic uniqueness, transport and specialization proofs. They
select no factor and provide no existence, analytic continuation, measure
normalization or local-coefficient comparison theorem.
