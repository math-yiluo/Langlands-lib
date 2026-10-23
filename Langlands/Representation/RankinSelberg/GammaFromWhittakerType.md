# Gamma construction from the original Whittaker-type pair

This derived construction supplies the two dual Whittaker-type hypotheses used
by the published gamma constructors from the original pair's Whittaker-type
hypotheses. It returns the existing certified rational-function unit and proves
that the reduced canonical input predicates are equivalent to the published
ones. It leaves the analytic and epsilon-existence inputs explicit.

## Provenance and normalization

The source normalization is Jacquet, Piatetski-Shapiro and Shalika,
*Rankin-Selberg Convolutions* (1983), section 2.1, printed pages 385–386.
Source ID: `jpss-1983-rankin-selberg`. Original file:
`Jacquet-Piatetski-Shapiro-Shalika--Rankin-Selberg Convolutions--1983.pdf`,
SHA256 `d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Both pages were read visually. Page 385 states the inverse-transpose transport
of Whittaker type; page 386, formula (4), identifies the transformed model with
the inverse additive character. Its separate irreducible contragredient
identification is not proved or used here.

The implementation composes the actual equivalences and type transport in
`DualWhittakerType` with the character identities in
`FunctionalEquationStatement` and the conditional constructions in
`PadicGammaFactor`. The input reduction and certified wrappers are internal
derived consequences of those constructions, not an additional analytic theorem
attributed to the source.

## Input reduction and constructed factors

`isOfWhittakerType_firstDual` starts with standard type for `π` and gives
standard type for `inverseTransposePullback π` at `ψ.scale (-1)`.
`isOfWhittakerType_secondDual` starts with inverse-standard type for `σ` and
gives inverse-standard type for its pullback at the same inverse character.
The proofs apply the respective transport theorems and rewrite the published
identities

```
standardCharacter (ψ.scale (-1)) n = inverseStandardCharacter ψ n
inverseStandardCharacter (ψ.scale (-1)) n = standardCharacter ψ n.
```

Thus the character in the dual analytic family remains exactly `x ↦ ψ(-x)`.
There is no choice of a functional or a dual representation in this reduction.

`gammaFactorOfWhittakerType` takes the original two Whittaker-type proofs and
supplies these two derived proofs to `gammaFactorOfAnalyticInput`. Its remaining
inputs are the rank order `n ≤ r`, both `PairAnalyticInput` propositions, `q > 1`,
self-duality of the given additive Haar measure, compatibility of the given
quotient measure, and `PairEpsilonFactorExists`. The output is a rational-function
unit together with the existing `IsPairGammaFactor` certificate.

`PadicPairGammaConstructionInput` installs the canonical p-adic topology,
valuation and local-field structure, Borel measurable structures, canonical
residue cardinality and normalized absolute value, and constructed
`unipotentQuotientHaar`. It retains exactly:

1. The rank order `n ≤ r`.
2. Self-duality of the given additive Haar measure for `ψ`.
3. Existence of the epsilon monomial satisfying the existing relation.
4. Standard Whittaker type for `π` and inverse-standard Whittaker type for `σ`.
5. The analytic conclusion for every nonzero functional pair of the original
   representations, and for every such pair of their inverse-transpose pullbacks
   at the inverse additive character. Equal rank uses the Schwartz-test family;
   unequal rank quantifies over every admissible rectangular block.

The private topology helper derives total disconnectedness from the valuative
topology using Mathlib's nonarchimedean-ring instance. This supplies the same
property needed by the existing self-duality predicate; it assumes no extra
field data.

`padicPairGammaConstructionInput_iff` proves equivalence with
`PadicPairGammaInput`. Its forward direction inserts the two derived type
proofs; its reverse direction discards them. Consequently the new predicate
has exactly the strength of the published input, while callers provide only
the original pair's type proofs.

`padicPairGammaFactorOfWhittakerType` converts this input and calls
`padicPairGammaFactor`. Its result is an actual unit with the existing
`IsPadicPairGammaFactor` certificate. All values, spectral conventions,
measure choices and uniqueness results belong to that unchanged construction.

`PadicSymmetricGammaConstructionInput` uses the existing larger-rank-first
branch convention. `padicSymmetricGammaConstructionInput_iff` proves equivalence
with `PadicSymmetricGammaInput` by the two rank-order cases.
`padicSymmetricGammaFactorOfWhittakerType` then returns the existing
`IsPadicSymmetricGammaFactor` certificate and unit for either order. This
branching convention asserts no rank-exchange identity.

## Scope

The field and representation carriers have independent universes `uF`, `uV`,
and `uW`. The shared `UnitaryAdditiveCharacter` already includes continuity
and nontriviality. Coefficients are complex; no topology is imposed on either carrier.
The general constructor uses the existing nonarchimedean local-field,
measurability, Borel, Hausdorff and total-disconnectedness hypotheses required
by its imported analytic and measure interfaces. The canonical constructors
install these structures from the actual `PadicField`.

All ranks are positive successors, including rank one, equal ranks and either
order of unequal ranks. Irreducibility is not added. The resulting factors use
inverse-transpose pullbacks; comparison with genuine smooth contragredients
remains separate. No convergence, rationality, normalized-generator existence,
functional equation, epsilon existence, self-dual measure existence, or
character independence is newly proved. The supplied analytic hypotheses
still carry convergence and rationality and permit the existing constructors
to build the original and dual L-factors. This construction removes only the
two redundant Whittaker-type assumptions.
