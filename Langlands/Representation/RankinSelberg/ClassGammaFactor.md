# Gamma construction on supercuspidal isomorphism classes

This derived internal consumer applies the existing canonical p-adic gamma
constructor to representatives with explicit input, then obtains a rational
function unit with the published `IsClassGammaFactor` certificate. It introduces
no new class equivalence or gamma-factor relation.

## Parameters and scope

The field is `F : PadicField.{uF} p` with its canonical topology. Coefficients
are complex numbers, and representation carriers have independent universes
`uV` and `uW`. The inputs are a unitary additive character `ψ`, an additive
Haar measure `ν`, and supercuspidal isomorphism classes `π,τ` of ranks `r+1`
and `n+1`. The class relation is the existing ordered pair relation; its
construction input includes `n ≤ r`. Both rank one and equal ranks are
included. This consumer does not introduce a symmetric class relation or
make a rank-exchange assertion.

`ClassGammaInput F ψ ν π τ` requires representatives `A,B` of the specified
classes, equality of their quotient classes with `π,τ`, and the published
`PadicPairGammaInput` for their underlying representations. That input retains
self-duality, pair epsilon existence, all four original/inverse-transpose
Whittaker-type hypotheses, and the original and dual analytic conclusions.
It constructs the quotient measure internally and uses the canonical residue
cardinality and absolute value. The required analytic and representation
theoretic results are not inferred merely from supercuspidality here.

`classGammaFactor` chooses the supplied representatives, calls
`padicPairGammaFactor` to construct a rational function unit, and transports its
certificate along the two quotient equalities using `isClassGammaFactor_mk`.
The result has type

`{G : RationalFunctionsˣ // IsClassGammaFactor F ψ ν π τ (G : RationalFunctions)}`.

There is no choice from an unconstrained gamma function. The actual value
comes from the published p-adic construction, whose gamma relation retains
its complete functional-equation domain and normalization.

## Proofs and provenance

The source-independent content of this file is a derived specialization of
`PadicGammaFactor` and the quotient lift already defined in `GammaFactor`.
The underlying mathematical normalization and original-source correspondence
are documented in those modules; this file adds no new analytic law.

`classGammaFactor_independent` applies `IsClassGammaFactor.unique` to the
two output certificates and then uses unit extensionality. Thus the result is
independent of the representatives and analytic witnesses used in its
construction. `classGammaFactor_eq` compares its underlying rational function
with any other value satisfying the published class relation. The proofs do
not need an additional hypothesis that analytic-input certificates transport
between arbitrary representatives: one representative pair suffices, and the
existing quotient relation and uniqueness compare the results.

The module asserts no unconditional existence of the analytic inputs,
smooth-contragredient identification, or nongeneric-class extension. It is a
focused consumer of the existing construction and relation, with all
remaining hypotheses retained explicitly.
