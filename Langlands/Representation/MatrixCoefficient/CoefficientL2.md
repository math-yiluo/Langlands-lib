# Actual coefficient embeddings into central L2

Author: Worker 386.

This internal construction restricts the published actual central coefficient
map to the published central L2 subrepresentation, proves that it is injective
for an irreducible source and a nonzero functional, and pulls back the actual
integral form. It does not complete the representation or claim that the
image is closed before completion.

## Parameters and restriction

The group `G : Type uG` and algebraic complex carrier `V : Type uV` have
independent universes. The assumptions on `G` are a group, a topology and a
topological group structure. The actual central quotient carries a Borel
measurable structure. The source representation `ρ` has no carrier topology
or finite dimensionality assumption.

Given `c : UnitaryCentralCharacter ρ`, smoothness `hρ : IsSmooth ρ`,
an algebraic complex-linear functional `ℓ`, a right-invariant Borel measure
`μ` on the full central quotient, and
`hL2 : ∀ v, MemLp (c.coefficientNorm ℓ v) 2 μ`,
`c.coefficientL2Intertwiner hρ ℓ μ hL2` is an actual intertwiner from `ρ`
to `Induction.centralL2Representation c.character c.norm_eq_one μ`.
It sends `v` to the existing smooth central function
`g ↦ ℓ(ρ(g)v)`, with its integrability proof. Its linearity and
equivariance follow from `coefficientIntertwiner`; membership follows from
`coefficientIntertwiner_memLp_iff`.

`coefficientL2Intertwiner_inclusion` recovers the original smooth central
function through the central L2 inclusion. The evaluation laws recover
the actual matrix coefficient and, at the identity, `ℓ(v)`.
Nonzero `ℓ` gives a nonzero restricted map. If `ρ` is algebraically
irreducible, `coefficientL2Intertwiner_injective` applies the published
coefficient injection to the equality of underlying functions.

## Actual pulled-back form

With the additional hypothesis that `μ` is Haar, algebraic irreducibility
and `hℓ : ℓ ≠ 0`, `c.coefficientL2Form hρ ℓ μ hL2 hℓ` pulls back
`Induction.centralL2Form` along this injective intertwiner using
`InvariantPositiveForm.comap`. Its positivity, definiteness, Hermitian
identities and invariance therefore come from the actual integral form
and the proved injection.

`coefficientL2Form_inner` gives the exact integral of the descended
Hermitian pairing of the two centrally covariant coefficient functions.
The coefficient functions themselves are functions on `G`; the product
with conjugation descends to `G / Z(G)`. The diagonal law is exactly

```text
coefficientL2Form(v,v) = complex(∫ q, coefficientNorm(ℓ,v,q)^2 dμ).
```

There is no change to ordinary L2 of `G`, no choice of a quotient
representative for a complex coefficient, and no claim that this form
equals an initially supplied invariant form.

## Existence from the analytic predicate

`InvariantPositiveForm.exists_nonzero_smoothDual` uses a nonzero source
vector and the published injective map `b.toSmoothDual hρ` to produce a
nonzero actual smooth-dual functional.

`IsSquareIntegrableModCenter.exists_coefficientL2_embedding` assumes the
actual analytic predicate for `μ`, unitarizability, and irreducibility.
The latter supplies source nontriviality through Mathlib's simple-module
comparison. An actual invariant positive form then supplies a nonzero
smooth-dual functional. The analytic predicate supplies `c` and the
`MemLp` condition for this functional, so the preceding construction
gives an injective coefficient map. No embedding is a premise.

## Provenance and limits

This is an internal consequence of the existing CentralInduction,
CentralL2 and HermitianDual constructions. The implemented arguments are
the restriction of an actual map to a subrepresentation, preservation
of injectivity, and pullback of an actual positive form. No independently
numbered theorem in the original literature is being transcribed.
No external source is required for these derivations.

Completion, closedness of the completed range, irreducibility of a
unitary realization, a mirabolic decomposition, and a nonzero Whittaker
functional remain separate obligations of the genericity argument.
