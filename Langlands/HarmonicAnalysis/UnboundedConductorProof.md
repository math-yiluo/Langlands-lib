# Unbounded multiplicative conductors

The module `Langlands.HarmonicAnalysis.UnboundedConductorProof` proves
`Langlands.HarmonicAnalysis.padicQuasicharacterUnboundedConductor.{uF}` with
exact type
`Langlands.HarmonicAnalysis.PadicQuasicharacterUnboundedConductorStatement.{uF}`.
The theorem covers every prime, every canonical p-adic field in the independent
universe `uF`, and every natural conductor bound, including zero. It constructs
an actual continuous homomorphism from the field units to complex units.
The statement, canonical topology, quasicharacter type, and conductor definition
are imported without changes.

## Shared character separation and openness

The module imports
[`Langlands.HarmonicAnalysis.CharacterSeparation`](CharacterSeparation.md).
Its `exists_discrete_character` and `principalUnits_isOpen` are the helpers
originally implemented here, moved with their proofs unchanged into a shared
namespace. The rational-circle embedding and its injectivity proof remain
private in that module. These helpers are also used by the rank-one
bounded-conductor coset proof.

## The actual principal-unit filtration

The private `exists_strict_principal_unit` treats every positive level `n`.
Surjectivity of the actual valuation, followed by the ordered value-group
isomorphism, supplies `x` with
`T.discreteValuation x = WithZero.exp (-(n : ℤ))`.
Because `n` is positive, this value is less than one. The strong triangle
equality therefore gives `T.discreteValuation (1 + x) = 1`, which also proves
`1 + x` is nonzero. Regard it as a field unit `u`. Then `u - 1 = x`, so
`u` belongs to `T.principalUnits n`. Membership at level `n + 1` would imply
`-n ≤ -(n + 1)` after applying the strict order correspondence for
`WithZero.exp`, a contradiction.

## Final construction and conductor bound

For a prescribed bound `A`, set `T = F.canonicalTopologicalData` and
`n = A + 1`. Choose the unit just constructed and put
`H = T.principalUnits (n + 1)`. Its image in `F.Carrierˣ ⧸ H` is nonidentity.
Openness of `H` gives the quotient its discrete topology via
`QuotientGroup.discreteTopology`. The character-separation helper supplies a
continuous complex character of this quotient that detects the image of `u`.
Composition with the continuous quotient homomorphism
`QuotientGroup.mk' H` gives the required quasicharacter `χ` of the original
field-unit group, with `χ u ≠ 1`.

If `T.multiplicativeConductor χ ≤ n`, the imported
`T.multiplicativeTrivialAt_iff_conductor_le χ n` would make `χ` trivial on
`T.principalUnits n`, contradicting its value at `u`. Thus its conductor is
greater than `A + 1`, which implies the requested lower bound `A`. The choice
of a positive level handles `A = 0` in the same argument. No character
extension, reciprocity, finite-order character theorem, or power-cofinality
result is a premise.

## Provenance and authorship

This is an internal elementary proof of the existing Library proposition.
It uses the imported Library conductor theory and Mathlib's character-module,
quotient-group, circle, and valuation-topology results. The proof route is
independent of any original-source proof: the source motivation and conductor
convention remain documented in `UnboundedConductorStatement.md`.
It proves character existence, with no claim about Rankin--Selberg vanishing,
principal-unit power cofinality, or local class-field theory.

Worker 649 implemented the rational-circle embedding, discrete separation,
strict filtration witness, and final theorem. Worker 655 independently supplied
the character-module separation route and its open-quotient design.
The openness proof reuses Worker 394's `isOpen_principalUnits` implementation
from the shared, unreviewed revision-11 `WhittakerTypeHighlyRamifiedProof`
draft, adapted here as a private helper; only that helper was reused.
Both workers are credited as coauthors. Compilation and target inspection are
development evidence; independent semantic review and publication remain
separate requirements.

## All-field port

The declarations of this module that involve the p-adic field and that the Library's proofs of JPSS (3.1) multiplicativity use are re-declared over every nonarchimedean local field, of any characteristic, in `Langlands.AllField.HarmonicAnalysis.UnboundedConductorProof` (the Markdown there lists them). For those declarations this p-adic module is superseded by the all-field port; its Lean code is unchanged.
