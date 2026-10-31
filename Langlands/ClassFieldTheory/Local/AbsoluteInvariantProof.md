# Absolute local invariants and restriction by degree

Author: Worker 154.

`Langlands.ClassFieldTheory.Local.absoluteInvariantExistence` proves exactly
the existing proposition `AbsoluteInvariantExistence.{u}`. For every prime
`p`, it gives one simultaneous family

`inv F : absoluteCohomology F.Carrier 2 ≃+ RationalModIntegers`

for all `F : PadicField.{u} p`. For every compatible finite extension `E/F`
and every specified base-compatible embedding of their algebraic closures,
the family satisfies

`inv E (absoluteRestriction F.Carrier E.Carrier 2 x) =
  Module.finrank F.Carrier E.Carrier • inv F x`.

The common universe `u` is arbitrary. The theorem has no additional
mathematical premises. The base extension need not be Galois. Its cohomology,
discrete algebraic-closure-unit coefficients, quotient of the rationals by
the integers, and restriction map are exactly those of the unchanged
[target statement](AbsoluteInvariantStatement.md).

## Implemented proof and its six inputs

The proof applies the published
`AbsoluteInvariantAssembly.absoluteInvariantExistence_of_finite_stages`
from [AbsoluteInvariantAssembly](AbsoluteInvariantAssembly.md). It supplies
each of that construction's six explicit premises with the corresponding
published unconditional theorem, in this order:

| Premise | Theorem supplied | Proof module |
| --- | --- | --- |
| `UnramifiedH2Exhaustion.{u}` | `unramifiedH2Exhaustion.{u}` | [UnramifiedH2Proof](UnramifiedH2Proof.md) |
| `ClosureInflationTowerCompatibility.{u}` | `closureInflationTowerCompatibility.{u}` | [ClosureInflationNaturalityProof](ClosureInflationNaturalityProof.md) |
| `UnramifiedInvariantInflationCompatibility.{u}` | `unramifiedInvariantInflationCompatibility.{u}` | [UnramifiedInvariantInflationProof](UnramifiedInvariantInflationProof.md) |
| `UnramifiedBaseChangeStageExistence.{u}` | `unramifiedBaseChangeStageExistence.{u}` | [UnramifiedBaseChangeProof](UnramifiedBaseChangeProof.md) |
| `ClosureInflationBaseChangeCompatibility.{u}` | `closureInflationBaseChangeCompatibility.{u}` | [ClosureInflationNaturalityProof](ClosureInflationNaturalityProof.md) |
| `UnramifiedInvariantBaseChangeCompatibility.{u}` | `unramifiedInvariantBaseChangeCompatibility.{u}` | [UnramifiedInvariantBaseChangeProof](UnramifiedInvariantBaseChangeProof.md) |

Exhaustion supplies a finite unramified Galois representative of every
absolute class under the actual `closureInflation`. The assembly evaluates
the explicit finite invariant on such a representative. Tower naturality,
injectivity of closure inflation, and finite invariant compatibility compare
two representatives in a common unramified stage. This proves that the value
is independent of the representative and additive. Finite invariant
injectivity proves injectivity of the descended map. The published existence
of unramified extensions of every positive degree, together with the exact
denominator-subgroup range of the finite invariant, proves surjectivity.
The assembly packages this map as `descendedEquiv`.

For restriction, the stage theorem supplies an unramified Galois stage over
`E` containing the image of the source stage under the specified closure
embedding. The assembly restricts that very embedding to the two stages.
Mixed closure-inflation naturality identifies the restricted absolute class
with the resulting finite inflation followed by restriction. Finite
base-change compatibility then multiplies its invariant by `[E:F]`.
Representative independence yields the degree law for the descended maps.
Tower naturality and mixed naturality are supplied separately; both are
proved for the actual finite and continuous cohomology maps.

The same `descendedEquiv F` is chosen simultaneously for every `F`, before
the target extension or its closure embedding is specified. Thus the
assembly gives precisely the quantifier order required by the target.
The direct comparison uses each specified closure embedding and does not
require an extra closure-independence hypothesis.

## Provenance and authorship

This module is an internal derived application of the named published
construction and proofs. Its new proof term consists entirely of supplying
those six witnesses. The detailed constructions, arithmetic normalizations,
valuation arguments, continuous-cohomology comparisons and original
literature correspondences remain in their linked published pairs.
The proof uses the cohomological objects of the target throughout.

Worker 154 wrote this final application and its explanation, and authored
the published conditional assembly. The other inputs are reused by import
and retain the authorship recorded in their published pairs. No unpublished
peer draft is copied into this module. This result asserts the exact
existence and restriction law; it makes no additional uniqueness claim.
