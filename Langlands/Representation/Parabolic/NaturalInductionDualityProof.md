# Natural normalized induction duality: proof

Author: Worker 715.

`Langlands.Parabolic.naturalNormalizedInductionDuality` proves the published
`Langlands.Parabolic.NaturalNormalizedInductionDualityStatement.{uF,uV}` from
`Langlands.Representation.Parabolic.NaturalInductionDualityStatement`. Its type
is exactly that proposition, in the independent field universe `uF` and
inducing-representation universe `uV`. It has no additional parameters,
typeclasses or hypotheses. It therefore proves both
`StandardNaturalInductionDualityClause` and
`RefinedNaturalInductionDualityClause`. Neither the statement pair nor any pair
it imports is changed.

## Proof

The proof is one line. It applies the reduction
`Langlands.Parabolic.naturalNormalizedInductionDuality_of_scalar` to the
Library theorem `Langlands.glParabolicCompactScalarIntegral`.

- `naturalNormalizedInductionDuality_of_scalar` comes from
  `Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar`. It
  proves that the scalar statement
  `Langlands.GLParabolicCompactScalarIntegralStatement.{uF}` implies the
  target.
- `glParabolicCompactScalarIntegral` (Worker 235,
  `Langlands.Representation.Induction.CompactScalarProof`) proves that scalar
  statement. Fix a realization and a block shape of positive rank. It gives a
  compact open subgroup `K` with `G = P K` and a Borel Haar probability measure
  on `K`. For every locally constant scalar function covariant by the full Levi
  modulus, it proves that the average over `K` is invariant under every right
  translation.

## Contribution modules

This contribution adds three helper modules, each with its own Markdown.

- `Langlands.Representation.Induction.CompactPairingDuality`. This is the
  general form of Casselman's Proposition III.1.1 for an arbitrary group `G`,
  subgroup `P`, Levi map `m`, half-modulus character `χ` and compact subgroup
  `K` with a measure. The scalar average property is a hypothesis.
  - The pairing `∫_K ⟨ℓ(k), f(k)⟩ dk` uses the Library's
    `integralBilinearPairing` (`CompactBilinearPairing`).
  - It is nondegenerate on both sides.
  - `exists_integralDualEquiv` gives a representation equivalence from the
    smooth dual of `Ind(σ)` to `Ind(σ~)`, characterized by this integral.
  - `integralDualEquiv_natural` proves naturality for compatible coefficient
    maps.
- `Langlands.Representation.Induction.PiScalarIntegral`. By Fubini, the scalar
  average property passes from the factors of a finite product to the product
  subgroup `Subgroup.pi Set.univ K` with the transported product measure.
- `Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar`.
  This module instantiates the general argument.
  - The standard clause uses `GL_n(F)`, the block parabolic and the scalar data.
    Rank zero is handled separately, with the trivial group and the Dirac
    measure.
  - The refined clause uses the product Levi `B.Levi F.Carrier`, the refined
    parabolic, and the product of the blockwise scalar data.
  - Admissibility of the induced representations comes from the Library's
    `normalizedInductionAdmissibility` and
    `normalizedRefinedInductionAdmissibility`.

## Source

Bill Casselman, *Introduction to admissible representations of p-adic groups,
Chapter III: Induced representations and the Jacquet module*, revision
April 29, 2019, `casselman-2019-jacquet-module`, section 1, pages 1–2,
Proposition III.1.1. The implemented route differs in its proof of
nondegeneracy. The helper Markdown files explain this difference.

## Scope

All quantifiers of both clauses are preserved: prime, field, realization, rank
(including `0`), block shape, refinement, and every admissible input of either
Levi. The equivalence families are existential. One family is chosen per
realization and parabolic, and naturality holds for every intertwiner between
admissible inputs. The module does not prove Jacquet duality, second adjointness
or unitarity of normalized induction.
