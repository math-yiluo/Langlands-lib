# Finite twisted upper-unipotent coinvariants of irreducible representations

Author: Worker 499.

`Langlands.Whittaker.irreducibleCoinvariantFiniteness` proves exactly
[`IrreducibleCoinvariantFinitenessStatement.{uF,uV}`](IrreducibleCoinvariantFinitenessStatement.md).
For every prime `p`, p-adic field `F`, supplied topological data `T`, rank
`n : ℕ`, irreducible smooth complex representation `ρ` of the actual
`GL_n(F)`, and locally constant complex-valued unit character `θ` of its
actual upper-unipotent subgroup `U`, the actual quotient
`Jacquet.Localization.Coinvariants ρ U θ` is finite-dimensional over `ℂ`.
This is the finiteness assertion of Bernstein–Zelevinsky (1976),
Theorem 5.21, printed p.51.

The field universe `uF` and representation-carrier universe `uV` remain
independent. The theorem has no added premises. All topology instances
come from the supplied `T`. Arbitrary, trivial and degenerate characters
are included, and rank zero is included. The theorem establishes finite
dimension; it does not state a numerical dimension bound.

## Implemented proof

The proof composes published results. Its two auxiliary theorems are
private to the module.

At positive rank,
[`CuspidalSupport.cuspidalEmbedding`](../CuspidalSupport/CuspidalEmbeddingProof.md)
gives an actual block shape `B`, an irreducible cuspidal smooth
representation `σ` of `B.Levi F.Carrier`, and an injective intertwiner
`j` from `ρ` into the normalized induction

```lean
Induction.smoothInduced (B.parabolic F.Carrier)
  (twist (T.parabolicHalfModulus B)
    (σ.representation.comp (B.leviProjection F.Carrier)))
```

The published
[`leviCuspidalCoinvariantFiniteness`](LeviCuspidalCoinvariantFinitenessProof.md)
gives finite-dimensional character quotients of `σ` by the product of
its blockwise upper-unipotent groups for every locally constant
character. Feeding precisely this conclusion into
[`parabolicInducedCoinvariantFiniteness`](ParabolicInducedCoinvariantFinitenessProof.md)
makes the `θ`-quotient of the displayed normalized induction
finite-dimensional. Both applications use the original `F`, `T`, `B`
and `σ`; neither changes the inducing representation or the normalization.

The private helper
`irreducibleCoinvariantFiniteness_of_cuspidal_induction` implements the
remaining embedding argument. The linear map on quotients is
`Jacquet.Localization.mapLinear U θ j`. The published
[`upperUnipotent_isLimitOfCompactSubgroups`](../../Group/GL/UpperUnipotentCompactContainmentProof.md)
and
[`Jacquet.Localization.map_injective_of_smooth`](../Jacquet/LocalizationExactnessProof.md)
prove that this map is injective. The target representation is smooth
by `Induction.smoothInduced_smooth`; the character is locally constant
by the original hypothesis. To invoke the equivariant localization
interface, use the trivial auxiliary normalizing subgroup `⊥`.
Its character-invariance condition follows because its only element
is the identity. Its underlying map is the same `mapLinear`.
`FiniteDimensional.of_injective` now gives finite dimension of the
original quotient.

At rank zero, the private helper `finiteDimensional_rankZero` uses the
admissibility conclusion of `cuspidalEmbedding F T 0`. The actual group
`GL_0(F)` is a singleton. Consequently every vector is fixed by the full
open subgroup `K = ⊤`; that subgroup is compact because it is a singleton.
Admissibility makes its fixed-vector space finite-dimensional. The
inclusion of this fixed-vector space into the representation is
surjective, so `FiniteDimensional.of_surjective` makes the whole
representation finite-dimensional. The standard quotient instance
then gives the required finite-dimensional character quotient. This
argument supplies the zero-rank boundary case without adding a
positive-rank assumption to the theorem.

The final public theorem supplies the two published closed finiteness
theorems to the private embedding argument. No conditional finiteness
premise remains in its type.

## Source correspondence and provenance

The registered original is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local
field*, Russian Mathematical Surveys **31:3** (1976), 1–68, source ID
`bernstein-zelevinsky-1976-representations-gln`. Its retained PDF has
SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Printed pages equal one-based PDF pages. Theorem 5.21 and Corollary 5.22
are on printed p.51; the proof of Theorem 5.21 is in §§7.11–7.12,
printed pp.60–61. These passages were read during this task, and no
relevant erratum was found.

Section 7.11 reduces the irreducible case to a representation induced
from irreducible cuspidal Levi data, using exactness of character
localization. The present final assembly implements that reduction
with the published cuspidal embedding and localization-injectivity
theorems. Its rank-zero admissibility argument is an internal boundary
argument for the Library's natural-number indexing.

The two imported finiteness proofs implement the remaining §7.12
reduction: a finite orbit filtration reduces the induced quotient to
cuspidal Levi character quotients, and tensor factorization reduces
the latter to single-block cuspidal representations. Their paired
Markdown explains those proofs. The single-block proof uses a finite
spanning argument instead of the source's stronger multiplicity-one
assertion. The resulting chain proves the requested finite-dimensional
consequence of Theorem 5.21, without requiring the source's factorial
bound. The positive-character relation throughout is `ρ(u)v − θ(u)v`,
as in BZ76 Definition 2.30, printed p.24.

Only this proof pair is new. The published target pair and all its
imports are unchanged. The mathematical dependencies are imported by
their Lean names; neither an unproved multiplicity-one proposition
nor any additional finiteness hypothesis is used.
