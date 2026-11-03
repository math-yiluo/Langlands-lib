# Ideals of connected closed subgroups of corepresented groups

Let `F` be a group-valued functor on commutative `R`-algebras corepresented by `B`
(`e : (F ⋙ forget GrpCat).CorepresentableBy B`), and `groupScheme F e = Spec B` the
corresponding affine group scheme. This module records that a connected closed subgroup
of `Spec B` is cut out by an ideal `I` of `B` such that `B ⧸ I` has no nontrivial
idempotents. All declarations are in namespace `Langlands.GroupScheme.Corepresented`.

## Statements

- `HasTrivialIdempotents A` says that the only idempotents of the commutative ring `A`
  are `0` and `1`.
- `hasTrivialIdempotents_of_connectedSpace`: if `PrimeSpectrum A` is connected, then
  `HasTrivialIdempotents A`.
- `exists_ideal_range_of_connectedSpace`: let `j : K ⟶ groupScheme F e` have underlying
  morphism a closed immersion, with `K.X.left` connected. Then there is an ideal `I` of
  `B` with two properties:
  - for every test scheme `U` over `Spec R`, a point `y : U ⟶ Spec B` lies in
    `SubgroupFunctor.range j` iff its classifying algebra map
    `e.homEquiv.symm (pointsEquiv F e U y)` kills `I`;
  - `HasTrivialIdempotents (B ⧸ I)`.

## Proofs

For the idempotent lemma, an idempotent `c` gives a clopen subset of `PrimeSpectrum A`
(Mathlib's `PrimeSpectrum.isIdempotentElemEquivClopens`, Stacks 00EE). Connectedness
makes it `⊥` or `⊤`, and these correspond to `0` and `1`.

For the closed subgroup, `IsClosedImmersion.Spec_iff` gives an ideal `I` and an
isomorphism `ε : K.X.left ≅ Spec (B ⧸ I)` identifying `j` with the closed immersion of
`Spec (B ⧸ I)`. The description of the points follows the Library's
`Corepresented.exists_ideal_range` (`NormalizerRepresentability`). It uses the
factorization criterion `Langlands.AlgebraicGeometry.factorsThrough_affineQuotient_iff`
and `homEquiv_symm_pointsEquiv_apply`. That theorem does not expose its ideal, so its
argument is repeated here with the ideal from `Spec_iff`. Since `ε` is a homeomorphism,
`PrimeSpectrum (B ⧸ I)` is connected when `K.X.left` is.

## Provenance

Internal supporting material for the proof of
`Langlands.GroupScheme.RelativeRoot.CyclicWeightFiltrationStatement` (task 023326af). It
supplies the inputs of `le_weightSubgroup` (`Rational.TorusWeightTangent`) for a smooth
connected closed generator of the filtration: an ideal cutting it out, and the absence of
nontrivial idempotents in its coordinate ring. The characterization of clopen sets of a
prime spectrum by idempotents is Stacks Project Tag 00EE, as formalized in Mathlib.
