# Regularity under the literal normalizer

Author: Worker 1597.

This supporting construction uses the actual subgroup normalizer and the
published conjugation functor. It supplies a regularity predicate, its inner
equivalences, a vanishing result for intertwiners from noninner conjugates, and
a sufficient central-character separation criterion.

The motivating source is Waldspurger, *La formule de Plancherel pour les
groupes p-adiques (d'après Harish-Chandra)*, 2003, registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
printed p.276 / PDF p.42, the definition preceding Corollary III.7.3.
There the finite group `W(G|M)` acts on square-integrable classes, and
regularity means that no nonidentity element fixes the class. The present
definition is a derived actual-normalizer formulation for any subgroup of a
topological group. It does not construct that finite Weyl group or prove its
comparison with the literal normalizer quotient.

## Actual actions and regularity

Let `G : Type uG` be a topological group and `M` a subgroup. No local
compactness, reductivity or closedness is assumed.
`σ : SmoothRep.{0,uG,uV} ℂ M` has an independent carrier universe `uV`.
For `g ∈ N_G(M)`, `normalizerConjugation g` is the topological group
automorphism `m ↦ g⁻¹ m g` of the literal subgroup `M`. The published
`conjugationEquiv` supplies its inverse, continuity and group laws.
`normalizerConjugate g σ` pulls back the original action by this map and
keeps its carrier.

`IsNormalizerRegular σ` says that, for every such `g` outside `M`, there
is no equivariant linear equivalence from this conjugate to `σ`.
This is an isomorphism condition, without a scalar-action or
finite-dimensional interpretation. For `g ∈ M`,
`normalizerConjugateInnerEquiv` is the explicit equivalence `v ↦ σ(g)v`;
its inverse is `σ(g⁻¹)`. The representation laws prove the inverse and
intertwining identities. Consequently `isNormalizerRegular_iff` says
that exactly the normalizer elements in `M` fix the class.

Conjugation preserves and reflects irreducibility by the published
surjective group-transport theorem. If `σ` is irreducible and regular,
`normalizerConjugate_hom_eq_zero` proves that every intertwiner into `σ`
from a conjugate with `g ∉ M` is zero. Mathlib's irreducible-map theorem
makes a nonzero such map bijective; its induced equivalence would violate
regularity. This argument does not use Schur's scalar theorem,
admissibility, or finite dimension.

## Central-character separation

`normalizerConjugateCentralCharacter g ω` is the character
`z ↦ ω(g⁻¹ z g)` on the full abstract center of `M`, using the actual
center automorphism induced by `normalizerConjugation g`. If `ω` acts
by scalars on `σ`, the conjugate has this displayed scalar central
character, as shown by `normalizerConjugate_hasCentralCharacter`.

For nonzero `σ`, if this character differs from `ω` for every `g ∉ M`,
then `isNormalizerRegular_of_centralCharacter` proves regularity.
An alleged equivalence intertwines the two scalar center actions.
Evaluating at a nonzero vector and cancelling its nonzero image forces
the character values to agree everywhere, a contradiction.

## Consumer boundary

These are derived constructions and elementary proofs, using the
published actual smooth pullback and inverse-conjugation constructions
and Mathlib's irreducible-map and center-transport results. The source
motivates the predicate; no source representation-theoretic theorem is
asserted as proved here.

There is no existence theorem for a regular twist, no finite set of
Weyl bad-locus equations, and no Jacquet-module decomposition or
multiplicity bound. Those remain necessary for the parent actual
unramified generic-irreducibility theorem. In particular, using the
finite group of the source requires a separate structural comparison.
