# An abelian scheme realizing the prime-power torsion closure

This module realizes the closure of `PrimePowerTorsion.locus A p` as an actual
closed subgroup scheme, and, over an algebraically closed characteristic-zero
field with prime `p`, as an actual abelian scheme. The universe `u` is arbitrary.

The definitions `closureIdeal`, `reducedClosure` and `reducedClosureι` use the
vanishing ideal of the closed torsion closure and its induced subscheme.
The subscheme is reduced, its inclusion is a closed immersion, and its
underlying image is exactly that closure. The identity factors through it.
The inversion and translation isomorphisms restrict through the vanishing
ideal because they preserve the closed subset. This proves
`reducedClosure_exists` over every field for every natural number `p`.

Assume the field is algebraically closed. Any two closed points of this reduced
closure have field-valued sections. Their translations send the identity to
the respective points, so composing one inverse translation with the other
gives an automorphism carrying one point to the other. The published
`closedPointHomogeneousSmooth` theorem consequently proves smoothness.
This gives `smoothClosure_exists`.

The product of the smooth closure with itself is reduced and Jacobson.
The ambient group multiplication sends every closed point of that product
back into the closure, by `closureSectionSubgroup`. The relevant inverse
image is closed, so density of closed points puts the full multiplication
image in the closure. The published reduced-source factorization lemma
then factors multiplication through the closed immersion.
`GroupObjectDescent.grpObjOfMono` descends the group identities and
commutativity along the monomorphism. Properness follows from the closed
immersion into the proper ambient abelian scheme.
Thus `closureGroupScheme_exists` gives an actual smooth proper commutative
group scheme over every algebraically closed field for every natural `p`.

For characteristic zero and prime `p`, the preceding closure module proves
connectedness of its underlying image. The closed immersion transfers it to
the subgroup scheme. The published `algClosedConnected` theorem promotes
connectedness to geometric connectedness over the algebraically closed field.
The resulting object is an `AbelianScheme`, and
`closureAbelianScheme_exists` supplies its homomorphism into `A` with the
specified closed image.

These are derived internal constructions, generalizing the published
two-power reduced, smooth, group-scheme and abelian-scheme closure proofs in
`Langlands.AbelianScheme.Tate`. The generic factorization lemma is reused
from `TwoPowerTorsionClosureGroupGeometry`; it has no specialization to the
number two in its statement. The geometric aim is Edixhoven, van der Geer
and Moonen, *Abelian Varieties*, preliminary version, Chapter V, §3,
Theorem (5.30), printed p.84 / PDF p.88
(`edixhoven-vandergeer-moonen-abelian-varieties-draft`). These helper
constructions describe the implemented closed subgroup route to its
characteristic-zero density consequence.
