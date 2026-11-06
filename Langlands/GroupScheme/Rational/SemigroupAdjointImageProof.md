# Actual semigroup fppf images under adjoint quotients

Worker 1284. This module proves
`Langlands.GroupScheme.RelativeRoot.semigroupAdjointImage :
SemigroupAdjointImageStatement.{u}` for every universe `u`. The proposition is
the unchanged Library target in `Rational.SemigroupAdjointImageStatement`.

For an algebraically closed field of arbitrary characteristic, the target
supplies an actual adjoint quotient `q : G ⟶ Q`, a split acting torus, and
actions on `G` and `Q` that are equivariant on every test scheme. For every
additive character semigroup `A` with `0 ∈ A`, the conclusion is the actual
`SubgroupFunctor.IsFppfImage` from the source semigroup subgroup functor to the
target semigroup subgroup functor. It includes monic group-scheme
representatives and a commuting restriction morphism that is flat,
scheme-surjective and locally of finite presentation.

## Implemented proof

The proof applies the published theorem
`RelativeRoot.semigroupAdjointImage_of_fixedCenterContainingTorus` from
`Rational.SemigroupComparisonFourPrerequisites` to the published unconditional
theorem `Langlands.GroupScheme.fixedCenterContainingTorus` from
`Reductive.FixedCenterContainingTorusProof`. Both have the same arbitrary
universe `u`. No structural premise remains in the final theorem.

The reduction obtains smoothness of the ambient source and target groups
from `IsAdjointQuotient q`, together with flatness, scheme surjectivity and
local finite presentation of `q`. The fixed-torus theorem gives a closed
split torus in `G` containing the full scheme-theoretic centre and fixed by
the acting torus on all tests.
`center_le_semigroupSubgroup_of_fixedCenterContainingTorus` then puts the full
centre in the source semigroup subgroup: the action on this embedded torus
is trivial, so zero in `A` includes the whole torus. The identity
`hq.kernel_range_eq_center` turns this into containment of the entire actual
kernel of `q`. The reduction applies
`isFppfImage_semigroup_of_kernel_le` from
`Rational.SemigroupFppfKernelTransport` to obtain the required actual fppf
image.

The imported transport proof uses the represented inverse image of the
target semigroup subgroup. Full kernel containment and the split-torus
weight decomposition give the same Lie image as the source semigroup
subgroup. Its inclusion into that inverse image is an open immersion. The
composite with the pullback projection is flat and locally of finite
presentation, and the flat-homomorphism surjectivity theorem supplies scheme
surjectivity onto the smooth connected target representative.

All containments and equivariance identities retain arbitrary test schemes,
including nonreduced tests. Smoothness is used for the two ambient groups;
neither the adjoint quotient morphism nor its full centre kernel is assumed
smooth. The theorem keeps the original field, universe and semigroup
hypotheses.

## Provenance

This is an internal composition of the named published Library theorems.
Worker 1372 supplied the sufficient reduction; the fixed-torus proof is
Worker 1544's published assembly, using the semidirect-product route proposed
by Worker 1334.

The target's source is Conrad, Gabber and Prasad, *Pseudo-reductive Groups*,
second edition (2015), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, proof of Proposition 3.3.10(c),
printed p.113 / PDF p.139. That proof chooses a fixed maximal torus and
compares root-subgroup descriptions across the full-centre quotient,
explicitly allowing the quotient to be nonsmooth. The implemented route
uses the fixed centre-containing torus to establish the essential full-kernel
containment, then invokes the published weight-and-Lie transport argument
described above.
