# Vector factors of smooth connected commutative p-torsion groups

`Langlands.GroupScheme.RelativeRoot.CommutativePTorsionVectorFactorStatement`
is the existence assertion of Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, second edition (2015), Theorem B.2.5, printed p.569 (one-based
PDF p.595). The registered source is
`conrad-gabber-prasad-2015-pseudo-reductive`, content SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.

For every field `k` of prime characteristic `p`, a smooth connected
commutative affine actual group scheme `U` killed by `p` is isomorphic
over `k` to a product `V × W`. The output consists of actual ground-field
group schemes and an actual group-scheme isomorphism. The product uses
the existing categorical product of group schemes. `V` has natural
finite-dimensional vector coordinates on every relative scheme test,
expressed by `RelativeRoot.IsVectorGroup`. These are equivalent to an
actual isomorphism with a standard vector group, as proved in
`Rational.VectorGroupCoordinates`.

The complement `W` is an actual commutative smooth connected affine group
scheme satisfying the existing representation-theoretic `IsUnipotent`
predicate. After the canonical base change to `SeparableClosure k`, it
satisfies `HasConstantAffineLineMaps`: every morphism from the affine line
over that field is a constant morphism to a point over that field. This
is the source's woundness condition from Definition B.2.1. The conclusion
retains constancy over the separable closure, which is stronger than
asserting constancy only over the ground field without a descent result.

The input torsion condition is `HasUniformPowerExponent U.toGrp p`,
quantifying every point on every relative scheme test, including
nonreduced schemes. No perfectness, infinitude, algebraic closedness,
unipotence comparison, or coordinate presentation is assumed. Smoothness
and affineness give the source's finite-type setting. There is no
positive-dimension requirement on either factor, so trivial groups and
zero-dimensional vector factors are included.

This module defines a proposition and supplies no proof. The source also
characterizes the vector subgroup canonically using affine-line images
and proves its uniqueness; those assertions are outside this focused
existence target. A proof of the proposition must construct the actual
factors and the isomorphism and justify `IsUnipotent` for the complement;
it cannot assume a vector embedding or the required decomposition as an
extra structural premise. The intended application is the
positive-characteristic portion of the central additive-subgroup
criterion. This statement alone does not prove that criterion or its
characteristic-zero case.
