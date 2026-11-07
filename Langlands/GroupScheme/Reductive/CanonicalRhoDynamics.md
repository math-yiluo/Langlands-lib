# Canonical polarized-rho dynamics

This internal derivation starts with a supplied finite integral root datum,
a base, and the hypothesis that its coroots span the entire integral
cocharacter lattice. The root index, character lattice, and cocharacter
lattice may lie in different universes. No reducedness is needed for the
root-sign comparison.

The canonical root form pairs rho positively with each simple root:
twice this value is the root's squared norm because rho evaluates its
coroot to one, and the squared norm is at least four. Mathlib's positive
root induction extends positivity to every positive root by additivity.
If a root is not positive, its negative is positive, so the value on the
original root is negative. The defining polarization identity gives
`pairing_root_polarization_rho_pos_iff`.

For an actual affine group scheme over a field, supply a commutative group
scheme `T`, its homomorphism `j` into the group, and a root datum on this
same torus's lattices satisfying `IsRootDatumOf j P`. That predicate
identifies both the pairing and the entire root set with the actual ones.
Consequently the actual roots positive on polarized rho are exactly the
image of the base-positive root indices. `positiveRhoCocharacter` bundles
this canonical cocharacter with genericity and the complete sign
certificate.

If the ambient group is connected reductive and `j` is a split maximal
torus, the published generic-centralizer theorem identifies the dynamic
centralizer with the torus centralizer. The published maximal-torus
centralizer theorem identifies the latter with the range of the original
`j`. The closed immersion in maximality supplies the monomorphism, so
`j` itself represents the canonical dynamic centralizer. These are
equalities and representability on every relative test scheme.

The structural inputs are supplied. This file does not prove their
existence or construct highest-weight modules, Steinberg modules, or
entire induced spaces. The host Steinberg big-cell proposition remains
a separate proof obligation.
