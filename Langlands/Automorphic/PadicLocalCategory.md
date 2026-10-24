# Canonical p-adic classes of actual automorphic local components

This internal adapter places the actual local form subspaces of
`PresentedLocalCategory.lean` in the existing correspondence category for the
canonical p-adic field of a finite place. It retains their original algebraic
actions and their actual form-space carriers.

## Inputs and provenance

Let `F : Type uF` be a number field and `v` a finite place. Smoothness and
admissibility comparisons apply to every natural matrix rank. The correspondence
objects and classes have positive rank `r + 1`, written `r.succPNat` in the
correspondence interface. They require explicit irreducibility and admissibility
of the actual local subspace for the existing completed-local topology.

The provenance is internal. `FiniteAdelicGL.localGL_topology_eq` proves that
the actual completion matrix topology equals the canonical p-adic matrix
topology. `localIntegral_eq_sphericalSubgroup` identifies the actual integral
subgroup with the correspondence's spherical subgroup. The carrier field and
algebraic matrix group are definitionally the same. The module combines these
comparisons with the published actual subspace constructions, genuine
isomorphism-class equality, and invariance of nonzero fixed spaces under an
equivariant linear equivalence. It asserts no new result from external literature.

## Actual subspace adapter

`LocalRealization.isSmooth_canonical` transports the published smoothness proof
along the topology equality. `isAdmissible_canonical_iff` rewrites that same
equality in the existing admissibility predicate, which includes smoothness
and finite generation of the fixed space for every open subgroup.

`padicObject` bundles the same actual form subspace and local action, using
canonical smoothness and the supplied irreducibility and admissibility proofs.
`padicClass` takes its existing `Correspondence.AutomorphicClass`. Both use
the actual form-carrier universe `uF`, without changing or resizing the carrier.

`padicClass_eq_iff` applies the correspondence quotient's equality criterion
to identify class equality with a genuine equivariant linear equivalence of
the actual local actions. `padicClass_eq_iff_isoClass_eq` then identifies it
with equality of their original smooth classes. These compare representations;
they do not identify the two embedded subspaces as subsets of forms.

`padicClass_isSpherical_iff` states that the correspondence class is spherical
exactly when the actual local action has a nonzero vector fixed by the actual
integral subgroup. For the forward implication, a witness representing the
same class is equivariantly isomorphic to the actual form subspace, so its
nonzero spherical fixed space transfers. The reverse implication uses the
actual form subspace itself as the representative. Both use the proved subgroup
equality.

## Genuine tensor presentations

For a genuine tensor presentation `P` onto a nonzero finite-adelic-invariant
subspace of actual forms, `localPadicObject` and `localPadicClass` apply the
adapter to its actual embedded local component. Irreducibility and admissibility
remain explicit hypotheses on the specified model factor. The factor carrier
universe `uV` is independent of the field and form-carrier universe `uF`.

`localPadicClass_eq` compares two nonzero presentations of fixed tensor data,
even with different actual target subspaces. It combines the new equality
criterion with the published independence of the underlying smooth class.
`localPadicClass_isSpherical_iff` transfers the integral-fixed-space condition
back through the genuine factor-to-component equivalence. Outside the supplied
finite exceptional set, `localPadicClass_isSpherical` uses the presentation's
nonzero integral-fixed reference vector via the published fixed-vector result.

## Scope

The object construction is conditional on a genuine presentation and explicit
local irreducibility and admissibility. It does not prove general factorization,
uniqueness across different factor families, or local properties of arbitrary
automorphic factors. Sphericality is the existing nonzero-fixed-vector condition;
no fixed-space dimension, Hecke character, normalized Satake parameter, or
local correspondence theorem is asserted. The topology comparison changes only
the category's group topology expression and its property proofs, while the
algebraic action and actual embedded carrier are retained.
