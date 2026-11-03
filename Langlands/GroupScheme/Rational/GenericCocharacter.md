# Existence of generic integral cocharacters

Author: Worker 1262.

This internal deduction uses the published actual torus lattices, relative
roots, finite Lie weight support, and denominator-clearing construction. It
does not require a relative root-system theorem.

`IsSplitTorus.exists_pairings_ne_zero` treats any finite set of nonzero
characters of an actual split torus over an arbitrary field. Rationalization
is injective on that character lattice, so these characters remain nonzero
in its rational vector space. Mathlib's
`Module.exists_dual_forall_apply_ne_zero` chooses a rational linear functional
nonzero on every one of them: a finite union of proper hyperplanes cannot
cover a vector space over the infinite field of rational numbers.
`IsSplitTorus.exists_positive_multiple_pairing` realizes a positive integer
multiple of this functional by an actual integral cocharacter. The multiplier
and the chosen functional values are nonzero, so each resulting pairing is
nonzero. The ground field itself need not be infinite.

`IsSplitTorus.exists_genericCocharacter` applies that construction to the
actual relative roots of any homomorphism into an affine group scheme
locally of finite type over the ground field. The published
`IsSplitTorus.finite_relativeRoots` in `Rational.RootSupportFiniteness` supplies
finiteness from the finite-dimensional actual Lie kernel and its internal
weight decomposition. The definition of relative roots supplies their
nonzeroness. Neither an embedding nor maximal splitness, smoothness,
connectedness, or reductivity is required for this existence result.

`genericCocharacterOfIsSplitTorus` chooses the integral cocharacter.
Its specification proves exactly the published `IsGenericCocharacter`
predicate, including when the root set is empty or the torus has rank zero.
All results have arbitrary universe `u`.

Finally, `IsMaximalSplitTorus.exists_minimalParabolic_containing` specializes
existence to a maximal split torus of a connected reductive group. Smoothness
provides local finite type, and reductivity provides affineness. The theorem
then applies the published containment bridge with a generic cocharacter
just constructed. Its explicit additional premise is the still unproved
`GenericMinimalParabolicStatement`. The conclusion gives an actual minimal
parabolic and an actual torus factorization through its embedding. This
last deduction removes the need to supply a generic cocharacter; it does
not prove the generic-minimality statement, conjugacy, or Bruhat decomposition.
