# Simultaneous principal trivialization of actual rank-one weight spaces

Worker 634, with the interface requested by Worker 587 for Task 6260.

This is an internal consequence of Mathlib's finite-presentation localization
of bases and the Library's actual finite-projective Lie weight modules. The
specialized theorem supplies a principal neighbourhood contained in any chosen
open neighbourhood, on which finitely many actual exponent weight spaces,
each of rank one at the given point, are all isomorphic to the base ring.
No noetherian, reduced, connected or local-ring hypothesis is imposed.

The defined type `splitTorus.ExponentWeightLineTrivialization` is the type of
linear equivalences from an actual exponent weight space to the base ring.
Its inhabitants are explicit choices of a free-line trivialization. The
specialized existence theorem returns inhabitants of this type after
principal localization.

The generic single-module theorem first uses finite projectivity to obtain a
free stalk, then spreads that finite basis to a principal localization with
the same rank. Rank one gives a linear equivalence with the localized ring.
Extension of scalars preserves this equivalence over every algebra in which
the chosen element is invertible. For a finite family, take the product of
these elements and an element whose basic open lies inside the prescribed
open. All factors are invertible after inverting their product.

The actual-weight theorem applies this module argument to
`splitTorus.exponentWeightSpace`. Finiteness and projectivity are the published
instances in `RelativeAdjointWeightRanks`, with their underlying-ring variants
in `GeometricAdjointWeightRanks`. The equivalence from
`RelativeAdjointWeightBaseChange` identifies the scalar extension with the
actual weight space of the base-changed group and coordinate torus.

The hypotheses supply the finite exponents and their rank-one condition. This
module constructs neither maximal tori nor root data and does not by itself
prove étale-local splitting of a reductive group.
