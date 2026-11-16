# Cocharacters adapted to a convex root subset

For a finite set of actual characters of a split torus that is stable under
negation, every convex subset admits an integral cocharacter nonnegative on
that subset. Among the entire ambient character set, its zero pairings occur
exactly on the symmetric part of the subset. This is an internal consequence
of closed-cone separation and the actual split-torus lattice pairing.

For each asymmetric character in the subset, the negative of its real tensor
lies outside the defining closed cone. Separation and a finite sum produce
a real linear functional nonnegative on the cone and strictly positive on
every asymmetric character. Both signs of a symmetric character lie in the
cone, so this functional vanishes on the symmetric rational span. Rational
approximation on the quotient by that span preserves these zero values and
the finitely many strict positive values. Clearing denominators realizes the
functional by an integral cocharacter.

A second integral cocharacter detects the symmetric rational span among the
ambient characters. A sufficiently large integral multiple of the first
cocharacter plus the second preserves positivity on the asymmetric part and
has zeros precisely in that span. The convex symmetric-span saturation
theorem identifies these ambient characters with the symmetric part.

The Prop-valued `ConvexRootCocharacterStatement` packages this assertion over
all fields in universe `u`, split tori, finite negation-stable ambient character
sets and convex subsets. The theorem `convexRootCocharacter` proves that
proposition. This supporting unit does not prove a group-subset intersection
or identify a Weyl group.
