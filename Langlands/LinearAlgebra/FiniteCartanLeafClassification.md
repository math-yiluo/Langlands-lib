# Allowed leaf extensions of standard Cartan matrices

This intermediate development converts the positive-column inequalities into
restrictions on attachment positions.

For A, a single edge may attach at an endpoint, next to an endpoint, or two
vertices from an endpoint in ranks five through seven. A double edge can
attach only at an endpoint; a triple edge forces the old rank to be one.
For B and C, only a single edge is possible: at the first vertex in any
rank, or at the last vertex in rank two or three. For D, only a single edge
is possible: at the first vertex in any rank, or at either fork endpoint
through rank seven.

The bounds are proved by integer arithmetic from the previously constructed
nonnegative columns. Their role is to reduce all remaining extension
numberings to the infinite families already handled and finitely many
explicit exceptional cases.

The module now also constructs the complete exact classification for all
allowed A/B/C/D leaf extensions. The infinite cases use the previously
proved reflection and cyclic numberings. The remaining finite cases use
explicit bijections checked entry by entry by Lean: branching A-chains give
E6/E7/E8, the end extensions in B/C ranks two and three give B/C or F4, and
the fork extensions of D4 through D7 give D5 or E6/E7/E8.
