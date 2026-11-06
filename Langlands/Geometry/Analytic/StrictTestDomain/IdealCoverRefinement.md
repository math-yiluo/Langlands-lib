# Strict rational ideal descent under refinement

This derived internal module transfers ideal effectiveness from a finite
rational point-covering refinement to an original rational family.

`refinedIdealFamily` extends each original ideal along its chosen actual
refinement restriction. Compatibility on arbitrary common bounded affinoid
tests proves compatibility of the refined family. It also identifies the
closed extensions of the original and refined ideals on the actual
coefficient pullback of every refined component to every original component.

The explicit contractions of the original and refined families agree.
One containment follows from the restriction base-map equation. For the
other, test each original ideal on the rational point cover obtained by
pulling the refined cover back to that component. The compatibility
identification and the actual structural square give membership on every
component of this cover. The strict rational ideal-locality theorem then
gives membership in the original ideal.

`IdealCoverDescent.of_refinement` assumes effectiveness for the refined
family. On each original component, pull back the refined rational cover
and compare extensions of its original ideal with extensions of the
global contraction. The structural square, refined effectiveness and
contraction identity give equality on every pulled-back member.
Ideal locality detects equality in the original component. The reindexing
corollary uses a bijective index change as a refinement by identity maps.

The nontrivial coefficient-valuation condition is explicit and is used for
the available strict ideal-locality theorem. Empty finite refinements,
empty spectra, nonreduced and zero quotient algebras are retained. This
module uses only the proved strict rational compatibility and locality
infrastructure. It does not prove effectiveness without the explicit
refined-family effectiveness premise.
