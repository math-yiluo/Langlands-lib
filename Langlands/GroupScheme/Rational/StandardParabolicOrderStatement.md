# The order on standard parabolics

`StandardParabolicOrderStatement` states, for `J,K ⊆ Δ`, that `J ⊆ K` is
equivalent to `standardParabolic i ν J ≤ standardParabolic i ν K`. For such an
inclusion it also asserts the covariant Levi inclusion and contravariant
unipotent inclusion. A separate conjunct states injectivity of the map from the
subtype of subsets of `Δ` to standard parabolic subgroup functors.

Every field `k : Type u` is quantified over. The group scheme `G` is assumed
`IsConnectedReductive`, the homomorphism `i : T.toGrp ⟶ G` is assumed
`IsMaximalSplitTorus`, and `ν : cocharacterLattice T` is assumed
`IsGenericCocharacter i ν`. Affineness and the monomorphism of `i` are obtained
from those assumptions. Write `Δ = simpleRelativeRoots i ν`. Subsets are actual
sets of characters, with explicit containment in `Δ`. There is no assumption of
reducedness, characteristic, perfectness, splitness or quasi-splitness; `Δ` may
be empty.

The **derived** `SubgroupFunctor` form means inclusion on every test scheme;
it does not replace that condition by rational-point inclusion. Borel–Tits
§5.14 (printed pp.99–100) classifies the standard parabolics, and §5.18(ii)
(printed p.101) gives the inclusion criterion and its conjugation refinement on
rational points. The Levi and unipotent directions also follow directly from
the standard root subsets of §5.12 with §4.2 (printed pp.85–86,99). The
cocharacter positivity and choice-free intersections imported from
[StandardParabolic](StandardParabolic.md) are derived reformulations of those
source constructions.

This file defines a proposition target. It supplies no proof or structural
axiom, and no instance asserting the proposition. The general proof remains an
obligation of the reductive-group program.

Source IDs: `borel-tits-1965-groupes-reductifs`.
