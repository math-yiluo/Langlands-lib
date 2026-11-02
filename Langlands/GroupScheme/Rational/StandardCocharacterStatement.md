# Standard cocharacters and choice-free standard subgroups

`StandardCocharacterStatement` states that each subset `J ⊆ Δ` has a standard
cocharacter. For every standard cocharacter `zeta` for that same subset, all three
choice-free standard subgroup functors are equal to its published dynamic
parabolic, centralizer and unipotent functors. The assertions are equalities of
`SubgroupFunctor G`, hence apply to every test scheme, with no separate point
model or chosen witness hidden in a parameter.

Every field `k : Type u` is quantified over. The group scheme `G` is assumed
`IsConnectedReductive`, the homomorphism `i : T.toGrp ⟶ G` is assumed
`IsMaximalSplitTorus`, and `ν : cocharacterLattice T` is assumed
`IsGenericCocharacter i ν`. Affineness and the monomorphism of `i` are obtained
from those assumptions. Write `Δ = simpleRelativeRoots i ν`. Subsets are actual
sets of characters, with explicit containment in `Δ`. There is no assumption of
reducedness, characteristic, perfectness, splitness or quasi-splitness; `Δ` may
be empty.

The provenance is **derived**. Borel–Tits constructs the standard root subsets
and groups in §4.2 (printed pp.85–86), transfers them to relative roots over the
base field in §5.12 (p.99), and obtains field-defined Levi and unipotent factors
through §3.13 (pp.78–80). Renard V.4.2, Proposition (printed p.118), describes the
same standard root triples over a nonarchimedean local field. Replacing the
source order by signs of the generic cocharacter, expressing the face by zero
pairing on `J` and positive pairing on `Δ \ J`, and realizing the groups by
intersections over all standard cocharacters are derived reformulations. In
particular, existence is asserted here, rather than built into the definitions.
The possibly empty root system is retained.

This file defines a proposition target. It supplies no proof or structural
axiom, and no instance asserting the proposition. The general proof remains an
obligation of the reductive-group program.

Source IDs: `borel-tits-1965-groupes-reductifs`, `renard-2026-representations-groupes-reductifs-padiques`.
