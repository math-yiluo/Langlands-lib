# The endpoints of standard parabolics

`StandardParabolicEndpointsStatement` gives five equalities of subgroup
functors: at `J = ∅`, the standard parabolic is
`Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)` and the standard Levi is
`torusCentralizer i`; at `J = Δ`, the parabolic and Levi are the full subgroup
functor and the unipotent functor is the identity subgroup functor.

Every field `k : Type u` is quantified over. The group scheme `G` is assumed
`IsConnectedReductive`, the homomorphism `i : T.toGrp ⟶ G` is assumed
`IsMaximalSplitTorus`, and `ν : cocharacterLattice T` is assumed
`IsGenericCocharacter i ν`. Affineness and the monomorphism of `i` are obtained
from those assumptions. Write `Δ = simpleRelativeRoots i ν`. Subsets are actual
sets of characters, with explicit containment in `Δ`. There is no assumption of
reducedness, characteristic, perfectness, splitness or quasi-splitness; `Δ` may
be empty.

Borel–Tits §5.12 (printed p.99) identifies the empty-subset group as minimal and
the full-subset group as `G`; its reference to §4.2(ii) (printed p.86) gives the
corresponding Levi and unipotent factors. Renard V.3.8 (printed p.111) fixes the
minimal Levi as the centralizer of the maximal split torus. Renard's setting is
a nonarchimedean local field; the arbitrary-field formulation comes from
Borel–Tits. The use of generic-cocharacter positivity and choice-free
intersection subgroup functors is **derived**, as documented in
[StandardParabolic](StandardParabolic.md). If `Δ` is empty, both endpoint
assertions apply to the same index, as required in the anisotropic case.

This file defines a proposition target. It supplies no proof or structural
axiom, and no instance asserting the proposition. The general proof remains an
obligation of the reductive-group program.

Source IDs: `borel-tits-1965-groupes-reductifs`, `renard-2026-representations-groupes-reductifs-padiques`.
