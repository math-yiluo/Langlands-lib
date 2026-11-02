# Standard parabolics inside standard Levis

`StandardLeviIntersectionStatement` quantifies over `J ⊆ K ⊆ Δ`. At each test
scheme `Q`, set
`H = (L_K ⊓ P_J)(Q)`, `V = (L_K ⊓ U_J)(Q)` and `L = L_J(Q)`.
The assertion includes `V ≤ H` and `L ≤ H`, normality of `V` as a subgroup of
`H`, and `V.IsComplement' L` inside `H`. The complement assertion expresses
bijectivity of multiplication `V × L → H`; together with normality, this is
the semidirect Levi decomposition on every test scheme.

The other conjunct is the set equality on rational points
`U_J(k) = (L_K(k) ⊓ U_J(k)) * U_K(k)`.
The product is the pointwise product of subsets of the actual group `G(k)`;
it is not an equality in an auxiliary abstract model.

Every field `k : Type u` is quantified over. The group scheme `G` is assumed
`IsConnectedReductive`, the homomorphism `i : T.toGrp ⟶ G` is assumed
`IsMaximalSplitTorus`, and `ν : cocharacterLattice T` is assumed
`IsGenericCocharacter i ν`. Affineness and the monomorphism of `i` are obtained
from those assumptions. Write `Δ = simpleRelativeRoots i ν`. Subsets are actual
sets of characters, with explicit containment in `Δ`. There is no assumption of
reducedness, characteristic, perfectness, splitness or quasi-splitness; `Δ` may
be empty.

Renard V.3.10–V.3.11 (printed p.112) describes the intersection of
semi-standard parabolics with a Levi and the bijection for parabolics contained
in a fixed parabolic. Applying that description to nested standard parabolics
gives exactly these factors. Renard works over a nonarchimedean local field.
Borel–Tits §5.12 with §4.2 (printed pp.85–86,99), using the root-subset Levi
and unipotent decompositions, supplies the arbitrary-field construction.
The all-test `SubgroupFunctor` formulation, as well as the imported
cocharacter-positivity and intersection constructions, is **derived**. The
rational-point product is the specialization of the corresponding source root
factorization.

This file defines a proposition target. It supplies no proof or structural
axiom, and no instance asserting the proposition. The general proof remains an
obligation of the reductive-group program.

Source IDs: `borel-tits-1965-groupes-reductifs`, `renard-2026-representations-groupes-reductifs-padiques`.
