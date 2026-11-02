# Classification of rational parabolics

`StandardParabolicClassificationStatement` has two clauses. A dynamic rational
parabolic containing the minimal parabolic is one of the standard functors.
For each dynamic rational parabolic, there is exactly one subset `J ⊆ Δ` for
which some point `g ∈ G(k)` conjugates it onto the standard functor indexed by
`J`. Uniqueness concerns `J`; no uniqueness of the point `g` is asserted.

The formula is
`Dynamic.parabolic zeta = (standardParabolic i ν J).comap (G.innerIso g).hom`.
The right-hand side consists, on every test scheme, of the points `x` such that
`g*x*g⁻¹` belongs to the standard parabolic (using the constant base-changed
point `g`). Because `innerIso` is an isomorphism, this equality says exactly that
conjugation carries the original functor onto the indicated standard one.

Every field `k : Type u` is quantified over. The group scheme `G` is assumed
`IsConnectedReductive`, the homomorphism `i : T.toGrp ⟶ G` is assumed
`IsMaximalSplitTorus`, and `ν : cocharacterLattice T` is assumed
`IsGenericCocharacter i ν`. Affineness and the monomorphism of `i` are obtained
from those assumptions. Write `Δ = simpleRelativeRoots i ν`. Subsets are actual
sets of characters, with explicit containment in `Δ`. There is no assumption of
reducedness, characteristic, perfectness, splitness or quasi-splitness; `Δ` may
be empty.

Borel–Tits §5.14 (printed pp.99–100) gives both standardness by containment and
uniqueness up to rational conjugation. Renard V.3.9 (printed p.112) records the
conjugacy assertion for nonarchimedean local fields. The arbitrary-field scope
comes from Borel–Tits. Using a `k`-cocharacter `zeta : Gm ⟶ G` to quantify over
rational parabolics is the published dynamic convention: Milne, *Algebraic
Groups* (2017), Theorem 25.1 (printed p.544; one-based PDF p.560) states that
these are exactly the parabolic subgroups of a reductive group over a field.
The `SubgroupFunctor`/`comap` formulation and the imported generic-cocharacter
and intersection definitions are **derived** reformulations.

This file defines a proposition target. It supplies no proof or structural
axiom, and no instance asserting the proposition. The general proof remains an
obligation of the reductive-group program.

Source IDs: `borel-tits-1965-groupes-reductifs`, `renard-2026-representations-groupes-reductifs-padiques`, `milne-2017-algebraic-groups`.
