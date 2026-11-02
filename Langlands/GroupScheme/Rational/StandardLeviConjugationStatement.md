# Conjugating standard Levis

`StandardLeviConjugationStatement` has two clauses. If `J,J' ⊆ Δ` and the
class of a normalizing point `n` maps the roots in `J'` onto those in `J`, then
conjugation by `n` maps `standardLevi i ν J'` onto `standardLevi i ν J`.
The hypothesis is expressed using the published `relativeWeylAction` on
`relativeRootSpan i`: `rootSubset J` is the set of span elements whose ambient
rational-lattice image is `toRat α` for some `α ∈ J`. Thus the hypothesis uses
the actual relative Weyl quotient, not a separately supplied root permutation.

The equality
`standardLevi i ν J' = (standardLevi i ν J).comap (G.innerIso n).hom`
means equality of the original Levi with the preimage of the target Levi under
conjugation. It is equivalent to the claimed image equality because `innerIso`
is an isomorphism. The second clause applies to any two normalizing points with
the same Weyl class and any `J ⊆ Δ`. It equates the `comap`s along their inverse
inner automorphisms, which are the two conjugate images of `L_J`. This states
independence of the lift on all test schemes, even when that image has not been
identified with another standard Levi.

Every field `k : Type u` is quantified over. The group scheme `G` is assumed
`IsConnectedReductive`, the homomorphism `i : T.toGrp ⟶ G` is assumed
`IsMaximalSplitTorus`, and `ν : cocharacterLattice T` is assumed
`IsGenericCocharacter i ν`. Affineness and the monomorphism of `i` are obtained
from those assumptions. Write `Δ = simpleRelativeRoots i ν`. Subsets are actual
sets of characters, with explicit containment in `Δ`. There is no assumption of
reducedness, characteristic, perfectness, splitness or quasi-splitness; `Δ` may
be empty.

Renard V.4.3 (printed p.119), especially equation (V.4.3.1) and the paragraph
following it, defines the Weyl action on Levis by conjugation and explains
independence of the lift from containment of the minimal Levi. Its description
in terms of simple-root subsets follows from the root-subset construction in
V.4.2 (printed p.118). Renard's scope is nonarchimedean local fields;
Borel–Tits §5.12 with §4.2 (printed pp.85–86,99) provides the standard root/Levi
construction over arbitrary fields. Transport through the rational root span,
`SubgroupFunctor.comap`, and the imported cocharacter/intersection conventions
are **derived** formulations.

This file defines a proposition target. It supplies no proof or structural
axiom, and no instance asserting the proposition. The general proof remains an
obligation of the reductive-group program.

Source IDs: `borel-tits-1965-groupes-reductifs`, `renard-2026-representations-groupes-reductifs-padiques`.
