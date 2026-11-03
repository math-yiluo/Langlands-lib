# Perfect real pairings and character kernels of actual split tori

Author: Worker 1327.

This internal derivation uses the published actual character and cocharacter
lattices, their real spaces and real pairing. Over every field and in every
universe, the pairing of an actual split torus is perfect.

For a coordinate split torus, the existing real coordinate equivalences
identify the pairing with the finite dot product, which is perfect.
Transport through any split presentation proves perfectness for the supplied
actual torus. The scalar-extension transport identity follows by tensor
induction from the existing integer lattice pairing identity.
`characterDualEquiv` is the resulting equivalence from the published full
real character space to the dual of the published real cocharacter space;
its evaluation is exactly the existing `pair`.

`latticePairing_map` associates composition of actual morphisms to identify
character restriction and cocharacter postcomposition as adjoint maps.
Tensor induction proves the corresponding real identity
`pair_cocharacterMapReal`.

The two annihilator constructions use these actual pairings.
`cocharacterAnnihilator W` consists of cocharacters pairing to zero with
every character in `W`; `characterAnnihilator N` consists of characters
pairing to zero with every cocharacter in `N`. Perfectness and the algebraic
double-annihilator theorem show that applying these successively recovers
every real character subspace. The common annihilator of a set of integral
characters is the cocharacter annihilator of their real span, by the
universal property of the span.

For any morphism `f : A → T` with split source `A`, pairing naturality and
nondegeneracy identify its real character-restriction kernel with the
character annihilator of its real cocharacter image.
Consequently, if that image equals the published
`relativeCentralDirections i` and `T` is split, its restriction kernel is
exactly `relativeRootSpanReal i`. This conditional linear-algebra theorem
does not assume or prove the geometric image equality; it is an internal
step for using that separately proved equality in the full target.

The proof uses no character/root complement, root-system realization,
positive-rank, reduced-root, characteristic-zero or perfect-field premise.
The provenance is internal: the geometric lattices, coordinate pairing and
isomorphism transport are already published, and the new conclusions use
composition, tensor induction and algebraic duality.

The pairing-transport lemma `RealTorusSpace.pair_congr` is reused from
`FiniteRealTorusSpace`, whose scalar-extension maps are the same maps used here.
