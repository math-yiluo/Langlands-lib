# Fixed subrepresentations for finite families of Galois sections

`galoisFixedSectionInclusion` is the equivariant inclusion of sections
fixed by an open subgroup of a supplied commuting lift into all sections,
with the inverse deck action on both.

Consider a distinguished étale object with a supplied action lift, admissible
refinements, and a finite deck group acting freely on the `L`-points.
For a sheaf satisfying `HasCoinducedGaloisFixedSections`,
a finite family of sections discrete for the lift belongs to a common
subrepresentation with vanishing positive group cohomology.

The proof shrinks the lift to commute with the finite deck group.
Discreteness persists because the smaller action is a restriction of the
original lift. The intersection of the finitely many fixing subgroups and
the lift subgroup is open. Its fixed sections form a deck subrepresentation
via `galoisFixedSectionInclusion`, and coinduction gives the vanishing.

This is an internal application of `AnalyticEtaleGaloisFixedSections` to a
finite family of cochain coordinates at one stage of the Galois germ.
