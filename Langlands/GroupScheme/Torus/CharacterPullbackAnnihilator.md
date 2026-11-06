# Actual character pullback and cocharacter annihilators

Authors: Worker 1293; Worker 1435 contributed the need for the saturated-span formulation.

This is an internal derived construction for the actual character-image step
of the Levi cocenter root model. It uses actual homomorphisms of commutative
group schemes and their integral character and cocharacter lattices. It does
not assert any existence or structural theorem about Levi subgroups.

For `f : T → Q` over a field, `cocharacterKernelAnnihilator f` is the submodule
of actual characters of `T` whose lattice pairing vanishes on every actual
cocharacter `ν` with `ν ≫ f = 0`.

Under perfectness of both actual lattice pairings and surjectivity of the
actual cocharacter map, `cocharacterKernelAnnihilatorEquiv f` identifies the
actual character lattice of `Q` with this annihilator. Its underlying map is
exactly precomposition by `f`. The construction first proves adjointness of
character pullback and cocharacter postcomposition. Injectivity follows from
surjectivity of the latter map and separation by the target pairing. For the
image assertion, Mathlib's
`LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective` produces a
functional on the quotient cocharacter lattice. Perfectness of the target
pairing represents that functional by an actual character.

`mem_range_precompose_iff_of_saturated_span` replaces the full kernel by a
specified family `c` in it, assuming that every kernel element has some
nonzero integral multiple in the integral span of `c`. A character vanishing
on `c` vanishes on its span, and torsion freeness of the integer-valued pairing
then removes the nonzero multiple. This allows use with coroots in general
reductive groups, where integral coroot generation is unavailable. The lemma
retains the saturation and surjectivity premises explicitly; it does not
establish them for a cocenter.

The provenance is elementary duality applied to the published actual lattice
and Hom constructions in `Torus.Lattice`, `Torus.KernelCocharacters`, and
`Torus.WeilRestrictionNormOneCharacters`, together with the cited Mathlib
duality theorem. No external source assertion is imported.
