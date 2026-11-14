# Actual big cells over arbitrary local rings

This is a derived prerequisite for the local Isomorphism Theorem. It combines
`LocalRootGroup.exists_rootParametrization_of_flat` with the existing fibrewise
big-cell construction in `Reductive/LocalSplitBigCellProof`. It does not change
the published reduced-base statements or their imports.

Let `R` be a commutative local ring, `G` a reductive group over `Spec R` with
affine structure morphism, and `i : G_m^I → G` a coordinate torus, maximal on
every residue-field fibre. Let `P` be a fibrewise root datum for this torus.
`LocalSplitBigCell.rootFamily` chooses, separately for each root of `P`, an
actual parametrization `G_a → G`. The theorem
`isRootParametrization_rootFamily` supplies its specification: it is a closed
immersion representing the prescribed relative root subgroup, with the
prescribed torus-equivariance identity on every scheme test. There is no
reducedness, noetherian, henselian or characteristic hypothesis.

`isOpenImmersion_cellMap` is slightly more general: over any commutative ring,
if a family of actual root parametrizations is supplied, its big-cell map is
an open immersion for every base of `P` and every enumeration of the negative
and positive roots. This theorem does not require locality, reducedness or a
separate closed-immersion hypothesis on `i`. Its proof reuses the existing
`isOpenImmersion_fibre`: after base change to any residue field, the actual
cell map is the open big-cell immersion of the field group. The source is
smooth, being the product of two vector groups and a split torus; `G` is
smooth by reductivity. The existing fibrewise open-immersion criterion
therefore applies over the original ring, including its nilpotents. Field
points are not used to detect equality of morphisms.

Finally, `isOpenImmersion_rootFamily` applies that criterion to the chosen
family. Thus actual big cells now exist over arbitrary commutative local
rings. The construction makes no claim that these independent choices have
Weyl normalization or provide compatibility for gluing maps between two
reductive groups. Those remain obligations of the Isomorphism Theorem.
