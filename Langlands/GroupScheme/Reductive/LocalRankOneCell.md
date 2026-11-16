# Open cells from fieldwise rank-one root support

This internally derived construction proves openness of the actual multiplication
map from an opposite root group, a split torus, and a positive root group.
The ring-level result works over every commutative ring. It assumes supplied
root parametrizations and a two-root condition on every field-valued fibre; it
does not construct those inputs or a Weyl representative.

## Field argument

`LocalRankOneCell.unipotent_eq_root_of_root_support` concerns a connected
reductive group over a field, with affine smooth structure map and a split
torus map. If every root is either `α` or `-α`, and a cocharacter `ν` pairs
positively with `α`, its dynamic positive unipotent subgroup is the intrinsic
root subgroup for `α`. The proof applies
`LeviGluing.unipotent_eq_root_of_positiveRoots_on_ray`: a root with positive
pairing must be `α`, which lies on its own positive integral ray.

`isOpenImmersion_tripleCell_of_root_support` additionally assumes the torus
is maximal, `α` is a root, and supplied maps represent the intrinsic root
subgroups for `-α` and `α`. Every pair of roots is linearly dependent,
because each is a signed copy of `α`. The published rank-one centralizer
theorem, applied with `dynamicCentralizerReductive`, therefore identifies
the dynamic centralizer of `ν` with the supplied torus. The preceding
unipotent comparison for `ν` and `-ν` identifies the other two factors.
The actual dynamic triple-cell theorem then proves that their ordered
multiplication is an open immersion.

## Product and base-change comparisons

`Dynamic.tripleCellMultiplication_precomp` proves that precomposing the
three subgroup maps is equivalent to precomposing their triple multiplication
with the corresponding product map.

`Dynamic.tripleBaseChangeIso` identifies the product of three actual
base-changed group schemes with the pullback of their product over the
base. It uses the monoidal product comparisons for `Over.pullback`.
`tripleBaseChangeIso_hom_comp` proves compatibility with the triple
multiplication, using preservation of multiplication and the equations
for the product projections.

`LocalRankOneCell.standardTripleBaseChangeIso` specializes this comparison
to the standard source `Ga × (T × Ga)` for a coordinate split torus.
It composes the additive-group and split-torus base-change isomorphisms
with the preceding product comparison.
`standardTripleBaseChangeIso_hom_comp` identifies the pulled-back cell
map with the cell of the standard base-changed root maps and torus map.
All these comparisons allow arbitrary commutative coefficient algebras.

## Arbitrary commutative base ring

`LocalRankOneCell.isOpenImmersion_fibre` assumes:

- A reductive group scheme `G` over `Spec R` with affine structure map.
- A coordinate split torus map `i`, maximal on every residue-field fibre.
- Exponents `a`, `nu` with strictly positive integral pairing.
- Actual root parametrizations `xm` and `xp` of weights `-a` and `a`.
- For the specified field algebra `k`, the roots of the base-changed
  torus map are exactly the exponent characters for `a` and `-a`.

Every character of the standard field split torus comes from an exponent.
Thus the two-root condition supplies the hypotheses of the field theorem.
Base change preserves the supplied parametrizations. The product
comparison above transports the resulting open immersion to the actual
pullback of the original cell map.

`LocalRankOneCell.isOpenImmersion` assumes that same two-root condition
for every field algebra of `R`, and proves
`IsOpenImmersion (Dynamic.tripleCellMultiplication xm i xp).left`.
The source is smooth over `R`, as a product of two additive groups and
a split torus; in particular it is flat and locally of finite
presentation. The reductive target is locally of finite type.
Applying `isOpenImmersion_fibre` to each residue-field algebra therefore
supplies the hypotheses of
`Langlands.AlgebraicGeometry.isOpenImmersion_of_fiberwise`.
The conclusion concerns the actual scheme morphism and retains nilpotent
structure. There is no locality, reducedness, noetherian, Henselian, or
characteristic restriction on `R`.

## Provenance and scope

The results are internal consequences of the published intrinsic
root-subgroup and dynamic-cell theorems, the rank-one dynamic-centralizer
theorem, actual group and torus base change, the standard character lattice
of a split torus over a field, and the fibrewise open-immersion criterion.
No new identification with an external source is asserted.

This module supplies the openness step once an actual rank-one
centralizer and its root parametrizations and field support are available.
It does not assert that a higher-rank group has such a three-factor open
cell. It does not construct normalized Weyl data or prove the unchanged
local Isomorphism Theorem.
