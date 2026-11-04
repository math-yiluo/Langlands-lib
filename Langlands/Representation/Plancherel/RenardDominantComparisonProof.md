# Actual dominant centralizer sections and finite positive covers

Author: Worker 1292. The imported `SplitComponentLatticeBridge` is by
Worker 1503.

`renardDominantComparison` proves the exact published
`RenardDominantComparisonStatement.{u}`. It retains every quantified datum
and hypothesis, including arbitrary nonarchimedean local fields of either
characteristic, arbitrary connected reductive groups, maximal split tori,
generic cocharacters, closed representatives of the actual centralizer,
the factorization through that centralizer, and every bijectivity argument
`h` for `restrictionEvaluation s`. It adds no premise or rank restriction.

## Structural inputs and the integral comparison

Maximal splitness gives `IsSplitTorus S.toGrp` by
`hi.isSplitSubtorus.1`. Connected reductivity of `G` gives smoothness of its
structure morphism; smoothness supplies the locally finite type instance.
Together with the target's affine instance and splitness, the published
`IsSplitTorus.finite_positiveRelativeRoots` proves finite support of the
actual positive relative roots. This theorem uses finite dimensionality
of the actual Lie kernel and its split-torus weight decomposition. No
abstract root-system finiteness hypothesis is added.

The other two inputs come from `RenardActualLattice`:
`finiteIndex_splitValuationImage_of_comparison s h hS` and
`bijOn_C0_splitValuationImage_of_comparison s h hS`. They require only
splitness of `S` and the already quantified comparison argument `h`.
Their proof uses the actual integral restriction image `A` inside the
character lattice of `S`. Pairing cocharacters with `A` is injective by
injectivity of `h` and the integral perfect pairing of a split torus.
The character and cocharacter lattices have the same finite rank, so
this restricted pairing has finite-index image in the integral dual of
`A`, by `IntegralRestriction.finiteIndex_range_of_injective`.

Every actual integer character valuation vanishes on the restriction
kernel, by `centralizerValuation_spec` and injectivity of the integer cast
into the reals. It therefore descends to an integral functional on `A`.
The descended valuation map is injective because its values on restricted
characters recover the original valuation. Uniformizer evaluation
identifies its value on a uniformizer point with the restricted integral
pairing. Worker 1503's
`exists_rationalCharacterValuation_map_eq` realizes the valuation of every
split-torus point by such a uniformizer point. Thus the actual split
valuation image is the inverse image of the finite-index pairing image.
Pullback gives finite index. The same realization proves surjectivity of
the valuation from `C0` onto the split image; injectivity follows from
uniformizer normalization and the embedding of the cocharacter lattice
into its real scalar extension. The imported
`CocharacterUniformizer.latticePairing_isPerfPair` supplies the split
integral perfect pairing.

This route proves the needed lattice facts directly from `h`; it does
not use connected reductivity of `Z`, the split-component property of
`s`, or injectivity of character restriction. The centralizer and
factorization hypotheses remain quantified in the exact target, even
though this proof establishes the conclusions under fewer hypotheses.
It does not prove the separate existence of `h` or the separate actual
centralizer structural statements.

## Assembly of the seven conclusions

The proof supplies these three established inputs to
`dominantCentralizerLatticeConclusions_of_latticeComparison` in
`RenardDominantSections`. Its implemented argument is as follows.

1. `RenardDominantValuation` evaluates actual restricted characters on
   uniformizer points to prove the positive normalization `1 ⊗ c`.
2. The same formula turns nonnegative integral positive-root pairings
   into the actual real chamber inequalities, giving `C0Plus = C0 ∩ D`.
3. The published intrinsic valuation-image equivalence sends each actual
   point's real valuation to its integer character valuation. It
   therefore identifies the two dominant valuation images.
4. `RenardDominantTransversal` represents each of the finitely many
   lattice residues by an actual point and translates it by a sufficiently
   large nonnegative multiple of `ν` at the uniformizer. Finitely many
   positive roots have a common bound, and each pairs with `ν` by an
   integer at least one. Translation puts the point in `D` and preserves
   its lattice residue. Choosing one translated point per residue gives
   a finite dominant full-lattice transversal. This also covers empty
   root support.
5. Full transversality and the `C0` valuation bijection give a bijection
   on product pairs. Equality of residues identifies the transversal
   factors, and injectivity on `C0` identifies the remaining factors.
   Surjectivity first chooses the residue representative and then the
   split-image factor. Cutting this full section by `D` retains exactly
   the dominant valuations because dominance is constant on valuation
   fibers. The intrinsic image equivalence also gives the required
   bijection under the real centralizer valuation.
6. `RenardDominantFiniteCover` applies Dickson's lemma to natural floors
   of the finitely many positive-root orders, separately in each finite
   lattice residue. There are finitely many minimal floor vectors, and
   every dominant point has a selected point with no larger floors in
   its residue. Their valuation difference comes from `C0`, so all root
   differences are integers. Ordering the floors of nonnegative reals
   whose difference is integral makes these differences nonnegative.
   The difference is therefore represented by `C0Plus`. The selected
   actual dominant points give the finite positive product cover.
7. For a chamber-compatible transversal, its stipulated equality
   identifies the dominant intersection with the positive product.
   Restricting the full product-pair bijection proves nonrepetition.
   Existence of a chamber-compatible transversal is not asserted.

All sets, subgroups and images are the actual published constructions.
The finite-cover proof uses Dickson's lemma rather than a separate
polyhedral finite-generation theorem. The helper Markdown files describe
the corresponding Lean proofs in detail. This is a derived proof of the
published proposition and uses its positive-order normalization; it
introduces no additional source assertion or structural axiom. The target
and all its imported Lean/Markdown pairs are unchanged.
