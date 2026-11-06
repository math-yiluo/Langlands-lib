# The actual rational graph cell is dense

This internal support unit constructs the rational-point families and three-factor cell in the actual `SimpleComparisonGraph`, constructs the generated subgroup's left action on its closure, and proves density of the cell's locations. The density and action constructions use an algebraically closed field and retain the explicit ambient chamber-centralizer identity from the preceding support units. The exact common-torus isomorphism and global Levi gluing propositions are not proved here.

## Actual rational families

Let `k` be any field, `G1` and `G2` smooth affine group schemes over it, `T` the common torus object, and `i1`, `i2` its homomorphisms. Let `D` be an actual `SimpleComparisonGraph`. It supplies splitness of `T`, a generic chamber for the actual roots of `i1`, actual simple-root directions and local comparisons, and the generated graph with its actual root maps. The preceding `SplitLeviGluingSimpleGraph` constructor supplies this record from connectedness of `G1`, splitness, and precisely the existing local Levi gluing premise. No separately chosen root group or pinning is used.

`GraphPoints` means actual morphisms `Spec k → D.envelope.group` over `Spec k`. For each intrinsic simple-root index `a`, `positiveRational a` and `negativeRational a` are the range subgroups of the corresponding actual root maps, evaluated on `Spec k`. `torusRational` is the range of the distinguished graph torus lift on that same test.

`positiveGenerated` and `negativeGenerated` are the abstract subgroup closures of the unions of the positive and negative rational ranges. Here `Subgroup.closure` is algebraic generation by multiplication and inversion, without any topology. `rationalGraphCell` is the ordered set product

`negativeGenerated * torusRational * positiveGenerated`.

The separate `rationalPointClosure` used below consists of actual rational points whose locations lie in the scheme-topological Zariski closure of the locations of a set.

## Containment, normalization, and generated subgroup

Each individual rational root subgroup lies in its respective generated subgroup. The positive generated subgroup lies in the rational points of the graph's actual positive dynamic unipotent subgroup for the chosen chamber, and the negative generated subgroup lies in its opposite. These are containments, not claimed equalities. They follow because the dynamic rational points form a subgroup containing every corresponding root range, as proved on all tests in `SplitLeviGluingSimpleGraph`.

The torus normalizes both generated rational subgroups. For a generator, this is exactly the already proved all-test torus normalization of its actual root map. The published subgroup normalizer criterion extends conjugation containment from the generators to their abstract subgroup closure. It uses no continuity of multiplication and no smoothness of a generated rational subgroup.

The preceding `rootFamilyRationalPoints` construction used an `Option (Sum SimpleIndex SimpleIndex)` family with the torus as its `none` source. `rootFamilyRationalPoints_eq_closure` identifies that actual subgroup with the algebraic subgroup closure of the union of the positive root ranges, `negativeGenerated`, and `torusRational`. The proof checks the three source-index cases, then uses the algebraic closure-of-union identities. This preserves the torus even when the simple-root family is empty and supplies exactly the group used by the published word-induction theorem.

All these family, containment, normalization and subgroup-identification results hold over every field, with no assumption of reduced roots or connectedness of the original ambient groups beyond the data already stored in `D`.

## Constructed closure action

For the remaining constructions assume that `G1` is connected and `k` is algebraically closed. Assume `i1` is closed and that the dynamic centralizer of its chosen ambient chamber cocharacter equals `range i1`. Let `P1` and `P2` be actual root data realizing the roots of `i1` and `i2`, and assume the two actual ambient root sets are equal. The root datum index universes are arbitrary and independent.

The definition `rationalGraphCellClosureAction` constructs a `MulAction` of the actual `rootFamilyRationalPoints` subgroup on the rational-point closure of `rationalGraphCell`. Its underlying action is left multiplication in the graph rational-point group. It rewrites the generated subgroup by the equality above and applies the already published `rationalTripleProductClosureAction` to the actual positive and negative rational root families, the actual generated negative and positive subgroups, and the actual torus rational subgroup.

Every input of that word induction is proved for these objects. Positive-root containment in the positive generated subgroup and negative generation hold by construction. Torus normalization is the preceding theorem. For distinct simple-root indices, graph commutation follows from the realizing root data, equality of ambient root sets, and the all-test two-projection argument in `commute_positive_negative`. For the same index, the already proved `positive_mul_negative_subset_rationalPointClosure` gives exactly containment in the closure of the negative-root, graph-torus, positive-root products. Its local-cell argument is why algebraic closedness, connectedness of `G1`, closedness of `i1`, and the chamber-centralizer identity are explicit here.

## Density of the actual graph cell

Under precisely those same hypotheses, `dense_rationalGraphCell` proves that the locations of the actual `rationalGraphCell` are dense in the graph's underlying scheme.

The theorem first uses `dense_rootFamilyRationalPoints` from `SplitLeviGluingGraphGeneration`, which proves density of this particular generated rational subgroup from actual all-test algebraic generation by these root and torus maps. The subgroup equality above changes it into the generated-location input expected by the published `dense_rationalPointImage_tripleProduct`. Applying that theorem to the same actual families, normalization, commutation and equal-index closure gives the claimed cell density. Thus no generation, density, normalization or root-commutation premise for the selected family is supplied without proof.

The imported word-induction theorem uses separate continuity of left and right multiplication in the induced rational Zariski topology. This specialization does not assert joint continuity. The dense cell is a set of actual rational products of generated subgroups; this module does not claim it is already the image of an open immersion represented by those abstract rational subgroups.

## Provenance and remaining obligations

The construction is internal: it specializes the previously proved abstract rational word-induction and density theorems to the actual graph root maps, using the preceding local-cell and graph-generation units. No new literature assertion, global isomorphism, classification theorem, or root-group parameterization is used.

The ambient chamber-centralizer identity remains a visible hypothesis of the action and density results. The preceding units can derive it from an explicitly retained `DynamicCentralizerReductiveStatement`, connected reductive `G1`, and maximality of `i1`, with all other structural inputs supplied by published unconditional theorems. No pending proof is used as an unconditional input here. Equality of the generated rational factors with the whole intrinsic graph dynamic factors, projection invertibility, exact Levi gluing, and the exact arbitrary-field main theorem remain separate obligations. The published target statements remain unchanged.
