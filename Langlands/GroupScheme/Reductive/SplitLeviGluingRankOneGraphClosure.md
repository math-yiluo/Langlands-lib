# Local root cells and equal-index rational closure in the graph

This is an internal support unit for the common-torus isomorphism argument, at arbitrary universes and over any field unless algebraic closedness is explicitly specified. It transports the actual local-cell closure into the constructed graph. Its torus-middle and equal-index conclusions retain an explicit chamber-centralizer identity, or the separately stated dynamic-centralizer reductivity proposition from which that identity follows. It does not prove the main isomorphism or the global Levi gluing proposition unconditionally.

## Transport of rational-point closure

The auxiliary `postcomp_mem_rationalPointClosure` allows different source and target group schemes `K` and `H`, with a morphism of their underlying schemes over `Spec k`. If this morphism sends every point of a set `S` into the rational-point closure of `S'`, it sends every point in the closure of `S` into the closure of `S'`. Continuity of the map on underlying topological spaces proves this: its image of the closure is contained in the closure of the image. No smoothness, affineness, finite-type, connectedness or algebraic-closedness assumption is needed for this transport lemma, and the morphism need not respect the group law.

The auxiliary `postcomp_mem_rationalTripleProduct` uses a group-scheme homomorphism. It sends the literal rational products of three factor images to the products of the three composite maps, by naturality of multiplication. There is no assertion that multiplication is jointly continuous for the induced topology on rational points.

## The actual local cell in the graph

Let `G1` and `G2` be smooth affine group schemes over `k`, with common torus object `T`, homomorphisms `i1` and `i2`, and an actual `SimpleComparisonGraph D`. This record contains splitness of `T`, a generic chamber for the actual roots of `i1`, its simple-root directions and their rank-one and annihilation properties, the actual local comparisons, and the generated graph. `SplitLeviGluingSimpleGraph` constructs such a record from connectedness of `G1`, splitness of `T`, and exactly the existing local Levi gluing premise. Here we use its actual maps and the local root cells constructed in `SplitLeviGluingRankOneFactors`.

Assume `G1` is connected, `k` is algebraically closed, `a` is an intrinsic simple root for that chamber, and `E` is an actual `RankOneRootCell` in the left local comparison for `a`. Every rational point in the image of its local Levi in the graph lies in the rational-point closure of

`negativeHom a * (E.middleHom followed by localLift a) * positiveHom a`.

This statement concerns actual rational points in the ranges of the specified maps. The proof lifts the point to the local Levi, applies the previously proved rational density of the actual local cell, and transports closure through the local lift. It requires neither a root datum on the graph nor that either graph projection be injective.

## Identifying the local middle with the common torus

The theorem `local_torus_rep` retains two explicit hypotheses: `i1` is a closed subgroup, and the dynamic centralizer of the ambient chamber cocharacter is exactly `range i1`. It proves that the local torus inclusion represents the entire local chamber centralizer on every scheme test, including nonreduced tests.

Indeed, the left local comparison inclusion is monic, so its chamber centralizer is the preimage of the ambient chamber centralizer. The ambient identity makes this the preimage of `range i1`. The equation identifying the composite local torus inclusion with `i1`, together with monic cancellation, identifies that preimage with the local torus range. Closedness of the local torus follows from closedness of `i1` and of the local Levi inclusion.

With connected `G1` and a root datum `P1` realizing the actual roots of `i1`, `torusRankOneRootCell` constructs a local root cell whose middle group is the given `T`, whose middle map is the actual local torus inclusion, and whose endpoint maps are the existing actual root representatives. It uses the preceding full local centralizer representation and the already proved endpoint dynamic representations.

Over an algebraically closed field, `positive_mul_negative_subset_rationalPointClosure` then proves the exact same-index condition in the graph: every product of a rational point in the positive simple-root range and a rational point in the corresponding negative range lies in the rational-point closure of the opposite-root, common-torus, positive-root products. Both factors lie in the image of the same local Levi, which is a subgroup on rational points. The closure transport above applies to their product. The local torus followed by the local lift is precisely the distinguished graph torus lift, so its middle factor has the required actual map.

## Explicit structural adapter

The constructor `torusRankOneRootCellOfCentralizerReductivity` retains `DynamicCentralizerReductiveStatement` as an explicit structural premise. It also assumes that `G1` is connected reductive, that `i1` is a maximal torus inclusion, that `P1` realizes its actual roots, and that the graph `D` is as above; its construction takes place with the smooth affine and connected instances used for the preceding local cell. These assumptions do not restrict the field or require reduced roots.

The theorem `chamber_centralizer_eq_range_of_reductiveCentralizers` discharges the preceding ambient chamber-centralizer identity from that structural premise. It applies the existing `maximalTorusCentralizer_of_structuralInputs` reduction to the retained centralizer-reductivity proposition and the published unconditional `noTorusUnipotent` and `solvableTorusQuotient` theorems. The published unconditional `genericCentralizer` theorem then identifies the dynamic centralizer of the chosen generic chamber with the whole-torus centralizer. Maximality of `i1` implies maximal splitness because `D` supplies splitness. Thus every structural input except dynamic-centralizer reductivity has an actual proof in this adapter.

The final same-index closure theorem `positive_mul_negative_subset_closure_of_reductiveCentralizers`, over an algebraically closed field, applies that identity to the actual graph root families. The structural proposition remains visible in its type. No assertion of that proposition, no pending candidate, and no global isomorphism or classification theorem is treated as an axiom or a published proof here.

## Remaining obligations and provenance

All constructions and arguments here are internal compositions of the named published interfaces, the actual simple-root graph maps, and the preceding rank-one factor unit. There is no new external source assertion. The global simple-root generation, graph-cell density, equality with global graph dynamic factors, projection invertibility, and exact main theorem remain separate obligations. The conditional support constructors do not add a premise to either published target statement.
