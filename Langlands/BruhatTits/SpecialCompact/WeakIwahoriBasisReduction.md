# The remaining common normal weak-Iwahori basis construction

This internal derived reduction is at arbitrary universe `u`. The algebraic `StandardSplitComponentFamily` is defined over any field `F`, for an affine ambient group scheme `G` over `Spec F`, a torus map `i : S → G` and cocharacter `ν`. It fixes actual compatible split components for all subsets of the simple relative roots before any basis member is chosen. `StandardSplitComponentFamily` records those component tori, maps and compatibility proofs. For connected reductive `G`, maximal split `i` and generic `ν`, `standardSplitComponentFamily` obtains them from the published compatible-component existence theorem.

The normalization, contraction, subgroup-family and basis results are over a nonarchimedean local field `F`. Their ambient topology is exactly the canonical `rationalPointTopology F G.X`, and all subgroup topologies are inherited from it. The contraction and final basis reductions assume connected reductive `G`, maximal split `i` and generic `ν`; a single-face contraction additionally assumes that `J` is contained in the simple relative roots and that its actual component is compatible. Its subgroup `K` is compact and open.

Every actual component point commutes with every point of the corresponding standard Levi. Therefore its conjugation fixes the literal Levi intersection with any subgroup, proving `LeviIntersectionNormalization` without a further hypothesis on that subgroup.

For a compact open subgroup, `contractionAndCofinality_of_weak` combines this normalization with the strict-point power-basis theorem and both uniform-chamber consequences. Hence weak-chamber preservation suffices for the full published `ContractionAndCofinality` predicate at that subgroup.

`weakIwahoriNormalFamily` is the actual set of compact open subgroups contained and normal in a supplied subgroup `K0` which have the ordered Iwahori intersection decomposition and weak-chamber preservation for every standard face, with the already fixed compatible components. It does not assert that this set is cofinal.

`simultaneousStandardBasisAt_of_cofinal_weakIwahoriNormalFamily` takes the supplied subgroup `K0` and the fixed component family, and assumes the concrete local construction of a member of this family in every ambient identity neighborhood. It then proves the entire `SimultaneousStandardBasisAt` property for that same `K0` and the original standard groups. The neighborhood assumption gives the compact-open normal basis directly; closedness of the represented standard Levis gives its literal inherited bases; the preceding contraction theorem gives every remaining member condition.

The cofinality construction remains a hypothesis of this reduction. No valid KP datum is claimed to provide it here. This unit is not the exact available-data proof, and supplies no completion evidence for that target.
