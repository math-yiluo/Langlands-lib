# Zariski descent for actual centralizer families

`TorusCentralizerZariskiSheafStatement` asserts that the presheaf of actual centralizer families, with their structural maps, is a sheaf for the big Zariski topology. The base group has affine residue fibres. The parameters can be arbitrary schemes over the base.

Compatible families give matching subgroup conditions on every relative test scheme. Closed subgroup descent represents the glued condition by a closed subgroup. Its restrictions are isomorphic to the given local representatives. Smoothness and geometric connectedness are local on the target. For a residue point, choose a lift to a member of the cover and apply the residue-field comparison to the local representative there. Uniqueness is equality of the subgroup functors on every test, which is detected by their base changes along the cover. Gluing the structural maps then gives absolute Zariski descent, by the same general argument used in `AdmissibleSheaf`.

This is the sheaf step for gluing centralizer charts in SGA 3, Exposé XV, §5.2. The proof uses the project’s closed subgroup descent and field reflection results for the actual subgroup functors.
