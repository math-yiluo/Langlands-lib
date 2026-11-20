# Compact product levels at the finite places

`productLevel` assembles a family of open subgroups of the local integral matrix groups into a subgroup of the finite adelic matrix group. The local subgroups are full outside a specified finite set. `mem_productLevel_iff` describes membership through the standard integral product equivalence. The product of the local subgroups is open by the product topology, and the standard integral group is open in the finite adelic group. The assembled subgroup is closed in the standard integral group, so it is compact.

`exists_productLevelSubgroup_le` shows that every open subgroup of the finite adelic matrix group contains an assembled product level. Pulling the subgroup back along the assembly map gives a neighborhood of the identity in the product. A basic product neighborhood inside it imposes conditions at finitely many places. At each of those places, the nonarchimedean open-subgroup basis of the local matrix group provides an open subgroup inside the prescribed neighborhood of the local integral group. Taking the full integral groups at the other places gives the desired level.

This construction uses the published local matrix topologies and the actual standard integral product equivalence. Getz and Hahn (2024), §10.1, p. 270 (PDF 282), describe the standard compact subgroup used in the surrounding adelic induction.
