# Haar normalization on the largest compact subgroup

`HasLargestCompactOpenSubgroup G` says that `G` has a compact open subgroup containing every compact subgroup. A closed embedding of groups pulls this subgroup back to a compact open subgroup. It contains every compact subgroup of the source because the image of such a subgroup is compact.

The property is preserved under finite products by projecting any compact subgroup to each factor. In a nonarchimedean local field, the integral units form a compact open subgroup. On any compact subgroup of the field's multiplicative group, the field norm of a unit attains a positive maximum. Multiplicativity applied to an element of maximal norm shows that every element and its inverse have norm at most one, so all elements are integral units.

`HasLargestCompactOpenSubgroup.haar` uses the Library's Haar measure of mass one on a compact open subgroup. Topological group equivalences carry the largest compact subgroup to the largest compact subgroup. The proof `map_haar` uses this identification and uniqueness of Haar measure with the assigned mass on the target subgroup. Both groups carry Borel measurable structures, and the target is locally compact and second countable.

This is an internal formulation of the normalization used for regular centralizers in Henniart–Lemaire (2011), I.2.7, printed p. 20. It applies to groups admitting the indicated largest subgroup.
