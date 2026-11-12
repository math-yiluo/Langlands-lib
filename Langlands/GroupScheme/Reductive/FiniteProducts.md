# Trivial unipotent radicals in finite products

This is internal support for the finite separable Weil restriction argument. It
uses the published definitions of pseudo-reductivity, connected reductivity and
the categorical finite product, without changing those definitions.

`SubgroupFunctor.isNormal_range_of_section_square` descends normality through a
commuting square when the ambient map has an actual section and the subgroup
map is an fpqc quotient. An ambient point lifts through the section; a subgroup
point lifts fpqc locally through the quotient. Conjugation in the source and
the published fpqc membership criterion then give normality in the target.

`HasTrivialUnipotentRadical.pi` takes a smooth connected normal unipotent closed
subgroup of a finite product and forms its schematic image under each
projection. The published image theorem makes each image smooth and connected,
and its quotient map is faithfully flat. Unipotence descends along that map.
The section of a product projection gives normality by the preceding lemma.
Triviality of the radical of each factor therefore kills each image, and the
product point equivalence kills the original subgroup on every scheme test.

`isPseudoReductive_pi` combines this result with stability of affineness,
smoothness and geometric connectedness under finite products. Connected finite
type group schemes over fields are geometrically connected.
`isConnectedReductive_pi_of_isAlgClosed` then applies the published equivalence
of pseudo-reductivity and connected reductivity over algebraically closed
fields. The empty product is included.
