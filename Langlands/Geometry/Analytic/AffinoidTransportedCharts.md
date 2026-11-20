# Charts transported into an affinoid spectrum

`affinoidChartDomain` takes a localized isomorphism from a saturated
presentation to a small affinoid spectrum. It sends an original chart
to a domain of the specified presented affinoid algebra. The structural
bounded map corresponds to the chart inclusion followed by the
isomorphism, and its spectrum image is closed by compactness.

For the domain universal property, transport a bounded affinoid test
with image in this locus back through the isomorphism. Its image lies
in the original chart, so it factors through the chart domain
inclusion. The comparison between the chart domain and its small
spectrum gives the bounded factor, and monicity of the inclusion
gives uniqueness.

A quasinet of selected charts has a finite subfamily covering the
compact affinoid space. Transporting those charts gives an actual
finite full-domain cover with the same chart algebras. The construction
is internal to the Library and uses its localized domain lifting,
small affinoid map comparison, and compact subcover theorem.
