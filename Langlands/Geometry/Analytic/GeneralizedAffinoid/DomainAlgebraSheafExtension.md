# Finite rational descent of the actual algebra sheaf to all domains

Author: Worker 36.

Work over one actual presented positive-polyradius affinoid algebra `A` over
a complete ultrametric normed field `K`. The construction uses the independently
constructed finite covering topologies and the actual fully faithful rational
inclusion.

`algebraSheafExtension K A` is an actual `CommAlgCat K`-valued sheaf on
all full represented domains. The input is the published actual rational
quotient-algebra sheaf, with its unconditional sheaf proof. The construction
uses the chosen finite ambient rational cover of each domain and its actual
product-radius pairwise intersections as small 1-hypercover data.
Mathlib's constructive dense-subsite comparison defines the value at a domain
as the multiequalizer of these rational algebras and their restriction maps.
The usual small limits in `CommAlgCat K` suffice.

`algebraSheafExtension_obj` states that value formula literally.
`sectionProjection` gives each rational-cover projection.
`section_hom_ext` is their joint uniqueness property for algebra maps.
`sectionProjection_condition` gives the equality after the two actual
bounded restrictions to each pairwise rational intersection.

`rationalAlgebraSheafIso` is an isomorphism of the restricted extended sheaf
with the original rational algebra sheaf.
`rationalSectionIso` supplies the corresponding algebra isomorphism on every
actual rational image object. The equation `restrict_rationalSectionIso`
identifies each multiequalizer projection with full-domain restriction to
the chosen chart followed by this rational algebra identification.

The construction is an internal derivation from finite rational descent and
Mathlib's explicit 1-hypercover extension. It adds no original-literature
assertion. No private peer draft is reused.
No identification of the extension at a general full domain `U` with the
stored presented algebra `U.algebra` is asserted. That remains a separate
mathematical obligation. This finite site over one affinoid does not yet
construct analytic atlases, etale sites or equivariant sites.
