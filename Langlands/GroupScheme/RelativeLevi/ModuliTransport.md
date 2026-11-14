# Ambient transport and identity comparison of relative Levi images

Author: Worker 179.

This internal definition module proves that transport of actual relative Levi
subgroup images through ambient isomorphisms respects identities and composition.
The inverse ambient isomorphism gives the inverse transport, so `mapIsoEquiv`
is an actual equivalence of image-valued moduli points.

`baseChangeIdEquiv P` specializes this equivalence to the published group-scheme
identity pullback isomorphism `baseChangeIdIso P`. Thus its domain is the actual
pullback along `1_S`, not a definitionally replaced copy of `P`. The theorem
`exists_presentation_of_identity_point` extracts an actual inclusion `L → P`
satisfying the unchanged `IsRelativeLeviSubgroup`, directly from a moduli point
for the identity pullback. It adds no Levi-existence hypothesis.

The proofs use the established ambient-isomorphism preservation of the relative
Levi predicate and the identity/composition laws for inverse image of subgroup
functors. No arbitrary-base stability or torsor existence is claimed here.
This is internal transport infrastructure for the moduli problem in Conrad,
*Reductive group schemes* (2014), Definition 5.4.2, p.174, and the section-to-Levi
use of Corollaries 5.4.6 and 5.4.8, pp.178–179. The source is registered as
`conrad-2014-reductive-group-schemes`, SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`.
