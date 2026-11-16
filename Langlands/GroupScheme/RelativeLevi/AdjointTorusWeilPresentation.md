# The Weil-presentation statement applied to the actual adjoint torus

This module connects the existing actual adjoint Borel extension to
`RelativeBorelAdjointTorusWeilPresentationStatement`. Its presentation result
is conditional on a proof of that proposition.

Let `d : RelativeLevi.AdjointBorelExtensionData i q a T t`. Thus `i : B ⟶ G`,
`q : G ⟶ A`, and `t : T.toGrp ⟶ B` are the original maps, while
`d.borel.projection` and `d.torus.projection` are the constructed actual
quotient maps. All the groups have the same base scheme.

`torus_center_isFppfQuotient` works over an arbitrary base scheme. If `q`
is a full fppf quotient by the whole `center G`, then the actual map
`d.torus.projection` is a full fppf quotient by

`(center G).comap (t ≫ i)`.

Its proof retains flatness, surjectivity and local finite presentation
from `d.torus`. The two quotient-subgroup kernel identities express its
full kernel as the successive inverse images, along `t` and `i`, of the
kernel of `q`. The supplied quotient identifies that last kernel with
`center G`; functoriality of inverse image combines the two maps. This
identity holds on every test scheme and includes any nonsmooth part of
the centre.

`torus_weilPresentation_of_statement` works over `Spec R` for any
commutative ring `R`. Its explicit premises are a proof of the universal
presentation statement, reductivity of `G`, the relative Borel property
of `i`, the full-center fppf quotient property of `q`, the relative-torus
property of `T`, and closedness and fibrewise maximality of `t ≫ i`.
Applying that supplied statement with the preceding kernel identity gives
a finite projective étale `R`-algebra `E` and an actual isomorphism

`d.torus.group ≅ WeilGm.groupScheme (CommRingCat.of R) E`.

`TorusWeilPresentationData d` packages such a coefficient type, its
commutative ring and `R`-algebra structures, its finiteness and
projectivity, its étaleness, and a chosen isomorphism of the actual torus
quotient. The four algebra and module structure fields are available as
instances. `torusWeilPresentation` chooses this data from the preceding
existence theorem, with exactly the same explicit premises. It uses
classical choice for the coefficient algebra and the isomorphism; it
asserts no uniqueness or canonicity of these choices.

The coefficient algebra is allowed to be the zero ring. No semi-locality,
affineness of the ambient quotient, or compatibility equation for the
action is an additional premise of these lemmas. The existing extension
data, which are supplied, already contain the needed actual quotients.

This is an internal deduction from the kernel identities of
`SubgroupFunctor.QuotientSubgroupData`, the existing adjoint extension
data and the explicitly supplied presentation statement. It proves the
kernel comparison and the conditional application and packages the latter's
witnesses as usable presentation data. It does not prove the universal
presentation statement, construct an ambient quotient, or prove the
semi-local quasi-split inner-form theorem.
