# Actual facet models for downstairs residue cocharacter parabolics

This internal supporting result combines actual descended cocharacter-ray
attainment, canonical coefficient specialization compatibility, and fpqc
reflection of equality of representable subgroup functors.

At arbitrary universe `u`, let `F` be a nonarchimedean local field, `B` its
supplied building data, and `C` maximal-unramified building data. The theorem
`exists_incidentFacet_quotientImage_eq_residueCocharacter` assumes apartment
axioms, common apartments, a compatible equivariant building map `e`, an
affine apartment map `a` with exact facet restriction, and a supplied
`FacetModelData` family `M` whose unramified neutral integral points are the
specified zero fixers of image facets. It also retains the generic
factorization `f` of the base-changed downstairs apartment torus inclusion
through the upstairs apartment torus.

For an apartment point `x`, a supplied reductive special-fibre quotient `Q`
of its actual family model, and supplied integral torus data `T` with split
integral torus and generic torus `B.S`, every cocharacter `c` of `B.S` selects
some positive short ray parameter `ε` and an actual incident downstairs
facet at the corresponding translated point. The schematic quotient image
of the actual family morphism to the model at `x` equals the dynamic
parabolic of the canonical specialization of `c` through `T` and `Q`.
The equality is over the original residue field of `𝒪[F]`, as subgroup
functors on every scheme test.

The proof first applies
`exists_incidentFacet_quotientImage_eq_descendedCocharacter` to obtain the
actual incident facet and its image equality over the maximal-unramified
residue field. The upstairs torus is the published integral split torus
attached to the singleton zero fixer. The canonical coefficient comparison
`IntegralTorusData.baseChange_quotientParabolic` identifies its dynamic
parabolic with the residue-field base change of the downstairs one.
`RelativeComponentModelHom.reductiveImage_range_baseChange` identifies
the other side with the base change of the actual downstairs image.
Finally, the residue-field extension is fpqc; both the schematic image
inclusion and the affine dynamic parabolic have actual representatives.
`SubgroupFunctor.eq_of_isRepresentedBy_baseChange_eq` therefore reflects
the equality.

`HasResidueCocharacterQuotientAttainment` is the Prop-valued statement
quantifying over these generic factorizations, apartment points, quotients,
split integral torus data and generic cocharacters. The theorem
`hasResidueCocharacterQuotientAttainment` proves it with the explicit
building, map and model-characterization hypotheses above.

The provenance is internal: the proof composes the imported ray-attainment,
coefficient-comparison and fpqc-reflection results. It makes no new
translation claim about the original literature. Existence of the supplied
torus data, attainment of arbitrary parabolics and the full facet order
bijection remain separate obligations.
