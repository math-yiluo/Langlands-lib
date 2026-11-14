# Parabolicity of descended facet images from upstairs radical generation

This is a derived supporting construction for the parabolic-image part of
`UnramifiedFacetParabolicImageStatement`. All fields, residue fields, schemes,
and buildings lie in an arbitrary universe `u`. The full upstairs
radical-generation statement remains an explicit hypothesis.

For an integral model `M` over a local domain `R`, with fraction field `K`,
`IntegralModel.hasConnectedSpecialFibre_baseChange` proves that connectedness
of the full special fibre persists after a local coefficient extension to a
local domain `A` with fraction field `L`. The coefficient algebras, the two
scalar towers, and locality of the map `R → A` are retained in the Lean
context. The proof uses the affine finite-type group structure of the original
special fibre and the published theorem that a connected finite-type group
scheme over a field remains connected after field extension. The actual
isomorphism `specialFibreBaseChangeIso` then transports connectedness from the
residue-field base change to the special fibre of `M.baseChange A L`.

Let `F` be a nonarchimedean local field, `K = inertiaFixedField F`, and
`O = fixedFieldIntegers F`. For a supplied
`D : RelativeComponentModelData ↥𝒪[F] F G`,
`D.unramifiedNeutral_hasConnectedSpecialFibre` applies this deduction to the
actual neutral model. Its original special fibre is connected because the
component-model data already include connectedness of every neutral-model
fibre. This argument requires no new geometric-connectedness premise.

`D.unramifiedNeutralRadicalData` chooses a group scheme `U` over the actual
residue field of `O`, a morphism
`i : U ⟶ D.neutral.baseChangeUnramified.specialFibre`, and a proof of
`IsUnipotentRadical i`. This is a sigma type containing the group scheme and a
subtype containing its actual inclusion and radical proof. Smoothness follows
from `D.neutral_smooth` by coefficient and residue base change; affineness
comes from the integral model. Together with the preceding connectedness
result, these facts supply the hypotheses of the published
`unipotentRadicalExistence`. The definition makes a noncomputable choice from
that existence theorem and asserts no canonical choice.

The generic upstairs-model deduction is
`unramifiedModelsImage_isParabolic_of_upstairs_rootGeneration`. It takes:

- a downstairs valuation building `B`, an upstairs building `C` for the actual
  base change of `G`, a building map `e`, and an affine apartment map `a`;
- rational-extension equivariance, apartment compatibility, and the exact
  restricted-facet preimage identity for those maps;
- a zero datum `E`, incident downstairs facets `Fc ≺ Fc'`, and two actual
  upstairs models `N`, `N'` whose integral-point images are precisely the
  zero-point subgroups intersected with the fixers of `e '' Fc.val` and
  `e '' Fc'.val`;
- smoothness of both models, connectedness of the full target special fibre,
  and a supplied identity-generic morphism `ψ : N'.Hom N (𝟙 _)`.

Its conclusion is geometric parabolicity of the actual schematic-image
inclusion of `ψ.specialFibreMap`. The proof first invokes
`exists_incident_apartment_models` to translate both facet images into one
upstairs apartment. This gives two nonempty subsets contained in incident
upstairs facets and the exact zero-fixer characterizations for the models
transported by the inverse inner automorphism. Transport changes their
generic identifications and leaves their integral group schemes, special
fibres, and special-fibre morphism unchanged.

The proof chooses a represented unipotent radical of the transported target
special fibre using `unipotentRadicalExistence`. Applying the supplied
`UnramifiedUpstairsRadicalRootGenerationStatement` to `C` and `E` gives one
subgroup `H` with its whole-apartment fixer bound. Its generation equality is
then applied to the transported target model and the nonempty subset of its
containing facet. The equality implies the generation bound required by
`unramifiedIncidentImage_isParabolic_of_rootGeneration`. That published
conditional theorem gives parabolicity of the transported comparison image,
which is the same special-fibre comparison image as the original one.

Finally,
`unramifiedFacetImage_isParabolic_of_upstairs_rootGeneration` specializes to
the actual neutral base changes of two supplied component models `D`, `D'`.
The component-model data supply their smoothness, and the connectedness
deduction above supplies the target-fibre hypothesis. The given morphism
`φ : RelativeComponentModelHom D' D` is extended by `Hom.baseChangeIdentity`.
The generic upstairs deduction proves parabolicity of its actual upstairs
special-fibre image. The published
`Hom.isParabolic_specialFibreImage_of_unramified` reflects this property
through the actual algebraic residue-field extension, giving exactly
`φ.HasParabolicSpecialFibreImage`.

The provenance is the composition of these named Library constructions and
theorems, rather than a new translation of an external source. This unit
proves neither `UnramifiedUpstairsRadicalRootGenerationStatement` nor a
reduction-preimage equality. Those remaining inputs are required before the
exact host theorem can be concluded.
