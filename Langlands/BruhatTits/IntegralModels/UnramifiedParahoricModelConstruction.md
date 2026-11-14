# Unramified parahoric models from two torus inputs

This internal construction transports the published full and relative neutral
models from the supplied apartment to every translate by a rational point.

`map_normal_inf_apartmentFixer_innerIso` computes the image of the intersection
of any normal subgroup with the pointwise fixer of an apartment subset under the
inner group scheme isomorphism defined by `g`. The rational point map is literal
conjugation by `g`. Normality preserves the first subgroup; the group action
conjugates the fixer to the fixer of the translated subset. Injectivity of the
point map makes it commute with the intersection.

`transport_relativeComponentModelData_apartmentFixers` applies this calculation
to both the character valuation kernel and the original datum's zero subgroup.
The existing `RelativeComponentModelData.transport` preserves the actual
integral group schemes and their relative component inclusion. The resulting
full and neutral integral point images are exactly their respective intersections
with the translated fixer, as subgroups of the original rational point group.

`exists_unramifiedParahoricModel_of_torusInputs` constructs these data for every
nonempty bounded subset of a translated apartment. All types are in the
arbitrary universe `u`. The group is any affine group scheme over the actual
inertia fixed field of a nonarchimedean local field `F`, with supplied building
data `C` and any original unramified zero datum `E`. Boundedness means that each
real affine function is bounded above on the apartment subset.

The proof first constructs a full model on the original apartment, using the
published proofs of vertex maximal boundedness, finite vertex approximation,
maximal bounded model existence, smooth intersection and finite index
enlargement. The published relative component constructor gives its smooth
affine neutral model and the actual relative identity component inclusion.
The exact simply connected normalizer theorem supplies the bounded
whole-apartment zero-fixer and sharp-fixer decomposition for the original `E`.
The existing neutral-point assembly then identifies the neutral integral
points. Finally inner transport moves both models and both point identities to
the translated apartment.

Exactly two proposition inputs remain:

- `UnramifiedTorusIwahoriModelStatement.{u}`, which supplies smooth torus
  models with geometrically connected fibres and Iwahori integral
  points;
- `UnramifiedTorusConnectedBoundStatement.{u}`, which bounds integral points
  of a smooth torus model with geometrically connected fibres by the
  torus Iwahori subgroup.

`unramifiedParahoricModelOfTorusInputs` chooses the resulting compatible pair.
Its `integralPoints` theorem gives both literal subgroup equalities in the
original `rationalPoints G`: the full image is the character valuation kernel
intersected with the translated fixer, and the neutral image is `E.zeroPoints`
intersected with that same fixer.

`unramifiedParahoricModel_of_torusInputs` specializes the construction to the
base change of a group over `F` and proves the exact published
`UnramifiedParahoricModelStatement.{u}` from these two torus inputs. It does not
prove either input. Thus this internal contribution completes the assembly and
translation steps while retaining the two mathematical torus obligations.
The published target pair and its imports are unchanged.

The provenance is the composition of the named published constructions and
group action lemmas. No new claim is attributed directly to the literature.
