# Supplied integral models and their relative components

This interface connects the published integral-model and relative-component
definitions for the later Bruhat–Tits model axioms. Its inputs include both
models and their geometric properties. It asserts no model existence.

## Supplied data

`Langlands.BruhatTits.IntegralModels.RelativeComponentModelData R K G` has an
arbitrary universe `u`, a commutative domain `R`, a fraction field `K` with the
given `R`-algebra structure, and an actual group scheme `G` over `Spec K`.
There is no reductivity, Henselian, local-field, splitness, or characteristic
hypothesis on this data interface.

The fields `full` and `neutral` are actual `GroupScheme.IntegralModel R K G`
objects. Each supplies an affine flat finite-type group scheme over `Spec R`
and a generic-fibre isomorphism to the same `G`. The fields `full_smooth` and
`neutral_smooth` require smooth structural morphisms. The separate field
`neutral_connectedFibres` requires connectedness of every scheme-theoretic
fibre of the neutral model. Connectedness of the total scheme is not used as
a replacement for connectedness of fibres.

`inclusion` is the existing `IntegralModel.Hom` from the neutral model to the
full model over the identity of `G`. Its generic compatibility square therefore
requires the two specified generic-fibre identifications to agree along this
map. It is not an arbitrary map between two unrelated models.

`isRelativeComponent` is the published
`GroupScheme.IsRelativeIdentityComponent full.group inclusion.hom`.
It says that the actual scheme map is an open immersion and that, on every
test scheme over `Spec R`, factorization through it is equivalent to the
whole-image criterion in every residue fibre. This imports the actual relative
predicate; it is not a field identity component or a predicate on rational
points alone.

## Constructed section and point subgroups

For supplied data `D`, `D.neutralSections` is the range of the homomorphism
from neutral integral sections to full integral sections. Thus it is a subgroup
with the inherited integral-section group law.
`mem_neutralSections_iff` specializes the supplied all-test factorization
criterion to the test scheme `Spec R`. It identifies this range with
`InRelativeIdentityComponent D.full.group x` for an actual integral section `x`.

`D.neutralPoints` is the image of this subgroup under
`D.full.integralPointMap`, in the existing group `rationalPoints G`.
`neutralPoints_eq` proves that it equals `D.neutral.integralPoints`.
For both inclusions the proof uses the published naturality of integral-point
maps and the identity generic map. `mem_neutralPoints_iff` expresses membership
as the existence of a full-model integral section satisfying the relative
criterion and mapping to the given generic point. `neutralPoints_le_full`
follows from containment of an image of a subgroup in the full map's range.
No injectivity of integral-point evaluation is needed for these image claims.

When `R` is local, `D.specialFibreMap` is the actual base change of the inclusion
along the residue quotient. `reduction_naturality` and
`map_mem_congruenceKernel` reuse the corresponding integral-model laws.
The two special fibres here are the full residue fibres of the two supplied
models. Neither is replaced by a maximal reductive quotient.

## Source correspondence and internal provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Definition 4.1.18, Remark 4.1.19, Axiom 4.1.20 and Definition 4.1.21,
printed pp. 162–163 / PDF pp. 193–194, motivate this supplied-data interface.
Definition 4.1.18 names the relative identity component of a smooth integral
group scheme. Remark 4.1.19 distinguishes connected total space from connected
fibres. The opening of Axiom 4.1.20 supplies a smooth affine model with generic
fibre `G` and its relative component. The structure records those two proposed
models and their actual compatibility; it does not assert that the axiom holds.
The name “parahoric” in Definition 4.1.21 applies to the relative model attached
to a facet after the building/model comparison, which is not supplied here.

The first paragraph of Axiom 4.1.22, printed p. 163 / PDF p. 194, uses model
maps with the identity generic fibre and their induced residue maps. The
published generic model-map and reduction APIs are reused here for the
component inclusion. This unit does not define or assert the ordered-subset
maps or any of the seven special-fibre clauses of that axiom.

Registered source `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The authors' corrections of 1 November 2024, Chapter 4, PDF p. 27, were
checked; they do not change these passages. Registered corrections
`kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`.

The data packaging, range subgroups, image identification and inherited
naturality laws are internal constructions from the two published interfaces.
They are not presented as a literal theorem or proof from KP. The membership
criterion itself is imported from `Langlands.GroupScheme.RelativeIdentityComponent`,
whose paired explanation gives its SGA 3 provenance.

## Scope

One may specialize `R` to the actual valuation integers of a nonarchimedean
local field, or use the general interface over the integers of Chapter 8's
maximal unramified extension. That extension need not be a local field.
No compactness or openness in a rational-point topology is asserted.

The interface constructs neither model nor the relative component. It supplies
no general normality, base-change, affineness, smoothening, gluing, reductive
quotient, or descent theorem. It has no building, apartment, facet, fixer,
zero subgroup, or one subgroup parameter, and proves no equality with such a
subgroup. The full corrected ten-axiom predicate and its existence, as well as
the Chapter 9 descended construction, remain separate obligations.
