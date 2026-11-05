# Field extension on rational identity-component quotients

Author: Worker 1107.

Let `H` be an actual smooth affine group scheme over a field `k`, and let
`φ : k →+* L` be a homomorphism to another field in the same arbitrary universe
`u`. Write `H_L` for its actual pullback along `Spec L → Spec k`.
`IdentityComponent.rationalComponentBaseChange H φ` is the homomorphism

`H(k) / H⁰(k) → H_L(L) / (H_L)⁰(L)`

induced by the published `GroupScheme.baseChangeSectionHom`. These are the
ordinary quotient groups from `IdentityComponentRationalQuotient`, with
`H⁰(k)` interpreted as the image of the actual identity-component inclusion.
There is no characteristic, perfection, algebraicity or separability
assumption on the field homomorphism.

## Construction and implemented laws

`baseChangeSectionHom_mem_rationalIdentitySubgroup` writes an
identity-component rational section as a section of `H⁰` followed by its
inclusion. Pulling back that section and composing with the published actual
comparison `IdentityComponent.baseChangeIso H φ` gives a section of
`(H_L)⁰`. The comparison's inclusion equation and naturality of
`baseChangeSectionHom` identify its image with the pulled-back original
section. Thus the target quotient projection kills the source identity
subgroup, and `rationalComponentLift` constructs the displayed homomorphism.
`rationalComponentBaseChange_projection` gives its value on every projected
rational section.

`rationalComponentEmbedding_baseChange` compares the existing injections
of these rational quotients into the topological connected components of
their actual schemes. The continuous first projection `H_L → H` sends the
embedding of a changed rational class to the embedding of its original
class. On representatives, this is the first-projection law for
`baseChangeSectionHom`, evaluated at the unique point of `Spec L`; the base
map sends that point to the unique point of `Spec k`.

This equation proves `rationalComponentBaseChange_injective`: equality
after extension gives equality of the source component embeddings, and
the published embedding is injective. Consequently
`baseChangeSectionHom_mem_rationalIdentitySubgroup_iff` says that the
changed section belongs to the actual identity-component subgroup exactly
when the original section does.

`rationalComponentBaseChange_naturality` proves the square of quotient
homomorphisms for an actual homomorphism `f : H → H'`, where `H'` is also
smooth affine over `k`. Surjectivity of the source quotient projection
reduces the equation to representatives, where it is the published
naturality of pulling back sections.

## Provenance and scope

This is an internal derived construction using the published
`IdentityComponent.baseChangeIso`, `GroupScheme.baseChangeSectionHom`,
their inclusion and naturality laws, and the rational quotient's
projection, universal lift and component embedding. The arguments above
describe the implemented Lean proofs. No external structure theorem is
introduced.

The construction concerns ordinary quotients of rational points. It
does not construct a quotient scheme or sheaf, identify these groups with
points of such a quotient, or assert surjectivity after field extension.
The component equation uses the first projection on actual schemes; it
does not assert a map in the opposite direction on all topological
components or a reverse homomorphism on the rational quotients.
