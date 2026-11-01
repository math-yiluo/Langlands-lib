# Coherent action on original-chart domains and locally constant sections

Author: Worker 56.

This module constructs the action on all pairs consisting of an actual
original-chart domain and a locally constant function on that domain.
A full chosen bounded atlas isomorphism transports the domain by its actual
image and transports the section by inverse precomposition. Identity and
composition hold for entire pairs. The resulting construction applies to
every group action in the existing category of chosen atlas presentations,
and arbitrary coefficient postcomposition gives an equivariant map.

## Provenance and hypotheses

This is an internal construction from the existing Library interfaces.
It does not introduce a separate theorem attributed to the literature.
`ChosenAtlasLocallyConstantTransport` supplies the section equivalence
`isoOriginalDomainLocallyConstantEquiv`, built from
`isoOriginalDomainHomeomorph`. Its forward direction pulls image-domain
sections back to source-domain sections by the actual restricted forward
base map. Its inverse precomposes with the restricted inverse base map.
`ChosenAtlasDomainTransport` supplies the literal image domains, while
`ChosenAtlasDomainPresentation` relates the restricted homeomorphism to the
full bounded presentation isomorphism. Literal inclusion restrictions are
those of `OriginalDomainLocallyConstantSheaf`.

The field `K : Type u` is a complete ultrametric normed field. The input
presentations have point universe `v` and chart-index universe `w`.
Coefficients `D` and `E` lie in an arbitrary independent universe `z`;
the group `G` lies in an arbitrary universe `t`. These are full coefficient
sets, without topology or a prescribed group action.

## Domain-section pairs and transport

`OriginalDomainSection A D` has two fields: an original-chart domain
`domain` in the supplied atlas of `A`, and its entire locally constant
function `value : LocallyConstant domain D`. No subset of sections is
selected. The theorem `OriginalDomainSection.ext` proves equality from
equality of the actual domains and equality of the values at each common
ambient point, for every choice of its membership proofs. The proof
substitutes equal domains and uses extensionality of the functions.

For a full categorical isomorphism `e : A ≅ B`, write `H_S` for
`isoOriginalDomainHomeomorph e S`. Then `transport e` sends

\[
  (S,f)\longmapsto (e(S),f\circ H_S^{-1}).
\]

Here `e(S)` is the literal image of the subset `S` under the original
forward base map. The module constructs the new function using the inverse
of the existing section equivalence, so local constancy is already proved.
`transport_section_apply` gives the displayed inverse-precomposition formula,
and `transport_section_image` proves that the transported section at `H_S x`
has exactly the original value `f x`.

`transport_refl` and `transport_trans` prove

\[
  T_{\mathrm{id}}s=s,\qquad
  T_{e\mathbin{\mathrm{trans}}f}s=T_f(T_e(s)).
\]

Both are equalities of the entire domain-section pairs. Their domain
equations use the actual identity-image and composition-image equations.
After these domain equations, both function comparisons reduce to the same
inverse base maps and point evaluations. Proof irrelevance removes the
differences in subtype membership witnesses. The composition theorem does
not supply an independently chosen identification between the functions.

## Restrictions and coefficient maps

`restrict s S hS` takes a literal included domain `S ≤ s.domain` and
precomposes `s.value` with its actual inclusion. `restrict_self` and
`restrict_restrict` establish the identity and composite restriction
equations. `transport_restrict` proves that transporting a restricted pair
equals restricting the transported pair to the literal image subdomain.
The image inclusion is constructed by `isoOriginalDomain_mono`; pointwise
both sides apply the same original function to the inverse base image.

For any function `φ : D → E`, `map φ` keeps the domain and postcomposes its
section with `φ`, using `LocallyConstant.map`. The equations `map_id` and
`map_comp` prove functoriality on the pairs. `transport_map` and
`restrict_map` prove that coefficient change commutes with transport and
literal restrictions. These are equalities of complete pairs, proved with
the same extensionality theorem.

## The actual induced group action

An input `X : Action (AffinoidAtlasPresentation K) G` is a group action by
the full chosen bounded atlas arrows. Mathlib's `Action.ρAut` constructs
the inverse of each action arrow from the arrow for the inverse group
element. Thus every group element supplies the full isomorphism required
by the preceding transport.

`ChosenAtlasSectionAction.action X D` is an
`Action (Type (max v z)) G`. Its underlying type is
`OriginalDomainSection X.V D`, and its arrow at `g` is exactly
`OriginalDomainSection.transport (X.ρAut g)`. The identity law follows from
`transport_refl`. With Mathlib's convention for multiplication in categorical
endomorphisms, `X.ρAut (g * h)` first applies `h` and then `g`;
`transport_trans` proves precisely the corresponding left action law.
The theorems `action_domain` and `action_section_apply` expose the literal
image domain and the inverse-precomposition formula of this action.

`ChosenAtlasSectionAction.coefficientMap φ` is a morphism from
`action X D` to `action X E` in the category of group actions. Its
underlying function is the preceding `map φ`; the proved `transport_map`
equation supplies its full equivariance square.

The input supplies a genuine chosen atlas action, including its bounded
algebra maps; an arbitrary homeomorphism is not promoted to an analytic
map. This module equips the complete set of varying-domain section pairs
with an algebraic group action. It imposes no group topology, compactness
or nonempty coefficient hypothesis, and asserts no continuity or
smoothness of the resulting action. Empty domains and coefficient sets
remain available exactly when their full section types have elements.
The construction concerns original-chart domains of the supplied atlas;
general analytic and etale sites, refinement invariance, equivariant
gluing and the Harris tower remain further constructions.
