# Positive radical inclusion along descended facet incidence

`Langlands.BruhatTits.IntegralModels.unramifiedFacetPositiveRadical` proves exactly
`UnramifiedFacetPositiveRadicalStatement.{u}` at arbitrary universe `u`.
It retains the seven building hypotheses, the eight apartment-descent hypotheses,
and every model and quotient quantifier of the published statement. Its conclusion
is the subgroup inclusion `Q.positivePoints ≤ Q'.positivePoints` in the actual
rational-point group for incident facets. It adds no premise.

The proof uses the published unconditional theorem
`unramifiedRadicalRootGeneration`. For the given upstairs building `C` and zero
datum `E`, that theorem supplies one common subgroup `H` and the radical-preimage
formula for all characterized descended models and their reductive quotients.
The proof uses this same `H` for both incident facets. The theorem already
incorporates the actual radical identification and unramified descent; neither
is assumed again here.

The incidence witness writes the two facets as translates of apartment facets
`Fa` and `Ca`, with `Fa` a face of `Ca`, using the same element `g`. The facet
pullback hypothesis implies that `a` maps each source apartment facet into the
upstairs facet through its image point. In particular, the two image subsets
`a '' Fa` and `a '' Ca` are nonempty and each lies in one upstairs facet, as
required by the generation theorem. Equivariance of `e` and its compatibility
with the apartment maps identify their translates with `e '' Fc.val` and
`e '' Fc'.val`. This gives precisely the integral-point characterizations
needed to apply the two radical-preimage formulas to the supplied models and
quotients.

The private lemma `affine_mem_facetClosure` transfers combinatorial facet closure
along `a`. The published `AffineRootSystem.facetClosure_subset_closure_facet`
places a source closure point in the topological closure of the source facet.
Each upstairs affine root composed with `a` is continuous, since the source
apartment is finite dimensional. Its nonpositive, zero, or nonnegative region
is closed. Constancy of the root sign on the image facet therefore gives the
required weak sign at the image closure point. The three cases for the sign
at the base point establish membership in the upstairs combinatorial closure.
The metric and finite-dimensional instances for the source apartment come from
the published valuation-building metric constructions.

Choose `w` in `Fa`. For every `x` in `Ca`, incidence places `w` in the
combinatorial closure of the source facet through `x`. The private lemma then
places `a w` in the upstairs facet closure through `a x`. The published
`filtration_comparison_of_mem_facetClosure`, using the AS4 property supplied by
`IntegerValuationBuildingData.affineRoot_mem_or_two_smul_mem`, implies

```
C.rootFixerPlus α (a '' Fa) ≤ C.rootFixerPlus α (a '' Ca)
```

for each relative root `α`. Here positive root fixers use membership in the
positive filtration at every point of the subset. Membership at `a w`, followed
by the closure comparison for each `a x`, proves the displayed inclusion.

Taking the supremum over the roots and adjoining the same `H` preserves this
inclusion. Mapping by conjugation with `rationalExtend F (inertiaFixedField F) G g`
and taking the inverse image along `rationalExtend F (inertiaFixedField F) G`
also preserve it. The two generation equalities then give the requested
inclusion of the actual `Q.positivePoints` subgroups.

The private affine-base-change instance only supplies affineness by stability
under pullback. The provenance of the proof is internal: it composes the
published radical-generation, facet-incidence, affine-closure and root-filtration
theorems. The target's unchanged Markdown records its KP Axiom 4.1.22(7),
Corollary 8.4.12 and §9.5 interpretation. This file proves the inclusion component
specified by that target; reduction-surjectivity assertions are outside its
conclusion. Some retained target hypotheses are unused by this proof.
