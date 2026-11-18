# Adjoint affine Weil existence from split isomorphism and pair descent

Worker 632, adapting Worker 634's simply connected comparison and existence
construction, with Worker 5254's adjoint component coordinates.

For an adjoint affine pinned model with nontrivial geometric fibres,
`AffineAdjointWeilPresentation.ofPinnedModel` constructs an actual adjoint
Weil presentation, assuming the affine split isomorphism theorem and
generic étale pair descent.

The root-generated character coordinates supply the Cartan-component data.
Their relative derived component groups are reductive. On every
algebraically closed field-valued pullback, the actual root-component
normal-model product is isomorphic to the original adjoint group, and the
actual component-derived comparisons identify it with the field pullback
of the relative product.

Worker 634's generic further-étale pinned comparison then supplies actual
product isomorphisms on affine étale charts covering the base. This step
uses the supplied affine split isomorphism theorem; it does not infer
equality of maps over a nonreduced base from equality on field fibres.

The relative factors have almost-simple geometric fibres after these
base changes, by their actual field comparisons under the ambient adjoint
semisimplicity hypothesis. The full centre of the original pinned adjoint
group is trivial over its ring and remains so on each chart. The existing
finite-family adjoint presentation construction therefore gives local
adjoint Weil presentations, including the finite base's surjectivity.
Generic pair descent globalizes them while retaining the adjoint and
almost-simple geometric factor conditions.

This is an internal adjoint adaptation of the component, field-product,
further-étale comparison and descent interfaces. Both structural inputs
remain explicit. The generic comparison follows the classification route
of Conrad, *Reductive group schemes* (2014), Proposition 6.4.4 and
Remark 6.4.5, pp.232–233.
