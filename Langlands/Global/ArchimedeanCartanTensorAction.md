# Bounded Cartan tensor actions on genuine enveloping modules

This internal algebraic construction uses the actual archimedean Cartan
complement, its symmetric algebra and symmetrization into the genuine universal
enveloping algebra. The field `K` has arbitrary universe and the rank is any
natural number.

For a continuous finite dimensional representation `τ` of the whole standard
compact subgroup, `cartanSymmetricTensorDegreeFiltration τ d` is the complex
span of tensors `P ⊗ v` with `P` in the actual Cartan symmetric monomial span of
degree at most `d`. These spans increase with `d`. Compact conjugation preserves
the bound on each monomial, since it replaces every vector in the monomial by
its actual linear conjugate. Span induction proves preservation for all bounded
Cartan tensors. Tensor span induction then proves that the actual diagonal
compact representation preserves every bounded tensor span.

Let `V` be any genuine left enveloping module with its compatible complex scalar
action, and let `j` be a complex linear map from the canonical representation
space of `τ` to `V`. The map `cartanTensorAction τ j` sends `P ⊗ v` to
`sym_p(P) • j(v)`. It is constructed by the tensor universal property from the
bilinear map obtained by composing actual Cartan symmetrization with the genuine
algebra action on `V` and then with `j`.

`cartanTensorAction_map_degreeFiltration` identifies the image of the bounded
tensor span with `cartanSymmetrizationSpan d • range j`. The forward inclusion
checks a pure tensor and extends by linearity; the reverse inclusion chooses a
Cartan preimage for its enveloping factor and a preimage under `j` for its vector
factor. If the range of `j` is stable under all actual complex compact Lie
generators, `cartanTensorAction_map_degreeFiltration_eq` identifies this image
with the full filtered enveloping action span `F_d • range j`, by the previously
proved Cartan filtered spanning theorem.

Finally, `cartanTensorAction_equivariant` assumes a compact representation `ρ`
on `V`, equivariance of `j`, and the genuine compatibility
`ρ(k)(a • v) = Ad(k)(a) • ρ(k)(v)`. Tensor induction, actual Cartan
symmetrization equivariance and these two assumptions prove equivariance of the
tensor-action map. No topology or finite orbit condition on `V` is assumed.

This pair is derived from the published concrete constructions and the filtered
spanning result. It does not prove invariant preimage lifting, finite central
generation or the automorphic differential growth statement.
