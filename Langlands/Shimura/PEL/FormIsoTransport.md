# Transport of form-compatible frames

This internal algebraic helper extends `FormIso` from `Similitudes`. It is derived
directly from that definition and makes no geometric existence assertion.

Let `ψ` be the scalar-valued source form and let `φ` and `φ'` be target forms
with respective value modules `L` and `L'`. Suppose a `B`-linear equivalence
`e : W ≃ W'` and an `R`-linear equivalence `c : L ≃ L'` satisfy
`φ'(e x,e y) = c(φ(x,y))`. Then `FormIso.transport e c hc` sends a compatible
frame `eta` to `e ∘ eta` and is an equivalence. Its inverse has underlying map
`e⁻¹ ∘ eta`. An existential value trivialization `a : R ≃ L` is transported
to `c ∘ a`; no trivialization is selected as part of the frame.

The inverse compatibility follows by applying the injective map `c` and the
assumed compatibility at `e⁻¹ x,e⁻¹ y`. Both inverse laws reduce to the inverse
laws of `e`, using subtype and linear-equivalence extensionality. Finally,
`transport_precomp` proves that transport commutes with source similitudes:
both underlying maps are `e ∘ eta ∘ g`. No compatibility between the `B`- and
`R`-actions beyond the displayed module structures is needed by this helper.
