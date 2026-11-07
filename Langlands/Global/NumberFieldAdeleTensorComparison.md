# Full number-field tensor comparison

For number fields `K` and `L` in an arbitrary common universe, with an
`Algebra K L`, `numberFieldAdeleTensorEquiv K L` constructs the actual algebra
equivalence

`L ⊗[K] Adeles K ≃ₐ[L] Adeles L`.

Its underlying algebra map is exactly the existing `numberFieldAdeleTensorMap`;
`numberFieldAdeleTensorEquiv_toAlgHom` records that equality.
`numberFieldAdeleTensorEquiv_tmul` gives the pure-tensor formula: `a ⊗ x`
maps to the principal adele of `a` times the original full adelic inclusion of
`x`. No arithmetic decomposition is assumed as an extra parameter.

The construction uses the published `finiteAdeleTensorEquiv` and
`infiniteTensorEquiv` at every infinite place. Tensor distribution over the
finite product of infinite completions, followed by commuting the two tensor
factors in each component, gives the product of the local comparisons. An
additive equivalence regroups the places above each lower infinite place
into the actual upper infinite adele ring. Tensor distribution over the
infinite/finite pair then gives an additive equivalence of the full rings.
The proof identifies its coordinate formula with the literal canonical map on
pure tensors, and tensor induction extends the equality to all tensors.
`numberFieldAdeleTensorMap_bijective` follows from this additive equivalence,
and `AlgEquiv.ofBijective` supplies the stated algebra equivalence.

The construction retains every archimedean factor and uses the actual
restricted product for the finite factors. The result is derived from those
published arithmetic comparisons; it is the number-field arithmetic identity
underlying the natural equality of adelic point sets in Conrad's
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
Example 4.2, printed pp.9–10. The explicit algebra-equivalence packaging and
the assembly through additive equivalences are derived constructions.

This unit addresses number fields. The function-field tensor comparison and
the topological Weil-point comparison are separate results. No tensor-product
topology is asserted here.
