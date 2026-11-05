# Scalar cancellation in restrictions of tensor contractions

This internal derived unit constructs a tensor contraction from two actual
chart comparisons and proves its restriction law. All schemes have the same
arbitrary universe. The construction needs an isomorphism from the pullback
of a module `A` to a local module `L`, and an isomorphism from the pullback
of a module `B` to the actual structure module. It assumes no global
trivialization of `B`.

`tensorRightUnitor_unitAut` moves multiplication by a unit on the structure-module
factor through the right unitor. `tensorContraction_pullback` identifies pullback
of a contraction with contraction of the pulled-back morphisms, using the
canonical structure-module comparison. `tensorContraction_scaled` combines the
naturality of the right unitor with its scalar formula.

`tensorChartContractionIso j a b` first uses the actual invertible pullback
tensor comparison, then tensors the two supplied local isomorphisms, and
contracts `L ⊗ O` by the right unitor. Its morphism formula is

`pullbackTensorComparisonApp j A B ≫ tensorMap a.hom b.hom ≫ rightUnitor`.

For `r : U ⟶ V` and compatible chart maps `jU`, `jV` to `X`, write `CA`
and `CB` for the canonical equal-composite comparisons on `A` and `B`.
Suppose the first local comparisons satisfy `r*aV ≫ gamma = CA ≫ aU`
and the second satisfy
`r*bV ≫ pullbackUnitIso(r) ≫ unitAut(c) = CB ≫ bU`.
Here `gamma : r*LV ⟶ LU` is any module morphism, and `c` is an actual
global unit on `U`. Then `tensorChartContractionIso_restrict` proves

`r*contractionV ≫ gamma ≫ unitAut(c) = Ctensor ≫ contractionU`.

Thus the inverse scalar in the restricted second coordinate cancels
the extra scalar in the transition of the local target module.
Both coordinate restriction equations are explicit hypotheses of this generic
lemma; this unit does not assert them for any particular projective atlas.

The proof first applies contraction pullback compatibility and moves the scalar
onto the structure-module factor using `tensorContraction_scaled`. The two
coordinate equations then replace both factors. The existing `compHom_tensor`
identity and functoriality of `tensorMap` identify the result with the canonical
restriction of the smaller contraction.

All assertions are derived from existing canonical tensor comparisons, their
proved right-unitor compatibility, actual scalar automorphisms, and tensor
compatibility of equal-composite pullback. No new literature assertion is used.
Application to the genuine tensor-frame atlas, the global degree-one
comparison, and the ordinary-moduli representability theorem remain open.
