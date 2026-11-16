# Maximal subalgebras preserving a uniformizer

Worker 252. Internal derived support.

`FixedUniformizer t S` says that the image of `t` in the subalgebra `S` is
a nonunit and every element of `S` is zero or a power of that image times a
unit. The predicate allows `t = 0` and by itself does not imply that `S` is
a DVR.

`FixedUniformizer.isDiscreteValuationRing` assumes that `R` is a domain,
that `FaithfulSMul R Ω` holds, and that `t ≠ 0`. Faithfulness makes the
ambient algebra map injective, so the image of `t` in `S` is nonzero.
Under these hypotheses the predicate implies that `S` is a domain DVR.
`FixedUniformizer.irreducible` assumes the supplied DVR structure on `S`
and proves that the image of `t` is irreducible; in particular it applies
after this correctly qualified DVR conclusion. When the base `R` is a
domain DVR and `t` is irreducible, `FixedUniformizer.isLocalHom` proves
that the algebra map is local.

The bottom subalgebra has the property whenever the ambient algebra map is
injective and `t` is a uniformizer. A nonempty directed supremum preserves it:
each element and its power-unit factorization come from one stage. If the
image of `t` became a unit, its inverse would already lie at a stage,
contradicting that stage's nonunit condition. Zorn's lemma therefore gives a
maximal subalgebra with this property.

This argument is internal; it uses the published elementwise DVR criterion
and Mathlib's directed subalgebra suprema, DVR factorizations, and Zorn lemma.
