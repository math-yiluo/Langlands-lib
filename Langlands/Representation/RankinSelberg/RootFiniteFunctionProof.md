# Proof of finite-function closure with the inverse root-coordinate modulus

`Langlands.RankinSelberg.rootCoordinateFiniteFunction` proves
`RootCoordinateFiniteFunctionStatement F T n`.
The proof retains every prime, p-adic field, supplied topological data and
positive rank, including rank one.

First, the shared helper `T.continuous_normalizedAbs` from
`Langlands.LocalField.Normalization.Continuity` identifies the supplied field topology with the
canonical norm topology. The published normalization identity expresses the
normalized absolute value as a natural power of the canonical norm. Continuity
of the norm and of natural powers then proves continuity of the actual
normalized absolute value with respect to the supplied topology.
The Integrator moved the former private helper to that module so this proof
and the scalar Schwartz–Bruhat valuation-bounds proof use one declaration;
the helper's proof and the theorem's meaning are unchanged.

On the torus, composition with coordinate evaluation and the units coercion
makes each normalized absolute value continuous. Complex coercion, natural
powers and finite products preserve continuity. The product is nonzero,
because every coordinate is a unit and its normalized absolute value is
positive. Taking its reciprocal therefore proves continuity of the displayed
inverse-modulus weight. Multiplicativity and its value one at the identity
follow from the corresponding normalization identities, powers, finite
products and complex inversion.

The published `rootCoordinateChange` theorem supplies continuity and
multiplicativity of the explicit suffix-product coordinate map. Its value at
one follows directly from the formula. The proof packages the coordinate map
and weight as monoid homomorphisms, applies `finiteFunctionClosure` to pull back
each of the two input functions, then multiplies the two pullbacks and the
continuous character given by the weight.

This internal proof uses the published normalization and root-coordinate
results and the finite-function closure lemma. It proves no Whittaker
expansion, quotient integral identity or Mellin analytic conclusion.
