# Rational Lie maps on a fixed scheme are independent of the rational base

Author: Worker 57.

This internal derived construction compares the existing rational Lie maps
when two actual structure morphisms on the same scheme supply rational
scalars. It is needed to write the Harris determinant and central trace
conditions through the same CM structure map. It introduces no new assertion
attributed to external literature.

For an actual scheme `S : Scheme.{u}`, two commutative ring objects `R` and
`R'` with rational algebra structures, and actual maps `p : S → Spec R`
and `q : S → Spec R'`, `rationalLinearOverBase_eq` proves equality of the
constructed rational-linear structures on `S.Modules`. The proof unfolds
`rationalLinearOverBase` and uses uniqueness of the ring homomorphism from
`ℚ` into the actual global section ring. No equality of `p` and `q` is
required.

`lieMap0_base_independent` rewrites this equality in the rational extension
of the actual Lie functor. `rationalLieBaseIso` then constructs a natural
isomorphism between the two rational Lie functors whose components and
inverse components are the identity on each actual Lie sheaf; its
naturality is exactly the proved equality of differentials. The lemma
`lieMap0_base_independent` proves equality of the two actual
sheaf morphisms assigned to every rational homomorphism between two abelian
schemes over this fixed `S`. Extensionality then proves equality of the
rational order-action ring homomorphisms. Their restrictions to a fixed
open and their actions on a fixed section module are equal by the
constructed definitions. Rewriting the local action proves equality of
the fixed-chart determinant polynomials and traces for any ring of
acting elements, finite family, actual finite Lie chart and smaller open.

The construction reuses `ModuleLinear`, `LieRational`,
`LieRationalDeterminant`, `LieRationalTrace` and Mathlib's uniqueness of
rational ring homomorphisms. This compares choices of scalar-supplying
maps on a fixed scheme and its fixed abelian schemes. It does not compare
Lie sheaves on different schemes, prove naturality under scheme base
change, or identify the arithmetic coefficient sections of independently
specified base maps. Those are separate obligations.
