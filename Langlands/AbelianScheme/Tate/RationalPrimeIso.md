# Actual prime rational Tate maps and rational isomorphisms

This module extends the interface of the published actual prime Tate construction
to rational isomorphisms. It works over any `S : Scheme.{u}`, any test object
`T : Over S`, and every natural prime `p` with `Fact p.Prime`. It introduces
`Langlands.AbelianScheme.Tate.PrimeAdic.rationalIso`; the other declarations are
compatibility lemmas for the existing constructions.

The imported `RationalPrimeHom` already defines
`PrimeAdic.rationalHomMap T p` as the rational-linear map

```text
Rationalization.Hom A B →
  (PrimeAdic.Rational A T p →ₗ[ℚ_[p]] PrimeAdic.Rational B T p).
```

Here the domain is the existing `ℚ ⊗[ℤ] (A ⟶ B)` and the actual target Tate
module is `ℚ_[p] ⊗[ℤ_[p]] PrimeAdic.Integral A T p`, whose integral factor
consists of coherent sequences of actual prime-power torsion sections. The
values of the Hom map are linear over `ℚ_[p]`; its dependence on a rational
homomorphism is linear over `ℚ`. The imported map is the additive
rationalization lift of the actual prime Tate functor. Its published
`rationalHomMap_tmul`, `rationalHomMap_ofHom`, `rationalHomMap_identity` and
`rationalHomMap_comp` supply the pure-tensor, integral-inclusion, identity and
composition laws.

`rationalHomMap_ofHom_groupHom` spells out that the value on
`Rationalization.ofHom f` is exactly
`Langlands.GroupScheme.Tate.PrimeAdic.rationalMap T p
(AbelianScheme.groupHom f)`. Thus this interface retains the original
group-scheme map, with no choice of representation. `rationalHomMap_smul`
states rational scaling on every rational Hom element. It is the scalar law
of the existing linear map. `rationalHomMap_ofHom_tmul` evaluates the map on an
integral homomorphism and a pure tensor in the actual prime Tate module:
`a ⊗ x` maps to `a ⊗ PrimeAdic.map T p f x`.
`rationalHomMap_tmul_apply` evaluates a rational Hom pure tensor `q ⊗ f`
at any prime Tate vector `x`, giving `q • PrimeAdic.rationalMap T p f x`.
The scalar action by `q : ℚ` is restriction of the p-adic scalar action.
`rationalEndAction_ofEnd` gives the integral-inclusion formula for the existing
rational endomorphism algebra action.

`rationalIso T p e` applies the existing rationalized prime Tate functor to
`e : Rationalization.of A ≅ Rationalization.of B` and converts the resulting
module isomorphism to a p-adic-linear equivalence. Its forward map is exactly
`PrimeAdic.rationalHomMap T p e.hom`, as stated by `rationalIso_apply`.
The inverse uses `e.inv`. The laws `rationalIso_refl`, `rationalIso_trans` and
`rationalIso_symm` express compatibility with identity, composition and inverse.
The identity and composition proofs evaluate the existing rational Hom laws on
a vector; inverse compatibility is definitional.

All these declarations are internal consequences of the imported published
prime Tate functor and the additive rationalization lift. This module introduces
no geometric faithfulness assertion. The separate
`FieldPrimeRationalFaithfulnessStatement` module gives that unproved target and
its conditional consequences over algebraically closed characteristic-zero
fields. No existing Tate definition or rigidity statement is modified.
