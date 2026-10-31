# Rational Lie pullback from canonical integral naturality

Author: Worker 57.

This internal construction extends canonical integral Lie naturality to
the actual rational homomorphisms used by the Harris moduli problem.
It depends explicitly on
`naturality : LieBaseChangeNaturalityStatement S`.
That published proposition remains a separate proof obligation. This
module supplies neither its proof nor cotangent naturality.

The base schemes `S,T` and the commutative ring `R` have the same arbitrary
universe `u`. The ring is an actual rational algebra, `p : S → Spec R`
is an actual structure morphism, and `b : T → S` is arbitrary.
No flatness, reducedness, affineness or characteristic assumption on the
schemes is added. Rational Lie scalars on `T` come from `b ≫ p`.

`lieMap_baseChange_of_naturality` applies the named naturality proposition
to the already constructed `lieBaseChangeIso` for both abelian schemes.
Their invertible cotangent comparisons and canonical equations are supplied
by the published Lie base-change theorem and characterization. The
comparisons are thus those uniquely determined by the existing actual
cotangent and dual maps.

`lieMap0_baseChange_of_naturality` proves the corresponding square for
every actual rational homomorphism. Such a homomorphism belongs to
`ℚ ⊗[ℤ] Hom(A,B)`. Tensor induction handles sums and pure tensors;
zero is already a pure tensor.
For `q ⊗ f`, the rational Lie map is `q` times the actual differential,
and actual rational pullback is `q ⊗ pullback(f)`. Module-sheaf pullback
is additive and hence linear over the rational scalar structures.
Bilinearity of composition reduces the square to the integral one.
No rational naturality or scalar compatibility equation is assumed.

`rationalLieBaseChangeIso` assembles the same canonical comparison
components into a natural isomorphism

```text
rationalLieFunctor(p) ⋙ modulePullback(b)
  ≅ rationalBaseChange(b) ⋙ rationalLieFunctor(b ≫ p).
```

The proved rational square supplies naturality for every rational
homomorphism, and the two component formulas retain the original hom and
inverse of `lieBaseChangeIso`.

`baseChangeRationalOrderAction` composes an actual rational order action
with the constructed rational algebra homomorphism on endomorphisms.
Its application formula and compatibility with restricting an action
along a ring homomorphism are definitional. The theorem
`lieRationalOrderAction_baseChange_of_naturality` specializes the proved
rational square to each element of this action.

The provenance is tensor induction on the existing rationalization,
additivity of actual module pullback, and the existing canonical
comparison characterization. This is a compatibility adapter for the
parent construction, with no additional external-source assertion.
It does not assert unconditional integral naturality, determinant or
trace stability, a varying-base PEL functor, representability, or scheme
levels.
