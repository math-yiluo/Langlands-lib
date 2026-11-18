# Proof: ground-field extension of affine analytification

The theorem
`Langlands.Analytic.AffineAnalytification.affineAnalytificationBaseChange`
proves the unchanged proposition
`Langlands.Analytic.AffineAnalytification.AffineAnalytificationBaseChangeStatement.{u, u', v}`.
Its module is
`Langlands.Geometry.Analytic.AffineAnalytificationBaseChangeProof`.

Let `K : Type u` and `L : Type u'` be complete, ultrametric, nontrivially
normed fields with `NormedAlgebra K L`, and let
`P : FinitePolynomialPresentation K A` present a commutative `K`-algebra
`A : Type v`. The theorem proves that `baseChangeMap K L P` is surjective.
For each `φ : AlgPoint K A K`, it also proves that the inverse image of
`{analyticPoint K P φ}` is the singleton consisting of the analytic point
of the scalar-extended character

```text
φ_L : L ⊗[K] A →ₐ[L] L,
φ_L (l ⊗ a) = l * algebraMap K L (φ a).
```

The three universes are independent. The extension `L/K` need not be finite.
There is no norm on `A`, and no reducedness, nonemptiness or positive-arity
hypothesis. The proof uses only `propext`, `Classical.choice` and `Quot.sound`.
All helper declarations belong to the namespace
`Langlands.Analytic.AffineAnalytification.BaseChangeComparison`.

## Source correspondence and provenance

Berkovich, *Spectral theory and analytic geometry over non-Archimedean
fields* (1990), introduces ground-field extension of affinoid spaces in
§2.3, printed pp.32–33 / PDF pp.46–47. The proof of Proposition 2.2.4,
printed p.29 / PDF p.43, uses surjectivity of the canonical map from a
ground-field extension and of the analogous maps for affinoid domains.
Remark 3.4.2, printed p.64 / PDF p.78, identifies the points of the
analytification of `Spec(A)` with multiplicative seminorms on `A` extending
the base-field norm. These passages motivate the two clauses of the
published target; they do not state this polynomial-presentation theorem
verbatim.

The registered source is
`provided-a03a0182668f6b92b01deacac09a9992b3edf55e23a0a2194554384ae44bd8d4`,
SHA256
`9b543e7ffae8ec6febf154a60c4d11a288f7ecc3795c66f004ba3200a6824e79`.

The implementation is an internal derivation using the Library's seminorm
comparison, complete-field realization, tensor seminorm and multiplicative
domination theorems. The tensor construction comes from Ben Yaacov,
*Tensor products of valued fields* (2015), Definition 6 and Lemma 7,
retained author version p.2, source
`ben-yaacov-2015-tensor-products-valued-fields`, SHA256
`9fe54c994f66a41132e4593626c05f930f884276ff0a1ee8786fbdd2a9f280a0`.
Only submultiplicativity, the strong triangle inequality, normalization at
one and upper bounds on pure tensors are needed here. Multiplicativity
on the tensor algebra is obtained separately by domination, with no
algebraic-closure assumption. The argument does not construct a completed
tensor algebra or invoke a same-universe field-amalgamation statement.

## Scalar-normalized seminorms and field realizations

`normedRealization` starts with a multiplicative seminorm `ν` on a
commutative `K`-algebra whose restriction to `K` is the norm
(`ExtendsNorm K ν`). The comparison lemma `SeminormComparison.add_le_max`
makes `ν` ultrametric. `Langlands.Analytic.seminormRealization` then gives
a complete ultrametric normed field `H` and a ring map `f` with
`‖f a‖ = ν a`. The imported construction takes the fraction field of the
quotient by the seminorm's zero ideal and completes its induced norm.

Give `H` its `K`-algebra structure through `f ∘ algebraMap K A`. Its
scalar map preserves norms because `ν` extends the norm of `K`, so the
norm multiplication formula supplies `NormedAlgebra K H`. Thus `f`
is a `K`-algebra map. The field `H` stays in the universe of the source
algebra.

`pullback` restricts a multiplicative seminorm along a ring homomorphism.
`field_restriction` proves that a contractive restriction to a normed
field `F` is exactly its norm: it packages the restriction as a point
of `BanachSpectrum F` and applies `BanachSpectrum.field_apply`. This is
the field argument using an element and its inverse.

## Extension of seminorms and surjectivity

`exists_extension` extends any `ν : MulRingSeminorm A` satisfying
`ExtendsNorm K ν` to `μ : MulRingSeminorm (L ⊗[K] A)` such that

```text
ExtendsNorm L μ,
μ (1 ⊗ a) = ν a  for every a : A.
```

First apply `normedRealization` to obtain `f : A →ₐ[K] H`. The theorem
`exists_ultrametricTensorSeminorm` supplies a normalized nonarchimedean
ring seminorm `p` on `L ⊗[K] H` whose restrictions to `L` and `H` are
at most their norms. `BanachSpectrum.nonarchimedeanDomination` supplies a
multiplicative seminorm `q ≤ p`. Both field restrictions of `q` equal
the original norms by `field_restriction`. Pulling `q` back along
`Algebra.TensorProduct.map (AlgHom.id L L) f` gives `μ`. Commutation
with scalars proves its `L`-normalization, and evaluation on `1 ⊗ a`
gives `μ (1 ⊗ a) = ‖f a‖ = ν a`.

In `surjective_baseChangeMap`, take
`ν = pointSeminorm K P x` for a given point `x`. The extension `μ`
corresponds to a point `y` over `L` by
`SeminormComparison.range_pointSeminorm`. The identity
`pointSeminorm_baseChangeMap` identifies the seminorm of
`baseChangeMap K L P y` with `ν`. The injectivity theorem
`SeminormComparison.pointSeminorm_injective` gives equality with `x`.

## The fibre over a rational point

`CenterComparison.pointSeminorm_analyticPoint` computes the seminorm of the analytic
point of an algebraic character: its value at `a` is `‖φ a‖`. The
proof unfolds its chart representative and uses the published
character evaluation formula.

`rationalLift` is precisely
`Algebra.TensorProduct.liftEquivRight K L A L
  (AlgPoint.mapCoefficients (Algebra.ofId K L) φ).toAlgHom`.
The equation in `rationalLift_tmul` is its defining pure-tensor
evaluation. `baseChangeMap_analyticPoint` uses that equation and
preservation of scalar norms to show that its analytic point maps to
`analyticPoint K P φ`.

For uniqueness, `eq_analyticPoint_of_baseChangeMap` starts with a point
`y` mapping to `analyticPoint K P φ`. Apply `normedRealization` over
`L` to the seminorm of `y`, obtaining a norm-preserving algebra map
`f : L ⊗[K] A →ₐ[L] H`. For every `a : A`, the fibre condition says

```text
‖f (1 ⊗ (a - algebraMap K A (φ a)))‖ = 0.
```

Definiteness of the field norm, additivity and scalar commutation
therefore give
`f (1 ⊗ a) = algebraMap L H (algebraMap K L (φ a))`.
Tensor induction extends this equality to the identity of algebra maps
`f = (Algebra.ofId L H).comp (rationalLift K L φ)`. For a pure tensor,
write `l ⊗ a = l • (1 ⊗ a)` and use scalar linearity; the additive
induction step uses preservation of addition.

Since `algebraMap L H` preserves norms, the seminorm of `y` is exactly
`b ↦ ‖rationalLift K L φ b‖`. The seminorm computation for an analytic
rational point and injectivity over `L` identify `y` with the asserted
point. The final theorem combines surjectivity with the two directions
of the singleton-fibre equality by set extensionality.

This proves the two clauses of the published target. It makes no
claim about other fibres or scheme-level ground-field extension.
