# Arithmetic pair gamma factors of upper triangular zero-monodromy pairs

Arithmetic half of the principal-series pair gamma comparison. Throughout, `B` and `B'`
are local Weil–Deligne representations of a `p`-adic field `K`, with zero monodromy and
continuous Weil action. They have bases `b : Fin r → B` and `b' : Fin t → B'` in which
every Weil element acts upper triangularly (`IsUpperTriangularBasis`), with diagonal
entries `(χ_i ∘ e)(g)` and `(η_j ∘ e)(g)` for quasi-characters `χ_i`, `η_j` of `K^×` and
a reciprocity candidate `e` (`RankOne.weilCharacter K e`). The module computes the
arithmetic epsilon factor, the reflected L-ratio and the arithmetic gamma factor of
`[B] ⊗ [B']` as products over `(i, j)` of rank-one data of `χ_i η_j`. These are the
additivity of epsilon and L-factors over exact sequences, applied to the triangular
flags (Henniart 1986, §2.7(iii)).

## Internal definitions

- `FiniteRepresentation.transportRepresentation ρ f` is the representation
  `g ↦ f ∘ ρ(g) ∘ f⁻¹` moved along a linear equivalence of carriers. `transportEquiv`
  is the resulting equivalence.
- `baseCoordinatePair K B b` is the restriction of `B` to the Weil group of the bottom
  intermediate field (`baseExtension K`), with zero monodromy. It is carried on
  `ULift (Fin n → ℂ)` through the coordinates of `b`. This puts it in the carrier
  universe of the supplied local-constant system, which may differ from that of `B`.
  `baseCoordinatePairEquiv` shows that, for zero monodromy, it is equivalent to the
  actual restriction. Hence it is a valid base datum
  (`isBaseRestriction_baseCoordinatePair`) and continuous
  (`baseCoordinatePair_isContinuous`).

## Auxiliary results

- `IsUpperTriangularBasis.restrict`: upper triangularity survives restriction to a
  subgroup.
- `WeilDeligneRepresentation.classOf_eq_zeroMonodromy`: a pair with zero monodromy has
  the class of the zero-monodromy pair of its Weil representation.
- `conditionalDeligneValue_finsetSum`: Deligne's spectral value of a supplied system is
  multiplicative on finite sums of exact virtual classes. The proof is by induction from
  `conditionalDeligneValue_add`.
- `ofRepresentation_eq_sum_of_isBaseRestriction`: every continuous base datum `A` of
  `[B]` has exact class `∑ i [χ_i ∘ e |_base]`. This uses the equivalence to the
  restriction and the triangular lemma of `TriangularExactClass`.

## Epsilon

`isArithmeticPairEpsilonFactor_triangular`: for a common-closure system
`(eC, ε, hε)` and `e` agreeing with `eC` on the base field, `([B], [B'])` has the
arithmetic pair epsilon factor `epsilonFactorProduct` of the rank-one data
`(rankOneArithmeticEpsilonCoefficient K ψ (χ_i η_j), epsilonExponent (χ_i η_j) ψ)`.
The coefficient is the product over `(i, j)` and the exponent is the sum.

*Proof.* The existence clause uses the coordinate base pairs above. The additive
character and measure come from the rank-one constructed certificate. For arbitrary
admissible data, the pair `A ⊗ A'` has zero monodromy, so its conditional epsilon value
is the Deligne value of its exact class (`conditionalEpsilonValue_of_monodromy_zero`).
That class is `∑ i ∑ j [χ_i η_j]` by the tensor lemma. Multiplicativity turns the value
into a double product. Each factor is the rank-one value, from the rank-one arithmetic
certificate (`isArithmeticPairEpsilonFactor_rankOneWeilCharacterClass_iff`,
`isArithmeticPairEpsilonFactor_rankOne_constructed`). `epsilonMonomial_factorProduct`
matches the double product of monomials.

## L-ratio

- `coe_lFactorUnit_eq_prod_characterLFactor`: if a continuous representation has exact
  class `∑ i ∑ j [α_ij]`, its L-factor on inertia invariants is
  `∏ i ∏ j characterLFactor (α_ij)`. The proof applies the L-factor homomorphism
  `InertiaEuler.lFactorHom`.
- `arithmeticPairLFactor_triangular` and `arithmeticPairLFactor_dual_triangular`: the
  arithmetic pair L-factor of the zero-monodromy pairs of upper triangular `V`, `W` is
  `∏ i ∏ j characterLFactor (χ_i η_j)`. That of the duals is
  `∏ i ∏ j characterLFactor ((χ_i η_j)⁻¹)`. The proofs use
  `arithmeticPairLFactor_zeroMonodromy` with `V ⊗ W`, and with `(V ⊗ W)^∨` through
  `tensorDualEquiv`, together with `continuousDual_characterClass` for the dual class.
- `rationalLRatioClass_triangular`: for a geometric candidate `e`, the reflected
  L-ratio of `[B] ⊗ [B']` is `∏ i ∏ j P_{χ_i η_j}(X) / P_{(χ_i η_j)⁻¹}(q⁻¹ / X)`, with
  Tate's Euler polynomials `P`. The proof uses `rationalLRatioClass_eq` and
  `dualClass_tensorClass`; zero-monodromy duals are given by `dualZeroMonodromyEquiv`.
  `characterLFactor_weilCharacter` identifies the character L-factors with Tate's.
  `RationalReflection.subst` is an algebra map, so it commutes with the products.

## Gamma

- `rationalEpsilonMonomial_finset` and `coe_rationalEpsilonMonomial_factorProduct`:
  epsilon monomials are multiplicative in the coefficient and additive in the
  exponent.
- `isArithmeticPairGammaFactor_triangular`: for every self-dual measure `ν`,
  `∏ i ∏ j tateRationalGamma K ψ ν (χ_i * η_j)` is an arithmetic pair gamma factor of
  `([B], [B'])` for the supplied system. The epsilon part is the theorem above. The
  geometricity of `e` comes from `isGeometricReciprocity_of_isBaseReciprocity` and the
  normalisation clause of the system. The arithmetic coefficient equals Tate's
  coefficient at `ν` by `tateEpsilonCoefficient_eq_rankOneArithmetic`, using the
  uniqueness of the self-dual measure. The rest is factorwise algebra on
  `rationalGammaExpression`.
