# Essential vectors of supercuspidal representations over p-adic fields

Module `Langlands.Representation.Conductor.SupercuspidalPadicEssentialExistence`, namespace
`Langlands.Conductor.SupercuspidalPadic`. This is a helper
module for [`SupercuspidalPadicConductorExponentProof`](SupercuspidalPadicConductorExponentProof.md).
It defines nothing new. It proves three theorems, all at independent universes `uF`
(the field) and `uV` (the carrier of `π`).

Throughout, `K : PadicField.{uF} p` is a p-adic field and `K.Carrier` carries the topology,
valuative relation and local-field structure of `K.canonicalTopologicalData`. The module
installs these as local instances. `T` abbreviates `K.canonicalTopologicalData`.

## Mathematical content

Let `π` be an irreducible admissible generic supercuspidal representation of
`GL_(n+2)(K)`. Under Jacquet's normalizations, every nonzero Whittaker model of `π`
contains an essential vector, with the standard L-polynomial `1`.

The source is Jacquet, *A correction to Conducteur des représentations du groupe
linéaire*, Pacific J. Math. 260 (2012) (literature ID `jacquet-2012-conductor-correction`).
Its Theorem 1 states the essential vector, and Remark 1 (printed p. 523) says that the
1981 existence proof is correct when `L(s, π) = 1`.
The Lean proof below does not follow the 1981 argument. It uses the zero-cell function,
which has a direct proof when `L = 1`.

## `eq_normalizedAbsoluteValue`

An absolute value `abv` on `K.Carrier` with `abv ϖ = q⁻¹` for a uniformizing element `ϖ`,
where `q` is the residue cardinality, and with `abv x = 1` on valuation units, equals
`normalizedAbsoluteValue T`.

*Proof.* The published `AllField.RankinSelberg.eq_normalizedAbsoluteValue_ofInstances`
(module `Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction`)
says that such an absolute value is a fixed canonical one. Apply it to `abv` and also to
`normalizedAbsoluteValue T`. For the second application, the published
`exists_uniformizingElement_normalizedAbs` and `normalizedAbsoluteValue_eq_one` (module
`Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput`) give a
uniformizing element `ϖ₀` with normalized absolute value `q⁻¹`, and give the value `1` on
units. Then combine the two equalities.

## `isCharacterLPolynomial_one_of_isSupercuspidal`

For `ψ` a unitary additive character and `π` an irreducible supercuspidal representation
of `GL_(n+2)(K)`, the statement is
`IsCharacterLPolynomial T.residueCardinality ψ (normalizedAbsoluteValue T)
(rankOneQuotientHaar K.Carrier) 1 π 1`.
Here `GL_1` and `N_1 \ GL_1` carry their Borel σ-algebras. So the standard L-factor
`L(s, π × 1)` is `1`.

This is Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*, Amer. J.
Math. 105 (1983), §(8.1), Proposition (i), printed p. 443 (literature ID
`jpss-1983-rankin-selberg`), for `σ` the trivial character of `GL_1`.

*Proof.*
- The published `nonempty_selfDualHaar` (module `…HighlyRamified.EssentialInput`) gives
  an additive Haar measure `ν` that is self-dual for `ψ`.
- The published `scalar_isOfWhittakerType_rankOne`, together with
  `rankOneCharacter_one_isSmooth` (module
  `Langlands.Representation.Conductor.TrivialCharacterEpsilonReduction`), makes the
  trivial character of `GL_1` a representation of Whittaker type.
- The published `RankinSelberg.supercuspidalUnequalRankLFactor` (module
  `Langlands.Representation.RankinSelberg.SupercuspidalUnequalRankLFactorReduction`) is
  JPSS 1983 (8.1)(i). Here it is applied at ranks `r = n + 1` and `t = 0`. It gives
  `IsPadicPairLPolynomial K ψ ν π 1 1`.
- The definition `IsPadicSymmetricLPolynomial` reads the larger rank first, so it unfolds
  to that pair statement. The `if` is resolved by `ite_eq_left` at `0 ≤ n + 1`.
- The published `isCharacterLPolynomial_of_isPadicSymmetricLPolynomial` (module
  `…HighlyRamified.EssentialInput`) turns the result into the `IsCharacterLPolynomial`
  clause.

## `exists_isEssentialVector`

Fix `n` and bind the measurable and Borel structures on `GL_(n+1)`, `N_(n+1)` and `GL_1`
and the measurable structures on `N_(n+1) \ GL_(n+1)` and `N_1 \ GL_1`, exactly as
`IsJacquetNormalization` and `IsEssentialVector` (module
`Langlands.Representation.Conductor.Essential`) do. Then let
`h : IsJacquetNormalization q ψ abv ϖ μ` be any choice of Jacquet's normalizations. Let `π`
be a representation of `GL_(n+2)(K)` with `IsGeneric ψ (n + 1) π` and
`IsSupercuspidal π`, and let `ℓ` be a nonzero Whittaker functional. Then some
`w` in the coefficient model `coefficientModel π ℓ` satisfies
`IsEssentialVector h π ℓ w`.

*Proof.*

1. **Normalization.** By `eq_normalizedAbsoluteValue`, `abv = normalizedAbsoluteValue T`.
   Also `q = T.residueCardinality` by `h.residueCardinality`. Both are substituted. Every
   bound measurable structure is Borel: those on `GL_(n+1)`, `N_(n+1)` and `GL_1` by the
   bound `BorelSpace` instances, and those on the two quotients by `h.borel` and
   `h.borel_rankOne`. So `BorelSpace.measurable_eq` replaces each of them by `borel _`.
   This is the form that the published zero-cell lemmas use.
2. **The vector.** The published `zeroCellWhittaker hϖ hψ (n + 1)` (module
   `…HighlyRamified.EssentialInput`) is the `ψ`-Whittaker function `W₀` on `GL_(n+2)`. It
   takes the value `ψ(u)` at `u k`, for `u` upper unipotent and `k ∈ GL_(n+2)(O)`, and the
   value `0` off `N · GL_(n+2)(O)`. Its restriction to the mirabolic subgroup is a
   mirabolic test function (`isMirabolicTestFunction_zeroCellWhittaker`). The Kirillov
   theorem `Whittaker.modelKirillovTransfer` (module
   `Langlands.Representation.Whittaker.ModelKirillovProof`) is applied to the published
   `whittakerTypeKirillov` (module `Langlands.Representation.Whittaker.WhittakerTypeKirillovProof`)
   and to `isOfWhittakerType_of_isGeneric`. It gives a vector `w` of the model of `ℓ` that
   agrees with `W₀` on the mirabolic subgroup.
3. **L-polynomial.** The L-polynomial is `P = 1`, by
   `isCharacterLPolynomial_one_of_isSupercuspidal` (this uses `hπ.1` and `hsc`).
4. **Essential identity.** Fix `x`. The published `corankOneIntegrand_eq_zeroCell` shows
   that the corank-one integrand of `w` against the spherical function
   `inverseSphericalWhittaker hψ hϖ q x` equals that of `W₀`. This is because the
   integrand only uses values on the mirabolic subgroup. The spherical function is right
   `GL_(n+1)(O)`-invariant (`inverseSphericalWhittaker_mul_integral`) and takes the value
   `1` at the identity (`inverseSphericalWhittaker_one`), both from module
   `Langlands.Representation.Conductor.Essential`. So the published
   `integrable_integral_corankOneIntegrand_zeroCell` applies: for every `s`, the
   integrand is integrable and its integral is `1`. Therefore the integral converges on
   every half-plane (the witness is `a = 0`). It also equals the constant `1` there. Since
   `essentialFactor 1 x = ∏ 1⁻¹ = 1` (by `simp`), the published
   `hasRationalContinuation_one_of_eq_on_halfPlane` (module
   `Langlands.Representation.RankinSelberg.EqualRankUnitNormalization`) gives the
   rational continuation `1`.
5. **Integral invariance on the restriction.** For `g ∈ GL_(n+1)` and
   `k ∈ GL_(n+1)(O)`, the elements `diag(g k, 1)` and `diag(g, 1)` lie in the mirabolic
   subgroup (`rankInclusion_lastRow`). So `w` agrees with `W₀` at both. The equality
   `W₀(diag(g, 1) diag(k, 1)) = W₀(diag(g, 1))` is the published
   `zeroCellWhittaker_mul_integral`, applied with `rankInclusion_mem_integralSubgroup`.

Steps 3 and 4 give the first clause of `IsEssentialVector`, and step 5 gives the second.

The same construction appears in the published
`RankinSelberg.HighlyRamified.exists_levelFixed_zeroCell_modelVector` (same module as
`zeroCellWhittaker`). That lemma takes `L = 1` as a hypothesis and fixes the canonical
normalized absolute value. Here `L = 1` is proved for supercuspidal `π` (step 3), and
step 1 allows any `IsJacquetNormalization`.
