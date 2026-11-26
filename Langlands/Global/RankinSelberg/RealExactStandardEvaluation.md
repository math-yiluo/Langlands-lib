# Continuous Whittaker evaluation of real character principal series

Let `ds` be a real block list of total rank `r + 1`. The Library's compact Banach completion
`RealStandardCompactBanach.representation ds` of the standard module has the Fréchet space
`DerivativeSmoothVectors` of genuine smooth vectors; `compactFiniteEquiv ds` identifies the
`O(r+1)`-finite standard module `Automorphic.realStandardKFinite (r + 1) ds` with its
compact-finite smooth vectors. `IsWhittakerStandardEvaluation ds a B L` (module
`RealSmoothWhittakerEvaluation`) says that the continuous functional `L` on smooth vectors
satisfies `L(π(g) f) = B f g` for all compact-finite `f` and all `g`, and
`L(π(u) v) = ψ_a(u) L(v)` for all upper unipotent `u` and all smooth `v`.

## Statement

`RealExactStandardEvaluationStatement`: for every list `cs` of real character data, every
`a ∈ ℝˣ` and every linear map `B` from the standard module of `ds = cs.map RealBlock.character`
to functions on `GL_{r+1}(ℝ)` with `IsRealWhittakerIntertwiner r ds a B`, there is a
continuous linear functional `L` on the smooth vectors with
`IsWhittakerStandardEvaluation ds a B L`. `realExactStandardEvaluation` proves it. In
particular every such `B` is the family of translated values of one continuous Whittaker
functional on the smooth completion; `B` itself carries no continuity hypothesis.

## Proof

1. **Derivative coordinates.** `derivativeCLM_compactEval`: the compact values of the derivative
   coordinate of a word `Xs` of a smooth standard vector `f` are the iterated right derivatives
   of the standard function `f` on `O(r+1)`.
2. **Continuous identity evaluation** (`exists_continuous_identityEvaluation`). By
   `realWhittakerFiniteOrder` there are `J` and `D` with `‖B f 1‖ ≤ D R` whenever
   `CompactDifferenceBound J f R`; by `realCompactDerivativeDifferences` such a bound holds
   with `R` a constant times the sum of the norms of the derivative coordinates along the
   finitely many elementary words of length at most `J`. Hence `f ↦ B f 1` on the
   compact-finite vectors is bounded by finitely many derivative-word norms, and the Library's
   Hahn–Banach extension `exists_extension_of_word_bound` (module `SmoothDerivativeTopology`)
   extends it to a continuous functional `L` on all smooth vectors.
3. **Translates** (`translate_identity`). Fix `f` and `g` and let `F(k) = L(π(k g) f) - B f (k g)`
   on the orthogonal group; it is continuous because orbit maps of smooth vectors are
   continuous (`continuous_apply_representation`) and `B f` is smooth. For a polynomial
   function `φ` on `O(r+1)` the weight `compactWeight φ` has finite-dimensional span of left
   translates (`finiteDimensional_compactWeight`, via the separated-variable form of
   `φ(h⁻¹ k)`). The exact compact projection `realExactCompactProjection` gives a
   compact-finite `p` with `p(x) = ∫ φ(k) f(x k g) dk` and `B p x = ∫ φ(k) (B f)(x k g) dk`.
   The compact average of the translates `π(k g) f` in the smooth completion is the smooth
   vector of `p` (`compactSmoothAverage_eq`), and `L` commutes with that average
   (`apply_compactSmoothAverage`, module `SmoothCompactOrbitIntegral`). Evaluating at the
   identity gives `∫ φ(k) F(k) dk = 0` for every polynomial `φ`, for the Haar measure
   `orthogonalHaar r` transported from the compact subgroup. Polynomials are dense, so `F = 0`
   (`OrthogonalFinitePolynomial.eq_zero_of_integral_polynomial_mul_eq_zero`); at `k = 1` this is
   `L(π(g) f) = B f g`.
4. **Covariance** (`isWhittakerStandardEvaluation_of_identity`). For fixed upper unipotent `u`
   both sides of `L(π(u) v) = ψ_a(u) L(v)` are continuous in `v`; on compact-finite vectors the
   identity is the unipotent covariance of `B` at the identity, and these vectors are dense
   (`denseRange_compactFiniteEquiv`).

The restriction to character lists comes only from step 2 (`RealWhittakerFiniteOrder`). This
is the real counterpart of the automatic continuity of Whittaker functionals obtained in the
Library's complex modules `ComplexWhittakerSmoothExtension` and
`ComplexWhittakerTranslateExtension`; there the extension is phrased with compact difference
orders, here with the derivative-word topology of `DerivativeSmoothVectors`. The result is
used in `RealUniformCanonicalRange`.
