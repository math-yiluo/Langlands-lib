# The simple twisted trace formula for `Res_{L/K} GL_n` and a cyclic extension (proof)

Module `Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaProof`, namespace
`Langlands.TraceFormula`.

`generalLinearSimpleTwistedTraceFormula : GeneralLinearSimpleTwistedTraceFormulaStatement.{u}`
proves the published statement with its universe parameter free and no added hypothesis. The
statement is in module `Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaStatement`,
whose page describes the data, the hypotheses and the conclusion. The module activates the
statement module's two local instances (`generalLinearSimpleTwistedTraceIsAffine`,
`generalLinearSimpleTwistedTraceSmooth`).

The notation follows that page and the page of
`Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives`:

- `W = Res_{L/K} GL_n` (local notation `Wₙ`) and `τ = unitGaloisAut K L GLₙ σ`;
- `Θ = adelicAut K τ`, `θ = normOneAut K τ`, `G¹ = normOneSubgroup K Wₙ` and
  `Γ = rationalNormOneSubgroup K Wₙ`;
- `f = f₁ * f₂` (local notation `convₙ`) and `fOne(x) = ∫_{A⁺} f(a x) da`;
- `localNormₙ w g = FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n (Φ (N g)))`, with
  `Φ = cyclicWeilAdelicMap K L n`.

## Proof of `generalLinearSimpleTwistedTraceFormula`

1. **Trace class.** `groupSchemeFullL2TraceClass` (module
   `Langlands.TraceFormula.GroupSchemeFullL2TraceClassProof`) is applied to `W` with the given
   `hPD, hG, T, i, hi, I, e, hc` and the Hilbert–Schmidt and radical-vanishing hypotheses on
   `f₁, f₂`. It gives `h : Integrable f μG` with `R(f)` trace class on `L²([W])`; this `h` is
   the integrability proof of the conclusion. The convolution `f` is continuous with compact
   support (`Langlands.Analysis.continuous_convolution_compactlySupported` and
   `Langlands.Analysis.hasCompactSupport_convolution_compactlySupported`, module
   `Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaReduction`).
2. **The general formula.** `groupSchemeSimpleTwistedTraceFormula` (module
   `Langlands.TraceFormula.GroupSchemeSimpleTwistedTraceFormula`) is applied to `W`, the torus
   data, `τ`, `isOfFinOrder_unitGaloisAut` and the twist condition. It gives the subgroup and
   measure preservation `hΘ`, `hΘμ` of the conclusion. It also gives the trace identity for any
   finite family of rational points with closed twisted orbits and compact centralizer
   quotients, pairwise not twisted-conjugate, that covers the rational classes on whose twisted
   orbits `fOne` is not identically zero.
3. **A compact set of regular elliptic points in `G¹`.** Let
   `Ω = normOneFactor '' tsupport f ⊆ G¹`. It is the image of the compact `tsupport f` under the
   continuous norm-one projection `normOneFactor` (`continuous_normOneFactor`, module
   `Langlands.Global.AdelicNormOneDecomposition`), so it is compact. Each `g ∈ W(𝔸_K)` is
   `positivePointMap (positiveFactor g) * normOneFactor g` (`positivePointMap_mul_normOneFactor`).
   By `localNorm_positivePointMap_mul`, `localNormₙ w (normOneFactor g) = localNormₙ w g`, which
   is regular elliptic for `g ∈ tsupport f` by hypothesis 3 of the statement. So
   `localNormₙ w z` is regular elliptic for every `z ∈ Ω`.
4. **Representatives.** `exists_twistedClass_representatives_of_isCompact` (module
   `Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives`), applied to `Ω`,
   gives `m` and `r : Fin m → Γ` with three properties: distinct indices are not twisted-
   conjugate under `Γ`, every `localNormₙ w (r j)` is regular elliptic, and every rational `q`
   that is twisted-conjugate under `G¹` into `Ω` is twisted-conjugate under `Γ` to some `r j`.
   The first two are the first two clauses of the conclusion. The second is restated in the
   unfolded form of `Φ` used by the statement; `cyclicWeilAdelicMap` is by definition that
   composite.
5. **Closed orbits and compact quotients.** For each `j`,
   `exists_sigmaElliptic_rational_matrix_of_isRegularElliptic_localNorm` (module
   `Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerReduction`) gives a rational
   `δ_j ∈ GL_n(L)` with `Φ (r j) = δ_j` that is `σ`-elliptic. Two theorems then apply:
   - `generalLinearWeilTwistedClosedOrbit` (module
     `Langlands.TraceFormula.GeneralLinearWeilTwistedClosedOrbitProof`): the twisted orbit of
     `r j` in `G¹` is closed;
   - `generalLinearWeilTwistedCompactQuotient` (module
     `Langlands.TraceFormula.GeneralLinearWeilTwistedCompactQuotientProof`): the quotient
     `(Γ ∩ C_j) \ C_j` of its twisted centralizer is compact.

   The theorem `generalLinearTwistedEllipticCentralizer` (module
   `Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerProof`) is proved from these
   two theorems. Its finite volumes and integrable orbit functions are obtained here inside
   `groupSchemeSimpleTwistedTraceFormula`, from the same two facts by
   `twistedCentralizerAnalyticConditions_of_compact_closed`. The compact support set of the
   abstract formula needs the closed orbits and compact quotients themselves.
6. **The covering clause.** Let `q ∈ Γ` and `x ∈ G¹` with `fOne(x⁻¹ q θ(x)) ≠ 0`, and put
   `y = x⁻¹ q θ(x)`. The integral defining `fOne(y)` is nonzero, so
   `f(positivePointMap a * y) ≠ 0` for some `a ∈ A⁺`. That point lies in `tsupport f`, and
   `normOneFactor (positivePointMap a * y) = y` by `positiveFactor_mul_normOne`. Hence `y ∈ Ω`,
   and step 4 gives `j` with `r j` twisted-conjugate to `q` under `Γ`. This is the third clause
   of the conclusion and the covering hypothesis of step 2.
7. **Conclusion.** Step 2 is applied to `f`, its continuity and compact support, `h`, the
   trace class of step 1, `m`, `r`, the closed orbits and compact quotients of step 5, the
   pairwise distinctness of step 4 and the covering clause of step 6. For every choice of Borel
   structures and compatible measures it gives the finite volumes, the integrability of the
   twisted orbit functions of `fOne`, and the trace identity of the conclusion.

The argument needs no case distinction on `n`.

## Implementation notes

As in `Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerProof`, the module makes
the following definitions locally irreducible, to keep elaboration from unfolding the adelic
group constructions:

- `normOneSubgroup`, `rationalNormOneSubgroup`, `normOneAut`, `unitGaloisAut` and
  `twistedCentralizer`;
- `AffineWeil.corepresentableBy`, `AffineWeil.tensorFunctor` and the adelic topology
  `AdelicGroupPoints.topologicalSpace`.

The general formula is proved for an arbitrary group scheme in its own module, so that its
application here is one instantiation. The second clause and the covering clause are closed
with `with_reducible` so that unification matches the statement's terms syntactically. The
theorem uses `set_option maxHeartbeats 4000000` and `set_option maxRecDepth 4000`.

## Correspondence with the sources

The statement is the Library's form of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), registered `getz-hahn-2024-automorphic-representations`, Corollary
18.5.1 (printed p. 488), for `G = Res_{L/K} GL_n` and the Galois twist. It is also the form of
Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
(1989), registered `arthur-clozel-1989-base-change`, Chapter 1, Lemma 2.5 (printed p. 14). The
statement's page gives the correspondence of the data, the hypotheses and the measures.

The route follows the source's derivation. Corollary 18.5.1 is the case `H = {(g, θ(g))}` of
Theorem 18.2.5 (printed p. 479), which is `groupSchemeSimpleTwistedTraceFormula` here (step 2),
with the passage to `A_G \ G(𝔸)` of §2.6 inside it. The source's hypothesis that every rational
element `θ`-conjugate into the support is `θ`-elliptic and `θ`-semisimple is obtained from the
regular ellipticity of the norm at `w`. Through the norm map of Arthur–Clozel, Lemma 1.1
(printed p. 3), rational points with that property are `σ`-elliptic (step 5). For `σ`-elliptic
rational points the twisted orbits are closed and the centralizer quotients compact. Finiteness
of the classes meeting the compact set `Ω` (step 4) is the twisted counterpart of Lemma 18.2.6
(printed p. 479). The analytic identity itself, the trace as the integral of the kernel on the
twisted diagonal and its unfolding over twisted classes, is the Library's abstract simple twisted
trace formula `abstractSimpleTwistedTraceFormula`, used inside step 2.
