# The simple twisted trace formula for `Res_{L/K} GL_n` with rational σ-elliptic support (proof)

Module `Langlands.TraceFormula.GeneralLinearRationalEllipticTwistedTraceFormulaProof`, namespace
`Langlands.TraceFormula`.

`generalLinearRationalEllipticTwistedTraceFormula :
GeneralLinearRationalEllipticTwistedTraceFormulaStatement.{u}` proves the published statement
with its universe parameter free and no added hypothesis. The statement is in module
`Langlands.TraceFormula.GeneralLinearRationalEllipticTwistedTraceFormulaStatement`, whose page
describes the data, the hypotheses and the conclusion. The module also proves one helper theorem,
`exists_twistedClass_representatives_of_sigmaElliptic`.

The notation follows the statement's page:

- `W = Res_{L/K} GL_n` (local notation `Wₙ`) and `τ = unitGaloisAut K L GLₙ σ` (local notation
  `τₙ`);
- `Θ = adelicAut K τ`, `θ = normOneAut K τ`, `G¹ = normOneSubgroup K Wₙ` and
  `Γ = rationalNormOneSubgroup K Wₙ`;
- `f = f₁ * f₂` (local notation `convₙ`) and `fOne(x) = ∫_{A⁺} f(a x) da`;
- `Φ = cyclicWeilAdelicMap K L n : W(𝔸_K) → GL_n(𝔸_L)`. By definition (module
  `Langlands.TraceFormula.CyclicAdelicTests`) it is the composite `Φ` written out in the
  statement.

## The helper theorem `exists_twistedClass_representatives_of_sigmaElliptic`

Let `Ω ⊆ G¹` be compact and `S ⊆ Γ` a set of rational points such that

- every `q ∈ S` is twisted-conjugate under `G¹` into `Ω`: `x⁻¹ q θ(x) ∈ Ω` for some `x ∈ G¹`;
- every `q ∈ S` has a σ-elliptic coordinate: `Φ(q) = AdelicGL.rational L n δ` for some
  `δ ∈ GL_n(L)` with `IsSigmaElliptic σ l δ`.

Then there are `m : ℕ` and `r : Fin m → Γ` with every `r j ∈ S`, the `r j` pairwise not
twisted-conjugate under `Γ`, and every `q ∈ S` twisted-conjugate under `Γ` to some `r j`.

Proof. `exists_weilAdelicEquiv` (module
`Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives`) gives a topological
group isomorphism `E : W(𝔸_K) ≃ GL_n(𝔸_L)` with underlying map `Φ` that carries `Θ` to the
entrywise action of `σ` (`AdelicGLTransport.adelicEquiv n σ`). So `Ωa = Φ(Ω) ⊆ GL_n(𝔸_L)` is
compact. `twistedEllipticClassFiniteness` (module
`Langlands.TraceFormula.TwistedEllipticClassFinitenessProof`) applied to `Ωa` gives a finite set
`R ⊆ GL_n(L)` such that every σ-elliptic `δ ∈ GL_n(L)` whose `σ`-twisted `GL_n(𝔸_L)`-orbit meets
`Ωa` is twisted-conjugate under `GL_n(L)` to some `ρ ∈ R`: `y⁻¹ δ σ(y) = ρ`. For `q ∈ S` with
coordinate `δ` and `x⁻¹ q θ(x) ∈ Ω`, the point `Φ(x)⁻¹ δ σ(Φ(x)) = Φ(x⁻¹ q θ(x))` lies in `Ωa`,
so `δ` meets `Ωa`; choose `ρ(q) ∈ R` and `y(q)` with `y(q)⁻¹ δ(q) σ(y(q)) = ρ(q)`. If
`ρ(q) = ρ(q')`, then `h = y(q) y(q')⁻¹` satisfies `h⁻¹ δ(q) σ(h) = δ(q')`, and
`isTwistedConjugate_of_rational_coordinates` (same module as `exists_weilAdelicEquiv`) makes `q`
and `q'` twisted-conjugate under `Γ`. So points of `S` with the same value of `ρ` lie in one
twisted class, and as `R` is finite, `exists_twistedClass_representatives` (module
`Langlands.TraceFormula.TwistedClassRepresentatives`) chooses one point of `S` in each of the
finitely many twisted classes of `S`.

The argument is that of `exists_twistedClass_representatives_of_isCompact` in
`Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives`, with the σ-elliptic
coordinates supplied by hypothesis instead of derived from regular ellipticity of the norm at a
finite place of `L`.

## Proof of `generalLinearRationalEllipticTwistedTraceFormula`

1. **Trace class.** `groupSchemeFullL2TraceClass` (module
   `Langlands.TraceFormula.GroupSchemeFullL2TraceClassProof`) is applied to `W` with the given
   `hPD, hG, T, i, hi, I, e, hc` and hypotheses 1 and 2 on `f₁, f₂`. It gives
   `h : Integrable f μG` with `R(f)` trace class on `L²(H \ G, ν)`; this `h` is the
   integrability proof of the conclusion. The convolution `f` is continuous with compact
   support (`Langlands.Analysis.continuous_convolution_compactlySupported` and
   `Langlands.Analysis.hasCompactSupport_convolution_compactlySupported`, module
   `Langlands.TraceFormula.GeneralLinearTensorSimpleTraceFormulaReduction`).
2. **The general formula.** `groupSchemeSimpleTwistedTraceFormula` (module
   `Langlands.TraceFormula.GroupSchemeSimpleTwistedTraceFormula`) is applied to `W`, the torus
   data, `τ`, `isOfFinOrder_unitGaloisAut` and the fixed-torus hypothesis. It gives the subgroup
   and measure preservation `hΘ`, `hΘμ` of the conclusion. It also gives the trace identity for
   any finite family of rational points with closed twisted orbits and compact centralizer
   quotients, pairwise not twisted-conjugate under `Γ`, that covers the contributing rational
   points.
3. **Contributing points meet a compact set.** Let `Ω = normOneFactor '' tsupport f ⊆ G¹`. It is
   the image of the compact `tsupport f` under the continuous norm-one projection
   `normOneFactor` (`continuous_normOneFactor`, module
   `Langlands.Global.AdelicNormOneDecomposition`), so it is compact. Let `q ∈ G¹` and `x ∈ G¹`
   with `fOne(x⁻¹ q θ(x)) ≠ 0`, and put `y = x⁻¹ q θ(x)`. The integral defining `fOne(y)` is
   nonzero, so `f(positivePointMap a * y) ≠ 0` for some `a ∈ A⁺`. That point lies in
   `tsupport f`, and `normOneFactor (positivePointMap a * y) = y` by
   `positiveFactor_mul_normOne`. Hence `y ∈ Ω`: every contributing point is twisted-conjugate
   under `G¹` into `Ω`.
4. **Representatives.** Let `S ⊆ Γ` be the set of contributing rational points. By step 3 and
   hypothesis 3 of the statement, `S` satisfies the two hypotheses of the helper theorem, which
   gives `m` and `r : Fin m → Γ` with every `r j` contributing, the `r j` pairwise not
   twisted-conjugate under `Γ`, and every contributing `q ∈ Γ` twisted-conjugate under `Γ` to
   some `r j`. By hypothesis 3, every `r j` is rationally σ-elliptic. These are the three
   clauses of the conclusion on the representatives.
5. **Closed orbits and compact quotients.** For each `j`, hypothesis 3 gives `δ_j ∈ GL_n(L)` with
   `Φ(r j) = AdelicGL.rational L n δ_j` and `IsSigmaElliptic σ l δ_j`. Two theorems then apply:
   - `generalLinearWeilTwistedClosedOrbit` (module
     `Langlands.TraceFormula.GeneralLinearWeilTwistedClosedOrbitProof`): the twisted orbit of
     `r j` in `G¹` is closed;
   - `generalLinearWeilTwistedCompactQuotient` (module
     `Langlands.TraceFormula.GeneralLinearWeilTwistedCompactQuotientProof`): the quotient
     `(Γ ∩ C_j) \ C_j` of its twisted centralizer is compact.
6. **Conclusion.** Step 2 is applied to `f`, its continuity and compact support, `h`, the trace
   class of step 1, `m`, `r`, the closed orbits and compact quotients of step 5, and the pairwise
   distinctness and covering of step 4. For every choice of Borel structures and compatible
   measures it gives the finite volumes, the integrability of the twisted orbit functions of
   `fOne`, and the trace identity of the conclusion.

The argument needs no case distinction on `n`: for `n = 0` no point is rationally σ-elliptic, so
hypothesis 3 makes `S` empty and the helper theorem returns `m = 0`.

## Implementation notes

The helper theorem is elaborated with the local instances `generalLinearSimpleTwistedTraceIsAffine`
and `generalLinearSimpleTwistedTraceSmooth` of
`Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaStatement`, the ones under which
`exists_weilAdelicEquiv` is stated, and before any definition is made irreducible. The main
theorem activates the statement module's own local instances
(`generalLinearRationalEllipticTwistedTraceIsAffine`, `generalLinearRationalEllipticTwistedTraceSmooth`);
all of these are proofs of propositions, so the two families agree definitionally. As in
`Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaProof`, the main theorem is
elaborated with the following definitions locally irreducible, to keep elaboration from
unfolding the adelic group constructions:

- `normOneSubgroup`, `rationalNormOneSubgroup`, `normOneAut`, `unitGaloisAut` and
  `twistedCentralizer`;
- `AffineWeil.corepresentableBy`, `AffineWeil.tensorFunctor` and the adelic topology
  `AdelicGroupPoints.topologicalSpace`.

The trace identity is closed with `with_reducible exact`, so that unification matches the
statement's terms syntactically. The helper uses `set_option maxHeartbeats 800000`; the main
theorem uses `set_option maxHeartbeats 4000000` and `set_option maxRecDepth 4000`.

## Correspondence with the sources

The statement is the Library's form of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), registered `getz-hahn-2024-automorphic-representations`, Corollary
18.5.1 (printed p. 488), for `G = Res_{L/K} GL_n` and the Galois twist, with the indexing of the
geometric side by rational σ-conjugacy classes with elliptic regular norm of Henniart–Lemaire
(2011), II.6.4 (printed pp. 120–121), and Arthur–Clozel (1989), Chapter 1, Lemma 2.5 (printed
p. 14). The statement's page gives the correspondence of the data, the hypotheses and the
measures.

The route follows Getz–Hahn's derivation. Corollary 18.5.1 is the case `H = {(g, θ(g))}` of
Theorem 18.2.5 (printed p. 479), which is `groupSchemeSimpleTwistedTraceFormula` here (step 2).
The source's hypothesis that every rational element `θ`-conjugate into the support is
`θ`-elliptic and `θ`-semisimple is replaced by hypothesis 3, rational σ-ellipticity of the
contributing classes; for these classes the twisted orbits are closed and the centralizer
quotients compact (step 5). Finiteness of the contributing classes (step 4) is the twisted
counterpart of Lemma 18.2.6 (printed p. 479), obtained from `twistedEllipticClassFiniteness`.
