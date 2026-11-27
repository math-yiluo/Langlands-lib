# Rational twisted classes of `Res_{L/K} GL_n` with regular elliptic norm at a finite place

Module `Langlands.TraceFormula.GeneralLinearWeilTwistedEllipticRepresentatives`, namespace
`Langlands.TraceFormula`.

The module works with the data of `GeneralLinearSimpleTwistedTraceFormulaStatement` (module
`Langlands.TraceFormula.GeneralLinearSimpleTwistedTraceFormulaStatement`, whose page fixes the
notation). It activates that module's local instances `generalLinearSimpleTwistedTraceIsAffine`
and `generalLinearSimpleTwistedTraceSmooth`. Its notation is as follows.

- `K, L` are number fields with `[Algebra K L] [FiniteDimensional K L]`, `σ : L ≃ₐ[K] L` and
  `l : ℕ`.
- `W = Wₙ = weilGroup K L GLₙ` is `Res_{L/K} GL_n`. `τₙ = unitGaloisAut K L GLₙ σ` is the
  Galois automorphism of `W`, `Θ = adelicAut K τₙ` its action on `W(𝔸_K)` and
  `θ = normOneAut K τₙ` its action on `G¹ = normOneSubgroup K Wₙ`.
  `Γ = rationalNormOneSubgroup K Wₙ` is the group of rational points in `G¹`.
- `N(g) = ((List.range l).map fun k => adelicAut K (τₙ ^ k) g).prod` is the ordered norm
  `g Θ(g) ⋯ Θ^{l-1}(g)` of the statement.
- `cyclicWeilAdelicMap K L n : W(𝔸_K) → AdelicGL L n` (module
  `Langlands.TraceFormula.CyclicAdelicTests`) is by definition the map `Φ` of the statement. It
  composes `AdelicGaloisUnit.weilAdelicEquiv`, `AdelicGroupPoints.map` for
  `GroupScheme.GeneralLinear.baseChangeIso` and `GeneralLinearGroupPoints.adelicHomeomorph`.
- For a finite place `w` of `L`, the `w`-component of the norm is
  `localNormₙ w g = FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n (Φ (N g)))`, an
  element of `FiniteLocalGL L n w = GL_n(L_w)`. This is the quantity that hypothesis 3 of the
  statement requires to be regular elliptic.

## Topological facts

- `totallyDisconnectedSpace_finiteLocalGL L w n`: `GL_n(L_w)` is totally disconnected. It
  embeds continuously and injectively (`Units.val`) in the matrices over `L_w`, a finite product
  of copies of the totally disconnected field `L_w`.
- `apply_eq_one_of_connectedSpace ρ hρ a`: a continuous homomorphism `ρ` from a connected group
  to a totally disconnected group is trivial. The image of `ρ` is preconnected, hence a
  subsingleton, and contains `ρ 1 = 1`.
- `connectedSpace_intrinsicSubgroup G T i hi I e`: the positive real points `A⁺ =
  intrinsicSubgroup F T` of a split torus with injective finite-index character restriction form
  a connected space. `positiveAmbientLogEquiv F G T i hi I e` (module
  `Langlands.Global.AdelicLogSection`) is an isomorphism of topological groups between `A⁺` and
  the multiplicative group of the real vector space `RealCharacterDual F G`. That space is path
  connected.

## The norm

- `adelicNorm_twistedConj e l x q`: for any automorphism `e` of a group scheme `G` over a number
  field `F`, the ordered norm of `x⁻¹ q e(x)` is `x⁻¹ · (q e(q) ⋯ e^{l-1}(q)) · e^l(x)` in
  `G(𝔸_F)`. This is a telescoping product, proved by induction on `l`.
- `unitGaloisAut_pow_eq_one hcyc`: `τₙ ^ l = 1` when `IsCyclicAlgebra σ l`. The map
  `σ ↦ unitGaloisAut K L GLₙ σ` is the homomorphism `unitGaloisAutHom`, and `σ ^ l = 1`
  (`IsCyclicAlgebra.pow_eq_one`).
- `exists_weilLocalHom w`: there is a continuous homomorphism `ψ : W(𝔸_K) →* GL_n(L_w)` with
  `ψ g = FiniteAdelicGL.localProjection L n w (AdelicGL.finite L n (Φ g))`. It is the composite
  of the topological group isomorphism `W(𝔸_K) ≃ GL_n(𝔸_L)` of `generalLinearWeilAdelicTwist`
  (module `Langlands.TraceFormula.GeneralLinearWeilAdelicTwistProof`), whose underlying map is
  `Φ`, with the projections to the finite adeles and to the place `w`.
- `localNorm_positivePointMap_mul T i hi I e w a z`: for `a ∈ A⁺` and `z ∈ W(𝔸_K)`,
  `localNormₙ w (positivePointMap K Wₙ T i a * z) = localNormₙ w z`. The map
  `a ↦ ψ(Θ^k(positivePointMap a))` is a continuous homomorphism from the connected group `A⁺`
  to the totally disconnected group `GL_n(L_w)`, hence trivial. Applying the homomorphism `ψ`
  to the list product then removes every factor `Θ^k(a)`. Neither centrality of the torus nor
  the twist condition is used.
- `isRegularElliptic_localNorm_twistedConj hcyc w x q`: `localNormₙ w (x⁻¹ q Θ(x))` is regular
  elliptic if and only if `localNormₙ w q` is. By `adelicNorm_twistedConj` and
  `unitGaloisAut_pow_eq_one`, `N(x⁻¹ q Θ(x)) = x⁻¹ N(q) x`. Applying `ψ` gives a conjugate
  matrix, which has the same characteristic polynomial (`Matrix.charpoly_units_conj'`).

## Rational coordinates

- `exists_weilAdelicEquiv`: there is an isomorphism of topological groups
  `E : W(𝔸_K) ≃ₜ* AdelicGL L n` with `E g = Φ g`. It satisfies
  `Φ(Θ g) = AdelicGLTransport.adelicEquiv n σ (Φ g)`, the entrywise action of `σ`, and a point
  `g` is rational (`AdelicGroupPoints.rationalSubgroup K Wₙ`) exactly when `Φ g` lies in the
  image of `AdelicGL.rational L n`. This is `generalLinearWeilAdelicTwist K L n`, repackaged.
- `isTwistedConjugate_of_rational_coordinates q q' δ δ' h hq hq' hh`: let `q, q' ∈ Γ` with
  `Φ q = δ` and `Φ q' = δ'` for rational matrices `δ, δ' ∈ GL_n(L)`. If
  `h⁻¹ δ σ(h) = δ'` with `σ` acting entrywise (`entrywiseAut σ n`), then `q` and `q'` are
  `θ`-twisted-conjugate under `Γ`. The witness is `x = E⁻¹(h)`. It is rational, hence lies in
  `G¹` (`rationalSubgroup_le_normOneSubgroup`) and in `Γ`. Its image is
  `E(x⁻¹ q Θ(x)) = h⁻¹ δ σ(h)`, by `AdelicGLTransport.adelicEquiv_rational`.

## Finitely many classes

`exists_twistedClass_representatives_of_isCompact hcyc w Ω hΩ hell` takes a compact set
`Ω ⊆ G¹` and assumes that `localNormₙ w z` is regular elliptic for every `z ∈ Ω`. It gives
`m : ℕ` and `r : Fin m → Γ` with three properties:

1. distinct indices give points that are not `θ`-twisted-conjugate under `Γ`;
2. every `localNormₙ w (r j)` is regular elliptic;
3. every `q ∈ Γ` with `x⁻¹ q θ(x) ∈ Ω` for some `x ∈ G¹` is `θ`-twisted-conjugate under `Γ` to
   some `r j`.

Proof. Let `S ⊆ Γ` be the set of `q` that are `θ`-twisted-conjugate under `G¹` into `Ω`. Every
`q ∈ S` has regular elliptic `localNormₙ w q`, by `isRegularElliptic_localNorm_twistedConj`.
The image `Ωa = Φ(Ω)` is compact in `GL_n(𝔸_L)`. The theorem `twistedEllipticClassFiniteness`
(module `Langlands.TraceFormula.TwistedEllipticClassFinitenessProof`, proving
`TwistedEllipticClassFinitenessStatement`) gives a finite set `R` of rational matrices. Every
`σ`-elliptic `δ ∈ GL_n(L)` with `x'⁻¹ δ σ(x') ∈ Ωa` for some `x' ∈ GL_n(𝔸_L)` is
`σ`-conjugate in `GL_n(L)` to a member of `R`. Take `q ∈ S`, with `x⁻¹ q θ(x) ∈ Ω`.

- The theorem `exists_sigmaElliptic_rational_matrix_of_isRegularElliptic_localNorm` (module
  `Langlands.TraceFormula.GeneralLinearTwistedEllipticCentralizerReduction`) gives a rational
  `δ_q` with `Φ q = δ_q`, and `δ_q` is `σ`-elliptic (`IsSigmaElliptic σ l`).
- With `x' = Φ x`, the twist compatibility of `exists_weilAdelicEquiv` gives
  `x'⁻¹ δ_q σ(x') = Φ(x⁻¹ q Θ(x)) ∈ Ωa`.
- Hence `y_q⁻¹ δ_q σ(y_q) = ρ_q` for some `ρ_q ∈ R` and `y_q ∈ GL_n(L)`.

If `ρ_q = ρ_{q'}`, then `h = y_q y_{q'}⁻¹` satisfies `h⁻¹ δ_q σ(h) = δ_{q'}`. So `q` and `q'` are
twisted-conjugate under `Γ` by `isTwistedConjugate_of_rational_coordinates`.
`exists_twistedClass_representatives` (module `Langlands.TraceFormula.TwistedClassRepresentatives`),
applied to `S` and `q ↦ ρ_q` with values in `R`, gives the representatives. Each `r j` lies in
`S`, so property 2 holds. The theorem uses `set_option maxHeartbeats 800000`.

## Sources

The finiteness is the counterpart, for twisted conjugacy, of Getz–Hahn, *An Introduction to
Automorphic Representations* (2024), registered `getz-hahn-2024-automorphic-representations`,
Lemma 18.2.6 (printed p. 479), which counts the classes meeting a compact set. Here the count
comes from `twistedEllipticClassFiniteness` rather than from that lemma. Arthur–Clozel,
*Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula* (1989), registered
`arthur-clozel-1989-base-change`, Chapter 1, Lemma 1.1 (printed p. 3), relates
`σ`-conjugacy of rational points to their norms. The invariance of the `w`-component of the
norm under `A⁺` is what lets a hypothesis on the support of a function on `W(𝔸_K)` be read on
`G¹`: in the source the test function lives on `A_G \ G(𝔸)`.
