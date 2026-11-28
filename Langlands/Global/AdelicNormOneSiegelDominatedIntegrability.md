# Integrability of Siegel-dominated functions on the norm-one quotient

Module `Langlands.Global.AdelicNormOneSiegelDominatedIntegrability`, namespace
`Langlands.Global`.

The module states and proves the norm-one form of the Library proposition
`SiegelDominatedIntegrabilityStatement` (module
`Langlands.Global.AdelicWavePacketRapidDecaySiegelReduction`):

```
theorem normOneSiegelDecayIntegrability : NormOneSiegelDecayIntegrabilityStatement
```

Lean reports the axioms `propext`, `Classical.choice` and `Quot.sound` for it.

| Declaration | Kind | Content |
| --- | --- | --- |
| `NormOneSiegelDecayIntegrabilityStatement` | proposition | integrability on `G(F) \ G(𝔸)^1` of functions dominated on the norm-one points of a Siegel set |
| `continuous_adelicLogHeight` | theorem | `σ(x) = 1 + log max(1, ‖x‖_ρ)` is continuous |
| `exists_adelicLogHeight_mul_le_add` | theorem | `σ(x y) ≤ σ(x) + σ(y) + L` for a constant `L ≥ 0` |
| `adelicLogHeight_mul_le_of_le` | theorem | `σ(x) ≤ S₀` implies `σ(x y) ≤ (S₀ + L + 1) σ(y)` |
| `normOneSiegelDecayIntegrability` | theorem | proof of the proposition |

## The statement

`NormOneSiegelDecayIntegrabilityStatement` keeps the number-field universe `Type` and the
instance hypotheses of `SiegelDominatedIntegrabilityStatement`. Let `F` be a number field, `G`
connected reductive and `rho : MatrixRepresentation G (Fin N)` closed (`IsClosedSubgroup rho`).
Then there exist an algebraic Siegel setup `(T, i, ν, T₀, j)` (`IsSiegelAlgebraicSetup`), compact
factors `C`, a threshold `t`, a compact set `Ω ⊆ G(𝔸)` and `d : ℕ` with the following property.
Let `f : G(𝔸) → [0, ∞]` be measurable and left invariant under `G(F)`
(`rationalSubgroup F G`), and suppose

`f(x) ≤ siegelModulus(a) / adelicLogHeight(x)^d`

for every `x` with `IsSiegelPoint F G T i ν T₀ j C t Ω a x` and `x ∈ G(𝔸)^1`
(`normOneSubgroup F G`). Then

`∫⁻ y, f(y.out) ∂(normOneRationalQuotientHaarMeasure F G) < ∞`,

where `y` runs over `G(F) \ G(𝔸)^1` (`NormOneRationalQuotient F G`) and `y.out ∈ G(𝔸)^1` is its
chosen representative, viewed in `G(𝔸)`.

The notions are those of `AdelicWavePacketRapidDecaySiegelReduction.md`: `siegelModulus(a)` is
the modulus `δ_{P₀}(a)` of the minimal parabolic of the setup at the torus coordinate `a`, and
`adelicLogHeight` is Delorme's `σ(x) = 1 + log max(1, ‖x‖_ρ)`. The domination is asked only at
norm-one Siegel points, which is all that a function on `G(F) \ G(𝔸)^1` can be tested on.

*Provenance (derived).* Lapid, *On the Harish-Chandra Schwartz space of G(F)\G(A)* (registered
as `lapid-2013-harish-chandra-schwartz-space-automorphic`), §2, (2), (3) and (5), quoted by
Delorme, *On the spectral theorem of Langlands* (2023, `delorme-2023-spectral-theorem-langlands`)
as (2.5), give the integrability over `[G]` of such dominated functions; the Library proves
this as `siegelDominatedIntegrability`. The norm-one form follows because
`G(F) \ G(𝔸) = A_G × G(F) \ G(𝔸)^1` with product measure (Lapid 2011, §2, p. 311, as transported
by `PositiveRealTorus.measurePreserving_rationalQuotientDecomposition`). Neither source states
the proposition in this form.

## The height lemmas

Write `σ = adelicLogHeight F G rho` and `‖·‖_ρ = RepresentationGrowth.adelicSourceNorm`.

- `continuous_adelicLogHeight`: `σ = 1 + log ∘ max 1 ∘ ‖·‖_ρ`, with `‖·‖_ρ` continuous
  (`continuous_adelicSourceNorm`) and `max 1 ‖·‖_ρ ≥ 1 > 0`.
- `exists_adelicLogHeight_mul_le_add`: if `N = 0`, the matrices lie in the trivial group
  `GL_0(𝔸)`, so `σ(x y) = σ(y)` and `L = 0` works, since `σ(x) ≥ 1`. If `N > 0`, put
  `c = N^{Σ_v m_v} ≥ 1`, so that `adelicHeight = c ‖·‖_ρ`
  (`adelicHeight_eq_scalar_mul_sourceNorm`). Submultiplicativity of the height
  (`adelicHeight_mul_le`) gives `‖x y‖_ρ ≤ c ‖x‖_ρ ‖y‖_ρ`, hence
  `max(1, ‖x y‖_ρ) ≤ c max(1, ‖x‖_ρ) max(1, ‖y‖_ρ)`. Taking logarithms gives
  `σ(x y) ≤ σ(x) + σ(y) - 1 + log c`, so `L = log c` works.
- `adelicLogHeight_mul_le_of_le`: from `σ(x y) ≤ σ(x) + σ(y) + L`, `σ(x) ≤ S₀` and `σ(y) ≥ 1`
  one gets `σ(x y) ≤ S₀ + L + σ(y) ≤ (S₀ + L + 1) σ(y)`.

## Proof of `normOneSiegelDecayIntegrability`

1. **Data.** `siegelDominatedIntegrability` applied to `F, G, rho` gives a setup
   `(T, i, ν, T₀, j)`, compact factors `C`, a threshold `t`, a compact `Ω`, `d` and the
   integrability over `[G] = G(F) \ G(𝔸)` of functions dominated at all Siegel points for these
   data. The proof keeps `(T, i, ν, T₀, j)`, `C`, `t` and `d`, and replaces `Ω` by its image
   `π(Ω)` under the norm-one projection `π` defined in step 2; `π(Ω)` is compact.
2. **The central decomposition.** Take the canonical split component
   `i' : T' → G` (`RestrictionSplitCentre.canonicalComponent`), a splitting
   `e : T' ≅ G_m^I` (from `IsSplitTorus`), the injectivity of character restriction
   (`canonical_characterRestrict_injective`, using the proved `centralSplitTorusCharacter`), its
   finite index (`canonical_finiteIndex`) and centrality. Write `A = intrinsicSubgroup F T'`,
   `pp : A → G(𝔸)` for `positivePointMap`, `pf : G(𝔸) → A` for `positiveFactor` and
   `π : G(𝔸) → G(𝔸)^1` for `normOneProjection`. Then `x = pp(pf x) · π(x)`
   (`positivePointMap_mul_normOneFactor`), `π` is a continuous homomorphism equal to the
   identity on `G(𝔸)^1` and trivial on `pp(A)`, and `pf` is trivial on `G(𝔸)^1`. The image
   `pp(A)` is the subgroup `A_G` of the Siegel points
   (`canonicalSubgroup_eq_imageSubgroup`).
3. **The auxiliary function.** Let `S₀ = σ(1) + 1`, let `U = {a ∈ A : σ(pp a) < S₀}` (an open
   neighbourhood of `1`), let `L` be the constant of `exists_adelicLogHeight_mul_le_add`,
   `K₀ = S₀ + L + 1` and `c = K₀^{-d}`. Put

   `F₁(x) = c 1_U(pf x) f(π x)`.

   It is measurable. It is left `G(F)`-invariant: for `q ∈ G(F) ⊆ G(𝔸)^1`,
   `pf(q x) = pf(x)` and `π(q x) = q π(x)`, and `f` is left invariant.
4. **Domination.** Let `x = z · y · w` be a Siegel point for the data of step 1, with
   `z ∈ A_G`, `y = n m a k` and `w ∈ Ω`. The middle factor `y` lies in `G(𝔸)^1`
   (`IsSiegelAlgebraicSetup.productSet_subset_normOne` with `mem_productSet_iff`), and `z ∈ pp(A)`.
   Hence `π(x) = y · π(w)`, which is a Siegel point for the data with `π(Ω)`, with central factor
   `1` and the same torus coordinate `a`, and which lies in `G(𝔸)^1`. The hypothesis on `f`
   gives `f(π x) ≤ δ(a) / σ(π x)^d`. If `pf x ∉ U`, then `F₁(x) = 0`. If `pf x ∈ U`, then
   `σ(pp(pf x)) < S₀`, and `adelicLogHeight_mul_le_of_le` applied to
   `x = pp(pf x) · π(x)` gives `σ(x) ≤ K₀ σ(π x)`. Since `δ(a) ≥ 0` and `σ ≥ 1`,

   `F₁(x) ≤ c δ(a) / σ(π x)^d = δ(a) / (K₀ σ(π x))^d ≤ δ(a) / σ(x)^d`.

   So `siegelDominatedIntegrability` gives `∫⁻_{[G]} F₁(y.out) < ∞`.
5. **Integrating out the centre.** The map
   `Q = rationalQuotientDecomposition : A × G(F) \ G(𝔸)^1 → G(F) \ G(𝔸)`,
   `(a, [n]) ↦ [pp(a) n]`, carries `μ_A × μ₁` to the quotient Haar measure of `[G]`
   (`measurePreserving_rationalQuotientDecomposition`), where
   `μ_A = normalizedPositiveHaarMeasure` and `μ₁ = normOneRationalQuotientHaarMeasure`. The
   function `y ↦ F₁(y.out)` is measurable (`LeftCosetSpace.measurable_comp_out`). By left
   invariance, `F₁(Q(a, q).out) = F₁(pp(a) · q.out) = c 1_U(a) f(q.out)`. By Tonelli
   (`lintegral_prod_mul`) and `lintegral_indicator_const`,

   `∫⁻_{[G]} F₁(y.out) = c μ_A(U) ∫⁻ f(q.out) dμ₁(q)`.

6. **Conclusion.** `μ_A` is a Haar measure (`normalizedPositiveHaarMeasure_isHaarMeasure`), so
   the nonempty open set `U` has `μ_A(U) ≠ 0`; also `c > 0`. A product in `[0, ∞]` with a
   nonzero first factor is finite only if the second factor is finite
   (`ENNReal.mul_lt_top_iff`), so `∫⁻ f(q.out) dμ₁(q) < ∞`.

The finiteness of `μ₁` (`isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive`)
and the σ-finiteness of `μ_A` (`normalizedPositiveHaarMeasure_sigmaFinite`) supply the
instances for Tonelli's theorem.
