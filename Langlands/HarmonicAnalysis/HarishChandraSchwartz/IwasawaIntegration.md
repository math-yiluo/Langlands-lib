# The integration formula `dg = δ_P(m)^{-1} du dm dk` (Waldspurger I.1 (2))

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwasawaIntegration`,
namespace `Langlands.HarishChandraSchwartz`. It imports the published modules
`Langlands.Analysis.Local.CompactFactorizationIntegral` (Worker 235: the theorem
`CompactFactorization.lintegral_restrict_lintegral_mul`, integration over a factorization
`G = ι(X) K`) and `Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermBound`
(through which it uses `conjUnipotent` of `ConstantTerm`, and `IsConjModulus` and
`IsConjModulus.lintegral_comp`).

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

I.1 (printed p. 240, PDF p. 6): every closed algebraic subgroup `H` of `G` carries the left
invariant measure with `mes(H ∩ K) = 1`. For `P = M U` semi-standard, `G = P K`, and for
`f ∈ C_c^∞(G)` the first formula of (2) is

`∫_G f(g) dg = ∫_{U × M × K} f(u m k) δ_P(m)^{-1} dk dm du`.

(The second formula of (2), over `U × M × Ū` with the constant `γ(P)`, is not treated
here.)

## Scope: abstract data and explicit hypotheses

`G` is a second-countable topological group with its Borel σ-algebra; `M` and `U` are
subgroups with `M` normalizing `U` (`hMU`) and `U` second countable; `K` is a subgroup.
The measures are an s-finite left invariant measure `μ` on `G` and s-finite left
invariant measures `μ_M` on `M` and `μ_U` on `U`; they are not required to be Haar
measures. The following are explicit hypotheses of both theorems:

- `hK`: `K` is measurable;
- `hfac`: every `g ∈ G` is `m u k` with `m ∈ M`, `u ∈ U`, `k ∈ K` (for Waldspurger's data,
  `G = P K` and `P = M U`);
- `hPK`: `m u ∈ K` if and only if `m ∈ K` and `u ∈ K`, for `m ∈ M`, `u ∈ U` (for
  Waldspurger's data, `P ∩ K = (M ∩ K)(U ∩ K)` together with `M ∩ U = 1`);
- `hMK`, `hUK`: `μ_M(M ∩ K) = 1` and `μ_U(U ∩ K) = 1` (Waldspurger's normalization);
- `F : G → ℝ≥0∞` is measurable (the formula is stated for lower integrals of nonnegative
  measurable functions, which covers `|f|` and the positive and negative parts of `f`);
- for the second theorem, `hν : IsConjModulus hMU μ_U δ`, that is
  `μ_U(m S m^{-1}) = δ(m) μ_U(S)` for `m ∈ M`; for Waldspurger's data `δ = δ_P`.

The measure `dk` is the restriction of `μ` to `K`; with Waldspurger's normalization
`μ(K) = 1` it is the Haar probability measure of `K`, but the formula holds without it.
None of the hypotheses is proved here for Waldspurger's group: the factorizations, the
decomposition of `P ∩ K`, and the realization of the measures and of `δ_P` remain open.

## Definitions

- `leviUnipotentMul (m, u) = m u`: the coordinates of `P = M U`.
- `leviUnipotentShift hMU (m₀, u₀) (m, u) =
  (m₀^{-1} m, ((m₀^{-1} m)^{-1} u₀^{-1} (m₀^{-1} m)) u)`: left translation by `(m₀ u₀)^{-1}`
  in these coordinates.

## Results

- `leviUnipotentMul_shift`: `(m₀ u₀)^{-1} (m u) = leviUnipotentMul (leviUnipotentShift … )`.
- `continuous_leviUnipotentMul`, `continuous_leviUnipotentShift_snd`: continuity.
- `measurePreserving_leviUnipotentShift`: `leviUnipotentShift` preserves `μ_M × μ_U`.
- `lintegral_eq_lintegral_levi_unipotent`: under the hypotheses above,
  `∫⁻_G F dμ = ∫⁻_K ∫⁻_M ∫⁻_U F(m u k) dμ_U dμ_M dμ(k)`.
- `lintegral_eq_lintegral_unipotent_levi` (Waldspurger's form): with also
  `IsConjModulus hMU μ_U δ`,
  `∫⁻_G F dμ = ∫⁻_K ∫⁻_M δ(m)^{-1} ∫⁻_U F(u m k) dμ_U dμ_M dμ(k)`.

## Proof notes

The factorization theorem of `CompactFactorizationIntegral` is applied with parameter space
`X = M × U`, measure `μ_M × μ_U` and coordinate map `ι(m, u) = m u`. Its hypotheses are
`G = ι(X) K` (`hfac`) and, for each `x₀`, a measure-preserving map `σ` of `X` with
`ι(σ x) = ι(x₀)^{-1} ι(x)`: this is `leviUnipotentShift`, a skew product of the left
translation by `m₀^{-1}` on `M` with fiberwise left translations of `U`
(`MeasurePreserving.skew_product`, using the left invariance of `μ_M` and `μ_U`). The
theorem gives `∫_K ∫_X F(ι(x) k) = (μ_M × μ_U)(ι^{-1}(K)) ∫_G F`, and
`ι^{-1}(K) = (M ∩ K) × (U ∩ K)` by `hPK`, of measure one. Tonelli turns the integral over
`X` into the iterated integral. For Waldspurger's order, `m u = (m u m^{-1}) m`, and the
change of variables `u ↦ m u m^{-1}` (`IsConjModulus.lintegral_comp`) gives the factor
`δ(m)^{-1}`.

## Open obligations

For Waldspurger's group: the factorization `G = M U K`, the decomposition
`P ∩ K = (M ∩ K)(U ∩ K)`, the Haar measures and their normalization, the identification of
the modulus with `δ_P`, and the second formula of I.1 (2) (over the open cell
`U M Ū`, with `γ(P)`) are not proved here.
