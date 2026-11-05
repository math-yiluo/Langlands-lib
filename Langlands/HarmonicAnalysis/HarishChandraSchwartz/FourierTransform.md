# The Fourier transform `f ↦ f̂(ω, P)` and Lemma VII.1.1 of Waldspurger, for an abstract admissible representation

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierTransform`,
namespace `Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzActionConvolution`:
  `schwartzAction_translate_left` (`π(λ(g) f) = π(g) π(f)`) and
  `schwartzAction_translate_right` (`π(ρ(g) f) = π(f) π(g)⁻¹`); through it `Space.translate`
  (`Translations`, `(Space.translate ht g₁ g₂ f)(x) = f(g₂⁻¹ x g₁)`, i.e. `ρ(g₁) λ(g₂) f`),
  and from `SchwartzAction` the operator `schwartzAction hw hA hT f` (Waldspurger's `π(f)`,
  III.7, with `ℓ(π(f) w) = ∫ f(x) ℓ(π(x) w) dμ(x)`, `schwartzAction_eval`),
  `finiteRankSchwartzAction`, `schwartzCharacter` (the trace `θ_π(f)` of `π(f)`),
  `integrable_coefficient`, `continuous_coefficient`, `ext_smoothDual`,
  `HasTemperedCoefficients` and `CompactOpenSubgroup.cofinal`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceCoefficientFamily`:
  `averageProjection` (averaging over a compact open subgroup `K` onto the `K`-fixed vectors),
  `averageProjection_apply`, `fixedFunctional` (extension of a functional on the `K`-fixed
  vectors to a smooth functional) and, through it,
  `Langlands.Representation.Jacquet.BlockCompressionProof`
  (`Jacquet.map_averageMap_of_forall_eq`);
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.L2`: `L2Weights`, `Space.check`
  (`f̌(g) = f(g⁻¹)`, `Space.coe_check`, `check_apply`);
- `Langlands.Representation.Plancherel.CoefficientTensorForm`: `coefficientTensorInvariantForm`
  and `coefficientTensorInvariantForm_inner_tmul`; through it
  `Langlands.Representation.Plancherel.CoefficientTensors` (`CoefficientTensor A = A ⊗ Ã`,
  `coefficientTensorMap` with `coefficientTensorMap A (v ⊗ ℓ) g = ℓ(π(g) v)`,
  `coefficientTensorAction` with `(g, h) · (v ⊗ ℓ) = π(g) v ⊗ π̌(h) ℓ`,
  `coefficientTensorMap_action`), `Langlands.Representation.Unitary.PositiveFormTensor`
  (`InvariantPositiveForm.rescale`, `rescale_inner`), `Langlands.Representation.Unitary.HermitianDual`
  (`InvariantPositiveForm.smoothDualEquiv`, `toSmoothDual`), `dualInvariantForm` from
  `SquareIntegrableSemisimplicity`, and `Langlands.LinearAlgebra.FiniteRankTrace`
  (`finiteRankEnd`, `FiniteRankEnd.trace`, `FiniteRankEnd.rankOne`, `trace_rankOne`);
- `Mathlib.LinearAlgebra.TensorProduct.Basis`: `TensorProduct.equivFinsuppOfBasisLeft`.

The Library names from `CoefficientTensors` and `CoefficientTensorForm` are read in the
namespace `Langlands.Plancherel`. From Mathlib it also uses `TensorProduct.lift`,
`LinearMap.mk₂`, `LinearMap.smulRight`, `Module.Basis.ofVectorSpace`, `Module.finBasis`,
`LinearEquiv.ofInjective`, `MeasureTheory.integral_mul_right_eq_self` and
`MeasureTheory.integral_inv_eq_self`.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus 234.

- VII.1, printed p. 313 (PDF p. 79): "Soient `P = MU` un sous-groupe parabolique semi-standard
  de `G` et `(ω, E) ∈ E₂(M)`. On définit une application `C(G) → L(ω, P)`, `f ↦ f̂(ω, P)` de la
  façon suivante. Posons `π = I_P^G ω`. Notons `f̌` la fonction sur `G` définie par
  `f̌(g) = f(g⁻¹)`. On a `f̌ ∈ C(G)`, on peut donc définir `π(f̌) ∈ End(I_P^G E)`, cf. III.7.
  D'autre part, on a un plongement `L(ω, P) = (I_P^G E) ⊗ (I_P^G E)ˇ ↪ End(I_P^G E)`. (1)
  Comme `f̌` est bi-invariante par un sous-groupe ouvert compact de `G`, `π(f̌)` appartient à
  l'image de cette application et s'identifie donc à un élément de `L(ω, P)`. Alors
  `f̂(ω, P)` est le produit de cet élément par `d(ω)`." Further: "si `f₁, f₂` sont deux
  fonctions sur `X` telles que `f̄₁ f₂ ∈ L¹(X)`, posons `(f₁, f₂)_X = ∫_X f̄₁(x) f₂(x) dx`."
- Lemma VII.1.1, printed p. 314 (PDF p. 80): "Soient `f ∈ C(G)`, `g, h ∈ G` et
  `ψ ∈ L(ω, P)`. On a les égalités (i) `(ρ(g)λ(h)f)^(ω, P) = (π(g) ⊗ π̌(h))(f̂(ω, P))`;
  (ii) `(E_P^G ψ, f)_G = (ψ, f̂(ω, P))`; (iii) `(E_P^G f̂(ω, P))(g) = d(ω) θ_ω^G(λ(g) f̌)`."
  The proof (printed pp. 314–315, PDF pp. 80–81) computes, for `ψ = v ⊗ v̌` and `v'` with
  `⟨v'', v̌⟩ = (v', v'')`, `(E_P^G ψ, f)_G = ∫_G (v', π(g) v) f(g) dg = ∫_G (v, π(g⁻¹) v') f(g) dg
  = (v, π(f̌) v')`, and uses that "la composée de la fonction trace avec l'application (1) est
  l'application déduite par bilinéarité de l'application `v ⊗ v̌ ↦ ⟨v, v̌⟩`"; (iii) follows
  from the case `g = 1` "en remplaçant `f` par `ρ(g) f`, en utilisant (i) et en remarquant que
  `λ(g) f̌ = (ρ(g) f)ˇ`".
- The product on `L(ω, P)`, printed p. 293 (PDF p. 59):
  `(v₁ ⊗ v̌₁, v₂ ⊗ v̌₂) = d(ω)⁻¹ (v₁, v₂)(v̌₁, v̌₂)`, for the products on `I_P^G E` and
  `I_P^G Ě` deduced from a `G`-invariant positive definite hermitian product on `E`
  (antilinear in the first variable).
- The coefficient map, printed p. 288 (PDF p. 54): `E_P^G(v ⊗ v̌)(g) = ⟨π(g) v, v̌⟩`.

In the PDF image of printed p. 314 the displayed integral in the proof of (ii) is
`∫_G conj⟨π(g) v, v̌⟩ f(g) dg`, which agrees with the definition of `(·, ·)_G`; the extracted
text drops the bar.

## Scope: abstract data in place of `I_P^G E` and `d(ω)`

The module does not construct `I_P^G E`, the formal degree `d(ω)` or the induced products.
Throughout, `A : SmoothRep ℂ G` is an arbitrary smooth complex representation (in place of
`π = I_P^G ω`), `CoefficientTensor A = A ⊗ Ã` is its tensor with the smooth dual (in place of
`L(ω, P)`), and `d : ℝ` is an arbitrary real number (in place of `d(ω)`); only (ii) assumes
`0 < d`. The positive invariant form on `A ⊗ Ã` used in (ii) is `d⁻¹` times the tensor form
`coefficientTensorInvariantForm A _ hA b`, `(v₁ ⊗ ℓ₁, v₂ ⊗ ℓ₂) = b(v₁, v₂) (ℓ₁, ℓ₂)`, where `b`
is any positive invariant form on `A` and `(ℓ₁, ℓ₂)` is `dualInvariantForm b`, the form on `Ã`
obtained by transporting `b` along `v ↦ b(v, -)`. That for `A = I_P^G E` this is
Waldspurger's product on `L(ω, P)` (products on `I_P^G E` and `I_P^G Ě` defined by integration
over `P\G`, and `d = d(ω)`) is not proved here.

Analytic data are as in the published modules `L2`, `SchwartzAction` and `Translations`:
`Ξ σ : G → ℝ` are arbitrary weights, `Space Ξ σ` is the space `C(G)` built from them,
`hw : L2Weights μ Ξ σ` (`Ξ > 0`, `σ ≥ 0`, `∫ Ξ² (1 + σ)^(-d₀) dμ < ∞` for some `d₀`),
`hA : IsAdmissible A.representation` (smooth, with finite-dimensional fixed vectors under
every open subgroup) and `hT : HasTemperedCoefficients Ξ σ A.representation` (every coefficient
`g ↦ ℓ(π(g) v)` has tempered growth with respect to `Ξ`, `σ`) make `π(f)` defined.

## Declarations

Section `Embedding`: `G` a topological group (`[Group G] [TopologicalSpace G]`, and
`[IsTopologicalGroup G]` where used), `A : SmoothRep ℂ G`.

- `coefficientTensorToEnd A : CoefficientTensor A →ₗ[ℂ] Module.End ℂ A`, the map VII.1 (1):
  `v ⊗ ℓ ↦ (w ↦ ℓ(w) v)` (`coefficientTensorToEnd_tmul`).
- `equivFinsuppOfBasisLeft_apply_val A ℬ t i w` (any basis `ℬ` of `A` with decidable index
  equality): the `i`-th coefficient `ℓᵢ` in `t = ∑ᵢ ℬᵢ ⊗ ℓᵢ` satisfies
  `ℓᵢ(w) = ℬ.coord i (T_t w)`, with `T_t = coefficientTensorToEnd A t`.
- `coefficientTensorToEnd_injective A`: VII.1 (1) is injective (an embedding).
- `coefficientTensorToEnd_mem_finiteRankEnd A t`, `coefficientTensorFiniteRank A` (the
  same map with values in `finiteRankEnd A`), `coefficientTensorFiniteRank_val`.
- `trace_coefficientTensorFiniteRank A t`: `trace(T_t) = (E t)(1)`, where `E` is
  `coefficientTensorMap A`; this is the statement "la composée de la fonction trace avec
  l'application (1) est l'application `v ⊗ v̌ ↦ ⟨v, v̌⟩`".
- `coefficientTensorToEnd_action A x t`: `T_{(g,h)·t} = π(g) T_t π(h)⁻¹` for `x = (g, h)`.
- `coefficientTensorMap_eq_trace A t g`: `(E t)(g) = trace(T_{(g,1)·t})`.

Section `Form`: as above with `[IsTopologicalGroup G]`, plus
`hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact L ∧ L ≤ K` and
`hA : IsAdmissible A.representation` (the hypotheses of `coefficientTensorInvariantForm`).

- `coefficientTensorInvariantForm_inner_tmul_left A hcof hA b v ℓ t`: for a positive invariant
  form `b` on `A`, `(v ⊗ ℓ, t) = b(v, T_t v')`, where `v' = (b.smoothDualEquiv hcof hA)⁻¹ ℓ`
  is the vector with `ℓ = b(v', -)`.

Section `Operator`: `G` a topological group with `[MeasurableSpace G] [OpensMeasurableSpace G]
[MeasurableMul G]` and `[Nonempty (CompactOpenSubgroup G)]`; `μ` a measure on `G` with
`[μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]` (a Haar measure of a unimodular group);
`Ξ σ : G → ℝ`; `A`, `hw`, `hA`, `hT` as in the scope section. Each declaration below takes
exactly those of these section data that its statement or proof uses (the Lean `omit` lines
drop the unused measurability and invariance instances from `Space.exists_rightInvariant`,
`Space.check_translate` and `integrable_conj_coefficientTensorMap_mul`).

- `Space.exists_rightInvariant f`: every `f ∈ C(G)` is right invariant under a compact open
  subgroup. Uses only `[IsTopologicalGroup G] [Nonempty (CompactOpenSubgroup G)]`.
- `schwartzAction_apply_rho_of_mem A hw hA hT hf hk w`: if `f(g k) = f(g)` for all `k ∈ H`
  (`hf`, `H` any subgroup) and `k ∈ H` (`hk`), then `π(f) π(k) w = π(f) w`; uses the right
  invariance of `μ`.
- `exists_coefficientTensorToEnd_eq_schwartzAction A hw hA hT f`: `π(f)` lies in the image of
  VII.1 (1). The proof writes `π(f) w = π(f) e_K w = ∑ᵢ ℓᵢ(w) π(f) bᵢ` for a compact open `K`
  with `f` right `K`-invariant, `e_K` the averaging projection onto the (finite-dimensional, by
  admissibility) `K`-fixed vectors, `bᵢ` a basis of them and `ℓᵢ` the smooth extensions of the
  dual basis. Waldspurger uses bi-invariance of `f̌`; right invariance of the function suffices.
- `schwartzActionTensor A hw hA hT : Space Ξ σ →ₗ[ℂ] CoefficientTensor A`: the tensor of
  `π(f)`, via `LinearEquiv.ofInjective` on the image of VII.1 (1);
  `coefficientTensorToEnd_schwartzActionTensor` (`T_{schwartzActionTensor f} = π(f)`) and
  `schwartzActionTensor_eq_of_coefficientTensorToEnd_eq` (uniqueness).

With additionally `hΞ : ∀ g, Ξ g⁻¹ = Ξ g` and `hσ : ∀ g, σ g⁻¹ = σ g` (so that
`f̌ ∈ C(G)`, `Space.check hΞ hσ`):

- `coefficientFourierTransform A hw hA hT hΞ hσ d : Space Ξ σ →ₗ[ℂ] CoefficientTensor A`, the
  main definition: `f ↦ d · schwartzActionTensor (f̌)`, Waldspurger's `f̂(ω, P)` with `A` in
  place of `I_P^G E` and `d` in place of `d(ω)`. `coefficientFourierTransform_apply`;
  `coefficientTensorToEnd_coefficientFourierTransform` (`T_{f̂} = d · π(f̌)`).
- `Space.check_translate hΞ hσ ht g h f` (`ht : TranslationWeights Ξ σ`, needed for
  `Space.translate`): `(ρ(g) λ(h) f)ˇ = ρ(h) λ(g) f̌`. Uses only `[IsTopologicalGroup G]`
  besides `hΞ`, `hσ`, `ht`.
- Lemma VII.1.1 (i), `coefficientFourierTransform_translate A hw hA hT hΞ hσ ht d g h f`
  (hypotheses: all `Operator` section data, `hΞ`, `hσ`, `ht`; `d` arbitrary):
  `f̂` of `Space.translate ht g h f = ρ(g) λ(h) f` equals
  `coefficientTensorAction A (g, h) f̂`, i.e. `(π(g) ⊗ π̌(h)) f̂`.
- Lemma VII.1.1 (iii), `coefficientTensorMap_coefficientFourierTransform A hw hA hT hΞ hσ ht d f g`
  (same hypotheses): `(E f̂)(g) = d · schwartzCharacter (Space.translate ht 1 g f̌)`, i.e.
  `d θ_π(λ(g) f̌)`. The case `g = 1`,
  `coefficientTensorMap_coefficientFourierTransform_one A hw hA hT hΞ hσ d f`, needs no `ht`:
  `(E f̂)(1) = d θ_π(f̌)`.
- `integrable_conj_coefficientTensorMap_mul A hw hA hT ψ f`: `g ↦ conj((E ψ)(g)) f(g)` is
  `μ`-integrable; hypotheses `[IsTopologicalGroup G] [MeasurableSpace G]
  [OpensMeasurableSpace G] [Nonempty (CompactOpenSubgroup G)]`, `hw`, `hA`, `hT` (no
  invariance of `μ`).
- `integral_conj_coefficientTensorMap_mul A hw hA hT hΞ hσ b ψ f`, with additionally
  `[MeasurableInv G] [μ.IsInvInvariant]` and a positive invariant form `b` on `A`:
  `∫ conj((E ψ)(g)) f(g) dμ = (ψ, schwartzActionTensor f̌)` for the tensor form
  `coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b` (the computation in the
  proof of (ii), before the factor `d`).
- Lemma VII.1.1 (ii), `integral_conj_coefficientTensorMap_mul_eq_inner A hw hA hT hΞ hσ d hd b ψ f`
  (hypotheses: all `Operator` section data, `hΞ`, `hσ`, `[MeasurableInv G] [μ.IsInvInvariant]`,
  `hd : 0 < d`, a positive invariant form `b` on `A`): `(E ψ, f)_G = (ψ, f̂)`, where
  `(E ψ, f)_G = ∫ conj((E ψ)(g)) f(g) dμ(g)` and the form on `A ⊗ Ã` is
  `(coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).rescale d⁻¹`, i.e.
  `d⁻¹ b(v₁, v₂)(ℓ₁, ℓ₂)`.

## Proof outline

- Injectivity of VII.1 (1): with a basis `ℬ` of `A`, `TensorProduct.equivFinsuppOfBasisLeft ℬ`
  writes `t = ∑ᵢ ℬᵢ ⊗ ℓᵢ` uniquely, and `ℓᵢ = ℬ.coord i ∘ T_t`
  (`equivFinsuppOfBasisLeft_apply_val`); so `T_t = 0` forces all `ℓᵢ = 0`.
- Trace and action identities: on pure tensors `T_{v ⊗ ℓ} = FiniteRankEnd.rankOne ℓ v` has
  trace `ℓ(v) = (E(v ⊗ ℓ))(1)`; extended by additivity (`TensorProduct.inductionOn`).
- (i): by uniqueness of the tensor of an operator, it suffices that
  `π((ρ(g) λ(h) f)ˇ) = π(ρ(h) λ(g) f̌) = π(g) π(f̌) π(h)⁻¹`, from `Space.check_translate` and
  the published `schwartzAction_translate_left/right`.
- (iii): `(E f̂)(g) = trace(T_{(g,1)·f̂}) = d trace(π(g) π(f̌)) = d trace(π(λ(g) f̌))`. This
  uses `coefficientTensorMap_eq_trace` and `schwartzAction_translate_left` directly, rather
  than Waldspurger's reduction to `g = 1` through (i).
- (ii): additivity reduces to `ψ = v ⊗ ℓ`; with `ℓ = b(v', -)`,
  `(v ⊗ ℓ, π(f̌)-tensor) = b(v, π(f̌) v') = ∫ f(x⁻¹) b(v, π(x) v') dμ(x)` by
  `coefficientTensorInvariantForm_inner_tmul_left` and `schwartzAction_eval`; inversion
  invariance of `μ` turns this into `∫ f(g) b(v, π(g)⁻¹ v') dμ(g)`, and
  `b(v, π(g)⁻¹ v') = b(π(g) v, v') = conj(b(v', π(g) v)) = conj(ℓ(π(g) v))` by invariance and
  hermitian symmetry of `b`. The factor `d` of `f̂` cancels the `d⁻¹` of the rescaled form.

## Not covered

- The case `A = I_P^G E` for `(ω, E) ∈ E₂(M)`, the identification of
  `coefficientTensorInvariantForm` (with `b` the induced product and `dualInvariantForm b`)
  with the product on `I_P^G Ě` deduced from `Ě`, and `d = d(ω)` (formal degree, III.1 (3)).
- Lemma VII.1.2 and the rest of VII.
