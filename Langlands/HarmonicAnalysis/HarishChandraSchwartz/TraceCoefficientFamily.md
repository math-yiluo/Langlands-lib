# Waldspurger's family `ϕ_H = ϕ ψ_H` in the proof of Proposition III.7.1

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TraceCoefficientFamily`,
namespace `Langlands.HarishChandraSchwartz`. It imports `SchwartzActionFamily`
(`IdempotentFamily`, `IdempotentFamily.operator`, `IdempotentFamily.operator_apply_of_mem`,
`Space.normalizedIndicator`, `Space.normalizedIndicator_apply`, `rho_mem_fixedVectors_conj`,
and through it `schwartzAction_eval`, `HasTemperedCoefficients`, `ConvolutionWeights`,
`convolution_apply`, `TranslationWeights`, `CompactOpenSubgroup.conj`, `mem_conjSubgroup`) and
`CoefficientCutoff` (`HasRapidlyDecreasingCoefficientsOn`,
`TranslationWeights.mul_mem_schwartzSubmodule`, and through it `SmoothRep`,
`CoefficientTensor`, `coefficientTensorMap`, `coefficientTensorMap_tmul` of
`Langlands.Representation.Plancherel.CoefficientTensors`). From the representation-theory part
of the Library it imports `Langlands.Representation.Jacquet.CanonicalLiftDefinitions`
(`Jacquet.compressedAction`), `Langlands.Representation.Jacquet.StablePairingProof`
(`Jacquet.averageMap_apply_of_mem`, `Jacquet.averageMap_averageMap_of_le`,
`Jacquet.conjOpenSubgroup`, `Jacquet.mem_conjOpenSubgroup`, `Jacquet.averageMap_conj`, and
through it `Jacquet.map_averageMap_of_forall_eq`) and
`Langlands.Representation.Character.TransportProof` (`Character.integratedAction_right_input`,
and through it `Langlands.finiteRankEnd`, `FiniteRankEnd.trace`,
`FiniteRankEnd.ofFactorization`, `FiniteRankEnd.trace_eq_of_factorization` of
`Langlands.LinearAlgebra.FiniteRankTrace`). It also uses `Compact.averageMap`,
`Compact.averageMap_mem_fixedVectors`, `Compact.averageMap_id`,
`matrixCoefficient_isLocallyConstant`, `Hecke.heckeAction`, `Hecke.heckeAction_apply`,
`Hecke.integratedAction_dual`, `Hecke.fixedProjection`,
`Hecke.heckeAction_normalizedIndicator_of_fixed`,
`Hecke.HeckeAlgebra.normalizedIndicator_mem_biInvariant` and
`Hecke.TestFunction.rightTranslate_apply`, all reached through these imports.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082. Printed page numbers; the PDF page is the printed page minus
234.

- Proof of Proposition III.7.1 (printed p. 274, PDF p. 40), opening: "Fixons `(ω, E) ∈ O`.
  Pour tout sous-groupe ouvert compact `H` de `G`, notons `ε_H` et `ψ_H` les fonctions sur `G`
  définies par `ε_H(g) = 0, si g ∉ H, (mes H)⁻¹, si g ∈ H`,
  `ψ_H(g) = trace[ω̌(ε_H)ω̌(g)ω̌(ε_H)]`. Soit `ϕ ∈ C_c(G/G¹)`. Posons `ϕ_H = ϕψ_H`. Comme
  `ψ_H ∈ A(ω̌)`, on a `ϕ_H ∈ C(G)`. On vérifie facilement les propriétés: (1) si `g ∈ G`,
  `ρ(g)λ(g)ϕ_H = ϕ_{gHg⁻¹}` ; (2) si `H'` est un sous-groupe ouvert compact de `G` contenant
  `H`, `ϕ_H ∗ ε_{H'} = ϕ_{H'}`."
- Same page, after the definition of `π[ϕ]`: "Supposons `π` irréductible et calculons `π[ϕ]`.
  Soient `v ∈ V`, `v̌ ∈ V̌` et `H` un sous-groupe ouvert compact de `G` fixant `v` et `v̌`. On a
  les égalités `⟨π[ϕ]v, v̌⟩ = ∫_G ϕ(g)ψ_H(g)⟨π(g)v, v̌⟩dg = ∫_{G¹\G} ϕ(g)f(g)dg`, [...]".
  This module proves the first of these two equalities.
- III.7, second paragraph (printed p. 273, PDF p. 39): for `(ω, E)` admissible square
  integrable, `f ∈ A(ω)` and `ϕ ∈ C_c(G/G¹)`, "la fonction produit `fϕ` appartient à `C(G)`"
  (formalized in `CoefficientCutoff`, under the hypothesis `hD` described there).
- I.6 (printed p. 249, PDF p. 15): `ρ(g)f(x) = f(xg)`, `λ(g)f(x) = f(g⁻¹x)`, and `A(π)` is
  the span of the coefficients of `π`.

The source gives no argument for `ψ_H ∈ A(ω̌)` or for (1) and (2) ("On vérifie facilement").
The Lean proofs below supply them. The statements `averageMap_congr`,
`averageProjection_of_mem`, `averageProjection_rho_of_mem`, `traceCoefficient_eq_sum`,
`integrable_testFunction_mul_coefficient`, `heckeAction_normalizedIndicator_eq_averageMap`,
`heckeAction_normalizedIndicator_eq_subtype_comp`, `fixedProjection_eq_averageProjection` and
`heckeAction_mul_rho_mul_heckeAction_mem` are derived auxiliary facts, not displayed in the
source. `traceCoefficient_conj` and `integral_normalizedIndicator_mul_traceCoefficient` are the
facts about `ψ_H` behind (1) and (2).

## Scope: abstract data and explicit hypotheses

`G` is a topological group (`[IsTopologicalGroup G]`) and `V` a complex vector space with a
representation `ρ : Representation ℂ G V`; `ρ` plays the role of Waldspurger's `ω̌`. Waldspurger's
`ω` is irreducible and square integrable; here `ρ` is any smooth or admissible representation,
and the only analytic input on it is the hypothesis `hD` below. The weights `Ξ, σ : G → ℝ`
and the measure `μ` are arbitrary. Nothing is proved here about Waldspurger's own `Ξ`, `σ`,
`G¹` or Haar measure.

- `IsAdmissible ρ` is the Library's notion: `ρ` is smooth and `V^K` is finite-dimensional for
  every open subgroup `K`.
- `mes H` is `μ.real H` and `ε_H` is the Library's
  `Hecke.HeckeAlgebra.normalizedIndicator μ H.1 H.2` (as an element of `C(G)`:
  `Space.normalizedIndicator`); `ω̌(ε_H)` is the Hecke action `Hecke.heckeAction`.
- `G¹` is replaced by a subgroup `N` with `[N.Normal]` and `hN : IsOpen (N : Set G)`, as in
  `CoefficientCutoff`. The family `traceFamily` additionally assumes
  `hconj : ∀ g x : G, ((g⁻¹ * x * g : G) : G ⧸ N) = (x : G ⧸ N)` (every commutator lies in
  `N`, i.e. `G ⧸ N` is abelian) and `hHN : ∀ H : CompactOpenSubgroup G, H.toSubgroup ≤ N`.
  For Waldspurger's `G¹` (I.1, the common kernel of the `|χ|_F`, `χ` rational) both hold,
  since `G/G¹` embeds in a product of copies of `ℝ_{>0}` and the image of a compact subgroup
  there is trivial; this is not proved here.
- `ϕ ∈ C_c(G/G¹)` is `φ : G ⧸ N → ℂ` with `hφ : HasCompactSupport φ`; `ϕ_H(g)` is
  `traceCoefficient ρ hρ H g * φ g`, where `φ g` is `φ` at the coset of `g`.
- The conclusion of Corollary III.1.2 for the coefficients of `ρ` is the hypothesis
  `hD : HasRapidlyDecreasingCoefficientsOn Ξ σ N A.representation` of `CoefficientCutoff`.
  In the source it holds because `ω̌` is admissible and square integrable; this is not
  proved here.

The hypotheses of each result are:

- `averageMap_congr`: `hρ : IsSmooth ρ`, open subgroups with `h : K₁ = K₂` and compactness
  proofs `h₁`, `h₂`.
- `averageProjection`, `averageProjection_apply`: `hρ : IsSmooth ρ` and a compact open
  subgroup `H`; `averageProjection_of_mem` also `w ∈ V^H`; `averageProjection_rho_of_mem`
  also `k ∈ H`.
- `traceCoefficient`: `hρ : IsSmooth ρ`, `H`, `g : G`. `traceCoefficient_eq_sum`:
  additionally `[FiniteDimensional ℂ (fixedVectors ρ H.toSubgroup)]` and a basis `b` of `V^H`
  indexed by a finite type with decidable equality.
- `fixedFunctional`: `hρ : IsSmooth ρ`, `H`, a linear form `L` on `V^H`.
- `traceCoefficient_conj`: `hρ : IsAdmissible ρ`, `H`, `g x : G`.
- `traceCoefficient_mem_range`: `A : SmoothRep ℂ G` (a published smooth representation, carrier
  in universe `v`, `ℂ` in universe `0`), `hA : IsAdmissible A.representation`, `H`.
- `integrable_testFunction_mul_coefficient`: `[MeasurableSpace G]`,
  `[OpensMeasurableSpace G]`, a measure `μ` with `[IsFiniteMeasureOnCompacts μ]`,
  `hρ : IsSmooth ρ`, a test function `f : SchwartzBruhat G`, `L : Module.Dual ℂ V`, `v : V`.
- `heckeAction_normalizedIndicator_eq_averageMap`,
  `heckeAction_normalizedIndicator_eq_subtype_comp`, `fixedProjection_eq_averageProjection`:
  `[MeasurableSpace G]`, `[BorelSpace G]`, `[μ.IsHaarMeasure]`, `[μ.IsMulRightInvariant]`,
  `hρ : IsSmooth ρ`, `H`.
- `heckeAction_mul_rho_mul_heckeAction_mem`: the same instances, `hρ : IsAdmissible ρ`, `H`,
  `g`. `finiteRankTrace_eq_traceCoefficient`: the same, and `T : finiteRankEnd V` with
  `hT : T.val = ρ(ε_H) * ρ g * ρ(ε_H)` (Hecke actions).
  `integral_normalizedIndicator_mul_traceCoefficient`: the same instances,
  `hρ : IsAdmissible ρ`, compact open subgroups `H`, `H'` with `hHH' : H ≤ H'`, `x : G`.
- `traceCutoff`, `traceCutoff_apply`: `[Nonempty (CompactOpenSubgroup G)]`, `A`, `hA`, `N`
  normal, `ht : TranslationWeights Ξ σ`, `hN`, `hD`, `hφ`, `H`.
- `traceFamily`, `traceFamily_toFun`: in addition `[MeasurableSpace G]`, `[BorelSpace G]`,
  `[SecondCountableTopology G]`, `μ` with `[μ.IsHaarMeasure]`, `[SFinite μ]`,
  `[μ.IsMulRightInvariant]`, a subgroup `K` with `[CompactSpace K]`,
  `hc : ConvolutionWeights μ K Ξ σ`, `hconj` and `hHN`.
- `traceFamily_operator_eval`: in addition `hw : L2Weights μ Ξ σ`, a representation
  `π : Representation ℂ G W` with `hπ : IsAdmissible π` and
  `hT : HasTemperedCoefficients Ξ σ π`, a compact open subgroup `H` with
  `hv : v ∈ fixedVectors π H.toSubgroup`, and a smooth functional `ℓ : SmoothDual π`.

Waldspurger's `G` is unimodular, so his Haar measure is also right invariant; here
`[μ.IsMulRightInvariant]` is a hypothesis.

## Definitions

- `averageProjection ρ hρ H : V →ₗ[ℂ] V^H` is the averaging projection `e_H`: the Library's
  `Compact.averageMap` (the mean over the finite `H`-orbit of a vector) with codomain `V^H`.
- `traceCoefficient ρ hρ H g` is `ψ_H(g)`, defined as `LinearMap.trace` of
  `Jacquet.compressedAction ρ hρ H.1 H.2 g = e_H ∘ ρ(g)` on `V^H`. When `V^H` is
  infinite-dimensional, `LinearMap.trace` is `0`; all results about `ψ_H` beyond the
  definition assume admissibility. `finiteRankTrace_eq_traceCoefficient` shows that it is
  Waldspurger's `trace[ρ(ε_H)ρ(g)ρ(ε_H)]`.
- `fixedFunctional ρ hρ H L : SmoothDual ρ` is `L ∘ e_H`, smooth because it is
  `H`-invariant.
- `traceCutoff A hA ht hN hD hφ H : Space Ξ σ` is `ϕ_H = ψ_H ϕ`, the function
  `g ↦ traceCoefficient A.representation hA.1 H g * φ g`, as an element of `C(G)`.
- `traceFamily A hA hc ht hN hD hconj hHN hφ : IdempotentFamily hc ht` is the family
  `H ↦ ϕ_H` with Waldspurger's properties (1) and (2) (the fields of `IdempotentFamily` in
  `SchwartzActionFamily`). Its operator `IdempotentFamily.operator` is Waldspurger's `π[ϕ]`.

## Results

- `averageMap_congr`: `Compact.averageMap` depends only on the subgroup, not on the
  compactness proof or on the way the subgroup is written.
- `averageProjection_of_mem`: `e_H w = w` for `w ∈ V^H`; `averageProjection_rho_of_mem`:
  `e_H(ρ(k) v) = e_H v` for `k ∈ H`.
- `traceCoefficient_eq_sum`: `ψ_H(g) = Σ_i b_i^*(e_H ρ(g) b_i)`.
- `traceCoefficient_conj`: `ψ_{gHg⁻¹}(x) = ψ_H(g⁻¹ x g)`, with `gHg⁻¹ = H.conj g`.
- `traceCoefficient_mem_range`: `ψ_H ∈ A(ρ)`, i.e. `ψ_H` is `coefficientTensorMap A t` for
  some tensor `t`.
- `integrable_testFunction_mul_coefficient`: `k ↦ f(k) L(ρ(k) v)` is integrable.
- `heckeAction_normalizedIndicator_eq_averageMap`: `ρ(ε_H) v = e_H v` (Hecke action of the
  normalized indicator equals the orbit mean); `heckeAction_normalizedIndicator_eq_subtype_comp`
  states it as an equality of endomorphisms, and `fixedProjection_eq_averageProjection` says
  that the Library's `Hecke.fixedProjection μ ρ hρ H.1 H.2` equals `averageProjection ρ hρ H`.
- `heckeAction_mul_rho_mul_heckeAction_mem`: `ρ(ε_H)ρ(g)ρ(ε_H)` has finite rank.
- `finiteRankTrace_eq_traceCoefficient`: for any `T : finiteRankEnd V` whose underlying
  endomorphism is `ρ(ε_H)ρ(g)ρ(ε_H)`, `FiniteRankEnd.trace T = ψ_H(g)`; this is Waldspurger's
  definition of `ψ_H`.
- `integral_normalizedIndicator_mul_traceCoefficient`: for `H ≤ H'`,
  `∫_G ε_{H'}(k) ψ_H(x k) dμ(k) = ψ_{H'}(x)`, i.e.
  `(mes H')⁻¹ ∫_{H'} ψ_H(xk) dk = ψ_{H'}(x)`.
- `traceCutoff_apply`: `ϕ_H(g) = ψ_H(g) φ(gN)`. That `ϕ_H ∈ C(G)` is the content of the
  definition `traceCutoff` ("Comme `ψ_H ∈ A(ω̌)`, on a `ϕ_H ∈ C(G)`").
- `traceFamily` carries the proofs of (1) `Space.translate ht g g ϕ_H = ϕ_{H.conj g}`
  (`ρ(g)λ(g)ϕ_H = ϕ_{gHg⁻¹}`) and (2) `Space.convolution hc ϕ_H ε_{H'} = ϕ_{H'}` for `H ≤ H'`;
  `traceFamily_toFun`: its underlying map is `traceCutoff`.
- `traceFamily_operator_eval`: for `H` fixing `v` and every smooth functional `ℓ`,
  `ℓ(π[ϕ] v) = ∫_G ψ_H(g) φ(gN) ℓ(π(g) v) dμ(g)`, the first displayed equality of the source.
  It is proved for every admissible `π` with `hT` and every `H` fixing `v`; irreducibility of
  `π` and `H`-invariance of `ℓ` are not needed.

## Proof notes

- `traceCoefficient_eq_sum`: `LinearMap.trace_eq_matrix_trace` in the basis `b`.
- `traceCoefficient_conj`: let `E = ρ(g) : V^H → V^{gHg⁻¹}` and
  `F = (e_H ρ(g⁻¹xg)) ∘ ρ(g⁻¹) : V^{gHg⁻¹} → V^H`. Then `F ∘ E` is the compressed action of
  `g⁻¹xg` on `V^H`, and `E ∘ F` is the compressed action of `x` on `V^{gHg⁻¹}` by
  `Jacquet.averageMap_conj` (`e_{gHg⁻¹} ρ(g) = ρ(g) e_H`, with `H.conj g` identified with
  `Jacquet.conjOpenSubgroup g H` and `averageMap_congr`). `LinearMap.trace_comp_comm'` gives
  `trace(F ∘ E) = trace(E ∘ F)`.
- `traceCoefficient_mem_range`: for a basis `b` of `V^H`, the tensor
  `t = Σ_i b_i ⊗ fixedFunctional (b_i^*)` has coefficient
  `g ↦ Σ_i b_i^*(e_H ρ(g) b_i) = ψ_H(g)` (`coefficientTensorMap_tmul`,
  `traceCoefficient_eq_sum`).
- `integrable_testFunction_mul_coefficient`: the coefficient is locally constant
  (`matrixCoefficient_isLocallyConstant`), hence continuous, and the product with `f` is
  continuous with compact support.
- `heckeAction_normalizedIndicator_eq_averageMap`: by right invariance of `μ`
  (`Character.integratedAction_right_input`) and the bi-invariance of `ε_H`,
  `ρ(ε_H) ρ(k) v = ρ(ε_H) v` for `k ∈ H`, so `Jacquet.map_averageMap_of_forall_eq` gives
  `ρ(ε_H)(e_H v) = ρ(ε_H) v`; and `ρ(ε_H)` fixes the `H`-fixed vector `e_H v`
  (`Hecke.heckeAction_normalizedIndicator_of_fixed`).
- `heckeAction_mul_rho_mul_heckeAction_mem` and `finiteRankTrace_eq_traceCoefficient`:
  `ρ(ε_H)ρ(g)ρ(ε_H)` factors as `V → V^H → V` through `e_H` and
  `w ↦ e_H ρ(g) w` (`FiniteRankEnd.ofFactorization`); `FiniteRankEnd.trace_eq_of_factorization`
  turns its trace into the trace on `V^H` of `e_H ρ(g) e_H = e_H ρ(g)`
  (`averageProjection_of_mem`).
- `integral_normalizedIndicator_mul_traceCoefficient`: expand `ψ_H(xk)` in a basis `b` of
  `V^H` as `Σ_i L_i(ρ(k) b_i)` with `L_i = b_i^* ∘ e_H ∘ ρ(x)`, integrate term by term
  (`integral_finsetSum`, `integrable_testFunction_mul_coefficient`), and use
  `Hecke.integratedAction_dual` and `heckeAction_normalizedIndicator_eq_averageMap` to get
  `Σ_i b_i^*(e_H ρ(x) e_{H'} b_i) = trace(F ∘ E)` with `E = e_{H'}|_{V^H} : V^H → V^{H'}` and
  `F = e_H ρ(x)|_{V^{H'}}`. Then `trace(F ∘ E) = trace(E ∘ F)`, and
  `E ∘ F = e_{H'} e_H ρ(x) = e_{H'} ρ(x)` on `V^{H'}` (`Jacquet.averageMap_averageMap_of_le`),
  whose trace is `ψ_{H'}(x)`.
- `traceCutoff`: `traceCoefficient_mem_range` and `TranslationWeights.mul_mem_schwartzSubmodule`.
- `traceFamily`, property (2): `convolution_apply` writes `(ϕ_H ∗ ε_{H'})(x)` as
  `∫ ϕ_H(y) ε_{H'}(y⁻¹x) dμ(y)`; the substitution `y = xk` (`integral_mul_left_eq_self`),
  `ε_{H'}(k⁻¹) = ε_{H'}(k)` and `φ(xkN) = φ(xN)` for `k ∈ H' ≤ N` (`hHN`) turn it into
  `(∫ ε_{H'}(k) ψ_H(xk) dμ(k)) φ(xN)`, and
  `integral_normalizedIndicator_mul_traceCoefficient` concludes. Property (1):
  `traceCoefficient_conj` and `hconj`.
- `traceFamily_operator_eval`: `IdempotentFamily.operator_apply_of_mem` and
  `schwartzAction_eval`.

## Relation to the Library

`Jacquet.compressedAction` (`Langlands.Representation.Jacquet.CanonicalLiftDefinitions`) is the
compressed action `e_K ρ(g)` on `V^K` used there for Jacquet modules; `traceCoefficient` is its
trace. `Hecke.fixedProjection` (`Langlands.Representation.Hecke.ActionProjection`) is the
fixed-vector projection defined through the Hecke action of `ε_H`;
`fixedProjection_eq_averageProjection` identifies it with the orbit mean `e_H` for a left and
right invariant Haar measure. `FiniteRankEnd.trace` (`Langlands.LinearAlgebra.FiniteRankTrace`)
is the trace of finite-rank endomorphisms, in which Waldspurger's `ψ_H` is stated.
`IdempotentFamily` and `IdempotentFamily.operator` (`SchwartzActionFamily`) are the abstract
family and the operator `π[ϕ]`; this module supplies Waldspurger's concrete family.

## Open obligations

Not formalized here:

- Corollary III.1.2 (the hypothesis `hD` for `ω̌`), and the facts that Waldspurger's `G¹` is
  open and normal, contains every compact open subgroup and has abelian quotient, that his
  Haar measure is right invariant, and that his `Ξ`, `σ` satisfy the weight hypotheses.
- The rest of the computation of `π[ϕ]` for irreducible `π` (the second equality, through the
  integral over `G¹\G`, the central characters, the Fourier inversion on `G¹A_G\G` and the
  Schur orthogonality relations), the definition of polynomials on `O` and of `π(p)`, and
  Proposition III.7.1 (ii) and (iii). Proposition III.7.1 itself remains open.
