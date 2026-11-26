# Spectral expansion of traces on the cuspidal space: proof

Module `Langlands.TraceFormula.GroupSchemeTwistedCuspidalSpectralExpansionProof` proves the
Library statement `Langlands.TraceFormula.GroupSchemeTwistedCuspidalSpectralExpansionStatement`
as the theorem

```lean
theorem groupSchemeTwistedCuspidalSpectralExpansion :
    GroupSchemeTwistedCuspidalSpectralExpansionStatement.{u}
```

in namespace `Langlands.TraceFormula`. The universe parameter `u` stays free. The proof uses
only `propext`, `Classical.choice` and `Quot.sound`.

## Notation

As in the statement's Markdown, `H = Lp ℂ 2 μ_Q` is the ambient `L²` space of the quotient,
`S = fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc` is the full almost-everywhere cuspidal
subspace, `R(f) = haarQuotientL2IntegratedAction F G T i hi I e hc ν f hf` acts on `H`,
`R_S(f) = fullAEL2CuspidalIntegratedAction F G hPD hG T i hi I e hc ν f hf` acts on `S`,
`π_c = fullAEL2CuspidalBoundedRightAction F G hPD hG T i hi I e hc` is the right action on `S`,
and `I_Θ = twistOperator Γ Θ hΘ μ_Q hΘμ` with `Γ = positiveRationalSubgroup F G T i`. For a
complete subspace `W` of a Hilbert space `E`, `p_W = W.orthogonalProjectionOnto : E →L[ℂ] W`
and `ι_W = W.subtypeL : W →L[ℂ] E`. The compression of `X : E →L[ℂ] E` to `W` is
`p_W ∘L X ∘L ι_W`. `tr` is the Library's `operatorTrace`.

## Library results used

- `Langlands.Analysis.OperatorIdeals.hilbertSumTrace : HilbertSumTraceStatement.{u, v}`
  (module `Langlands.Analysis.HilbertSumTraceProof`), used at `{u, u}`.
  - Part (1): for a complete subspace `W` of a complex Hilbert space `E` and a trace-class
    `X : E →L[ℂ] E` with `X x ∈ W` for all `x`, the compression `p_W X ι_W` is trace class and
    `tr (p_W X ι_W) = tr X`.
  - Part (2): for a Hilbert sum `E = ⨁ W i` of complete subspaces and a trace-class `X`, every
    compression `p_{W i} X ι_{W i}` is trace class, the norms of their traces are summable, their
    traces have sum `tr X`, and, if `X` maps each `W i` into `W (τ i)`, the traces over the
    indices with `τ i = i` also have sum `tr X`.

  Every Hilbert-space trace step of the proof is one of these clauses; the module does not
  reprove any of them.
- `Langlands.Analysis.OperatorIdeals.isTraceClass_precomp`
  (module `Langlands.Analysis.TraceClassIdealProof`): if `A` is trace class then so is
  `A ∘L C` for every bounded `C`.
- From `Langlands.Automorphic.GroupSchemeFullAEL2Integrated`:
  - `fullAEL2CuspidalIntegratedAction_val`: `(R_S(f) φ : H) = R(f) φ` for `φ : S`;
  - `fullAEL2CuspidalIntegratedAction_apply` (by `rfl`): `R_S(f) φ` is the Bochner integral
    `∫ a, f a • π_c(a) φ ∂ν`;
  - `fullAEL2CuspidalActionIntegrand_integrable`: that integrand is integrable.
- The instance `fullAEL2Cuspidal_completeSpace` (module
  `Langlands.Automorphic.GroupSchemeFullAEL2Hilbert`) supplies completeness of `S`.
- Mathlib: `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`,
  `Submodule.starProjection_eq_self_iff`, `ContinuousLinearMap.integral_comp_comm`,
  `integral_congr_ae`.

## Lemmas in the module

### `integral_mem_of_forall_mem`

Let `K` be a subspace with an orthogonal projection (for instance a complete subspace) of a
complex Hilbert space `E`, and let `g` be integrable with `g a ∈ K` for every `a`. Then
`∫ g ∈ K`. Write `Q = K.starProjection : E →L[ℂ] E` for the orthogonal projection onto `K`,
viewed in `E`. By `Submodule.starProjection_eq_self_iff` it suffices to show `Q (∫ g) = ∫ g`.
`ContinuousLinearMap.integral_comp_comm` gives `Q (∫ g) = ∫ Q ∘ g`, and `Q (g a) = g a` for
every `a`, again by `Submodule.starProjection_eq_self_iff`.

### `eq_compression_of_val`

Let `S` be a complete subspace of a Hilbert space `H`, `R : H →L[ℂ] H` and `RS : S →L[ℂ] S`
with `(RS φ : H) = R φ` for all `φ : S`. Then `RS = p_S ∘L R ∘L ι_S`: for `φ : S`, the right
side is `p_S (R φ) = p_S (RS φ) = RS φ` by `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`.

### `compression_hilbertSum_trace` (the ordinary expansion, abstractly)

With `S`, `R`, `RS` as above, assume `R` is trace class and `R φ ∈ S` for all `φ : H`.

- Part (1) of `hilbertSumTrace` with `E = H`, the subspace `S` and `X = R` gives trace class of
  `p_S R ι_S` and `tr (p_S R ι_S) = tr R`. Rewriting with `eq_compression_of_val` gives
  `IsTraceClass RS` and `tr RS = tr R`.
- For a Hilbert sum decomposition `A` of `S`, part (2) of `hilbertSumTrace` with `E = S`, index
  type `A`, `W P = P` and `X = RS` gives trace class of every compression `p_P RS ι_P`,
  summability of the norms of their traces, and `HasSum` with sum `tr RS`, which is rewritten to
  `tr R`.

The conclusion is stated in exactly the form of the first conjunct of the target statement.

### `twisted_compression_hilbertSum_trace` (the twisted expansion, abstractly)

With `S`, `R`, `RS` as above and an arbitrary bounded `I : H →L[ℂ] H`, let a family
`π : X → (S →L[ℂ] S)` be given such that `RS` preserves every complete subspace of `S` that is
invariant under all `π a`. Put `B = p_S ∘L (R ∘L I) ∘L ι_S`.

- `R ∘L I` is trace class by `isTraceClass_precomp`, and its range lies in `S` because that of
  `R` does. Part (1) of `hilbertSumTrace` gives `IsTraceClass B` and `tr B = tr (R ∘L I)`.
- Let `A` be a Hilbert sum decomposition of `S` into `π`-invariant complete subspaces and
  `τ : A → A` such that for `x ∈ P` there is `y ∈ τ P` with `(y : H) = I x`. Then
  `B x = p_S (R (I x)) = p_S (R y) = RS y` by `eq_compression_of_val`, and `RS y ∈ τ P` because
  `τ P` is `π`-invariant. So `B` maps each `P` into `τ P`.
- Part (2) of `hilbertSumTrace` with `E = S`, index type `A`, `W P = P` and `X = B` gives trace
  class of the compressions `p_P B ι_P` and summability of the norms of their traces; its
  fixed-point clause, applied to `τ` and the previous step, gives `HasSum` over
  `{P : A // τ P = P}` with sum `tr B`, rewritten to `tr (R ∘L I)`.

The conclusion is stated in exactly the form of the second conjunct of the target statement for
a fixed operator `I`.

### `groupSchemeTwistedCuspidalSpectralExpansion`

After introducing the group data, `ν`, `f`, `hf` and the two hypotheses on `R(f)`:

- `hval` is `fullAEL2CuspidalIntegratedAction_val`.
- Invariance: let `P` be a complete subspace of `S` with `π_c(a) x ∈ P` for all `a` and
  `x ∈ P`, and let `y ∈ P`. By `fullAEL2CuspidalIntegratedAction_apply`, `R_S(f) y` is the
  integral of `a ↦ f a • π_c(a) y`. That integrand is integrable
  (`fullAEL2CuspidalActionIntegrand_integrable`) and takes values in `P`, so
  `integral_mem_of_forall_mem` gives `R_S(f) y ∈ P`.
- The first conjunct of the target is `compression_hilbertSum_trace` with `H`, `S`, `R(f)` and
  `R_S(f)`. The second conjunct, for given `Θ`, `hΘ` and `hΘμ`, is
  `twisted_compression_hilbertSum_trace` with the family `π_c` and the operator `I_Θ`.

The Hilbert-sum steps are proved for an abstract Hilbert space and applied to the concrete
operators only at the end. This keeps elaboration of those steps away from the definitions of
the concrete subspace and operators, which are large terms.

## Scope

The argument uses no property of the twist `I_Θ` other than its boundedness and the supplied
containment hypothesis on `τ`; in particular, measure preservation `hΘμ` enters only through
the construction of `I_Θ`. Invariance of the summands under `R_S(f)` uses only that each
summand is closed and invariant under every right translation, and that `R_S(f)` is a Bochner
integral of weighted right translates. The decomposition `A` is arbitrary; no irreducibility,
multiplicity or countability is used.

## Relation to the sources

The proof is an internal derivation from the Library's Hilbert-sum trace theorem and the
construction of the integrated actions; it follows the "Mathematical argument" section of the
statement's Markdown.

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Corollary 18.4.1 and its
  proof (printed pp. 485–486): the spectral side is the sum over cuspidal `π` of the traces of
  `R(f)` on the isotypic components, `m(π) tr π(f)`. The first conjunct is the Hilbert-space
  step behind this, for an arbitrary supplied Hilbert sum: the trace of `R(f)` with cuspidal
  image equals the sum of the traces of the compressions of `R_S(f)` to the summands.
- Getz–Hahn (18.33)–(18.36) and Corollary 18.5.1 (printed pp. 487–488): `I_θ` is the pullback
  `φ ↦ φ ∘ θ⁻¹`, `R(f) ∘ I_θ` restricts to maps `L²_cusp(π^θ) → L²_cusp(π)`, and only the
  components with `π ≅ π^θ` contribute to the twisted spectral side. In the second conjunct the
  map `τ` records which summand the pullback sends each summand into, and the fixed-point
  clause of `hilbertSumTrace` removes the summands with `τ P ≠ P`.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique
  non nulle* (2011), II.6.3 (printed p. 119): `tr ρ⁰_ω(f) = ∑_π tr π(f)` over the cuspidal
  summands of the Hilbert direct sum `L⁰_ω(G, F)`; II.6.4 (printed p. 120):
  `tr (R⁰_χ(φ) ∘ I_σ) = ∑_Π tr (Π(φ) ∘ A_Π)` over the cuspidal `Π` with `Π^σ = Π`, where `I_σ`
  sends `Π` to a representation isomorphic to `Π^σ` and `A_Π` is its restriction. These are the
  spectral sides compared in II.6.6 (printed pp. 122–123). The compression of `R_S(f)` to a
  summand plays the role of `π(f)`, and the compression of `B` to a `τ`-fixed summand plays the
  role of `Π(φ) ∘ A_Π`; this module does not identify them with representations.
