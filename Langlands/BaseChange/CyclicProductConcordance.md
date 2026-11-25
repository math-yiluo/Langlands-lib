# Concordance through the coordinates of a cyclic algebra

`Langlands.BaseChange.CyclicProductConcordance`. Namespace `Langlands.BaseChange`.

Transport of concordance from a cyclic field extension `L / F` to a cyclic algebra
`E ≅ L^{m+1}`, through the coordinates on `GL_n`; the field coordinates of a cyclic algebra; the
Haar measures that the coordinates carry to product measures; the construction from `GL_n(E)`
to `GL_n(L)`.

## Coordinates and measures

- `exists_cyclicAlgebraFieldCoordinates {F : Type u} [Field F] {E : Type v} [CommRing E]
  [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ} (hσ : IsCyclicAlgebra σ l) :
  ∃ (L : Type v) (_ : Field L) (_ : Algebra F L) (m d : ℕ) (τ : L ≃ₐ[F] L)
  (c : E ≃ₐ[F] (Fin (m + 1) → L)), l = (m + 1) * d ∧ IsCyclicAlgebra τ d ∧
  (∀ (x : E) (i : Fin m), c (σ x) i.castSucc = c x i.succ) ∧
  ∀ x : E, c (σ x) (Fin.last m) = τ (c x 0)`. Proof: the residue field `L = E ⧸ 𝔪` and the
  coordinates `x ↦ (σ^i x mod 𝔪)_i` of the Library's `CyclicAlgebraStructure.exists_coordinates`,
  renumbered by `Fin (m + 1)`; the shift rule is `σ^{i+1} = σ^i σ`, the wrap rule is the field
  `wrap` of `Coordinates`.
- `exists_isHaarMeasure_measurePreserving_pi` (`H : Type u`, `G : Type v` topological groups with
  Borel σ-algebras, `G` locally compact and second countable, `κ : H ≃ₜ* (Fin (m + 1) → G)`,
  `μH` a Haar measure of `H`): `∃ μ : Measure G, μ.IsHaarMeasure ∧
  MeasurePreserving κ μH (Measure.pi fun _ : Fin (m + 1) => μ)`. Proof: for `μ₀ = haar`,
  `ν₀ = κ⁻¹_*(μ₀^{⊗(m+1)})` is a Haar measure of `H` (second countable, locally compact through
  `κ`), so `μH = s • ν₀` with `s = haarScalarFactor μH ν₀ > 0` (Mathlib's uniqueness of Haar
  measures); `μ = s^{1/(m+1)} • μ₀` has `μ^{⊗(m+1)} = s • μ₀^{⊗(m+1)}` (`Measure.pi_eq`).

## Setting

`F` a nonarchimedean local field (`[Field F] [ValuativeRel F] [TopologicalSpace F]
[IsNonarchimedeanLocalField F]`); `E` a commutative `F`-algebra with
`[TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]`; `L` a field with
`[Algebra F L] [TopologicalSpace L] [IsTopologicalRing L] [IsModuleTopology F L]`;
`σ : E ≃ₐ[F] E`, `τ : L ≃ₐ[F] L`; `c : E ≃ₐ[F] (Fin (m + 1) → L)` with `hc : Continuous c`,
`hc' : Continuous c.symm`, the shift rule `hshift : ∀ x i, c (σ x) i.castSucc = c x i.succ` and
the wrap rule `hwrap : ∀ x, c (σ x) (Fin.last m) = τ (c x 0)`; Borel σ-algebras on `GL_n(F)`,
`GL_n(E)`, `GL_n(L)`; `κ = cyclicProductGLCoordinates (n := n) c hc hc' :
GL_n(E) ≃ₜ* (Fin (m + 1) → GL_n(L))`.

## Statements

The two facts on norms and measures that the transport uses in the coordinates,
`vanishesOffNorms_cyclicProduct_iff` and `IsAssociatedMeasure.cyclicProduct`, are in
`Langlands.BaseChange.CyclicProductNormCoordinates`.

- `isClosedEmbedding_twistedOrbitFunction_of_isNormAssociated (hτ : IsCyclicAlgebra τ d)
  {y : GL_n(L)} {γ : GL_n(F)} (hassoc : IsNormAssociated τ d y γ) (hreg : IsRegularSemisimple γ) :
  IsClosedEmbedding (twistedOrbitFunction (entrywiseAut τ n) y id)` (no coordinates involved:
  a statement about the cyclic field extension `L / F`).
- `areConcordant_cyclicProduct_of_splitFiberIntegral (hσ : σ ^ ((m + 1) * d) = 1)
  (hτ : IsCyclicAlgebra τ d) (μF : Measure (GL_n(F))) (μ : Measure (GL_n(L))) [μ.IsHaarMeasure]
  (μE : Measure (GL_n(E))) (hκ : MeasurePreserving κ μE (Measure.pi fun _ : Fin (m + 1) => μ))
  (Φ : (Fin (m + 1) → GL_n(L)) → ℂ) (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ)
  (f : GL_n(F) → ℂ) (h : AreConcordant τ d μF μ (splitFiberIntegral μ Φ) f) :
  AreConcordant σ ((m + 1) * d) μF μE (fun x => Φ (κ x)) f`.
- `areConcordant_cyclicProduct_of_splitFiberConvolution`: the same for a tensor
  `x ↦ ∏ i, ψ i (κ x i)` of continuous compactly supported `ψ i`, with the hypothesis
  `AreConcordant τ d μF μ (splitFiberConvolution μ ψ) f`.
- `exists_concordant_ordinary_cyclicProduct` (same hypotheses as the transport,
  `φ : SchwartzBruhat (GL_n(E))`): `∃ φL : SchwartzBruhat (GL_n(L)), (∀ K₀ : Subgroup (GL_n(L)),
  Function.support φ ⊆ κ ⁻¹' Set.pi Set.univ (fun _ => (K₀ : Set _)) → Function.support φL ⊆ K₀) ∧
  ∀ f : GL_n(F) → ℂ, AreConcordant τ d μF μ φL f → AreConcordant σ ((m + 1) * d) μF μE φ f`.
  Here `φL = splitFiberIntegral μ (φ ∘ κ⁻¹)` (`splitFiberIntegral_mem_schwartzBruhat`,
  `support_splitFiberIntegral_subset`, and the transport).
- `exists_concordant_twisted_cyclicProduct` (same hypotheses, `φL : SchwartzBruhat (GL_n(L))`):
  `∃ φ : SchwartzBruhat (GL_n(E)), ∀ f : GL_n(F) → ℂ, AreConcordant τ d μF μ φL f →
  AreConcordant σ ((m + 1) * d) μF μE φ f`. Here `φ = splitUnitTensor μ K φL ∘ κ` for a compact
  open subgroup `K` of `GL_n(L)` under which `φL` is bi-invariant
  (`Hecke.TestFunction.commonCompactOpenBiInvariance`); its fibre integral is `φL`
  (`splitFiberIntegral_splitUnitTensor`, left invariance).

Neither construction asks anything of supports; the neighbourhoods of the end theorem enter only
through the support conjunct of `exists_concordant_ordinary_cyclicProduct`.

No hypothesis is put on `μF` or `μE` beyond `hκ`: the measures on the centralizers and quotients
are those over which `AreConcordant` quantifies.

## Proofs

- Closed orbits: `N_τ(y)` is conjugate to `γ` in `GL_n(L)`, hence regular semisimple
  (`IsRegularSemisimple.baseChange`, `isRegularSemisimple_conj_iff`); then
  `isClosed_range_twistedConj_of_regularNorm` and `isClosedEmbedding_twistedOrbitFunction_id`.
- Non-norms: `vanishesOffNorms_cyclicProduct_iff` of `CyclicProductNormCoordinates`.
- At an associated pair `(δ, γ)` with `γ` regular semisimple
  (private `concordAt_cyclicProduct`), with `β = (List.ofFn (κ δ)).prod` (associated with `γ`
  for `τ` by `cyclicProductGLCoordinates_normAssociated_iff`): given `μδ`, `μγ`, `νδ`, `νγ` as in
  `ConcordAt`, put `μZ = e_* μδ` for the zeroth-coordinate isomorphism
  `e = cyclicProductCentralizerEquiv` of the twisted centralizers; take `νZ` compatible with
  `(μ, μZ)` (`compatibleMeasureExists`; `μ` is right invariant, `generalLinear_haar_rightInvariant`).
  `μZ` is associated with `μγ` (`IsAssociatedMeasure.cyclicProduct` of
  `CyclicProductNormCoordinates`) and the τ-twisted orbit of
  `β` is closed (`isClosedEmbedding_twistedOrbitFunction_of_isNormAssociated`). Then
  `cyclicProductOrbitalIntegral_eq_splitFiberIntegral` (of `CyclicProductConvolution`) and the
  concordance on `GL_n(L)` at
  `(β, γ)`.
- Tensors: `splitFiberIntegral_tensor`.

Private helpers: `generalLinear_topology_of_cyclic` (`GL_n(L)` Hausdorff, locally compact, second
countable, totally disconnected; `L` Hausdorff), `concordAt_cyclicProduct`.

## Declarations, in order

`exists_cyclicAlgebraFieldCoordinates`, `exists_isHaarMeasure_measurePreserving_pi`, private
`generalLinear_topology_of_cyclic`, `isClosedEmbedding_twistedOrbitFunction_of_isNormAssociated`,
private `concordAt_cyclicProduct`, `areConcordant_cyclicProduct_of_splitFiberIntegral`,
`areConcordant_cyclicProduct_of_splitFiberConvolution`, `exists_concordant_ordinary_cyclicProduct`,
`exists_concordant_twisted_cyclicProduct`.

## Literature

- G. Henniart and B. Lemaire, *Changement de base et induction automorphe pour GLₙ en
  caractéristique non nulle*, Mém. SMF 124 (2011): §I.2.1, pp. 10–11 (the cyclic algebra
  `E = E₁^r` with `σ(x₁, …, x_r) = (x₂, …, x_r, τ x₁)`, the norm `N'¹(δ) = δ₁ ⋯ δ_r` and
  `p'¹ ∘ N' = N₁ ∘ N'¹`); §I.2.2, p. 12 (association; `N(O_σ(δ)) = N₁(O_τ(N¹(δ)))`); §I.2.3, p. 13
  (the σ-centralizer identified with `G^τ_y(F)` through the first coordinate); §I.2.4, pp. 15–16
  (the orbital identity, with `dg^σ_δ = dg^τ_y`); §I.2.5, p. 17 (associated measures, concordance);
  §I.2.6, p. 18 (the two constructions of the reduction to a field, for regular support). HL take
  `dg_E` to be the product measure; here `hκ` says the same of `μE` and `μ`.
- J. Arthur and L. Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), Chapter 1, §5, pp. 48–49 ("if `f` is associated to `ψ` in the sense of
  Proposition 3.1, … the σ-twisted orbital integrals of `φ` coincide with the orbital integrals of
  `f`. The quotient measures must be normalized in obvious ways.").
