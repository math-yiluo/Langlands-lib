# Smoothness of `π(f χ)` along a torus of characters (Waldspurger VII.1.3, case `M = G`)

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedFourierFamily`, namespace
`Langlands.HarishChandraSchwartz`. It imports:

- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierTransform`: `schwartzActionTensor`
  (the tensor of `π(f)` in `A ⊗ Ã`), `coefficientTensorToEnd` with
  `coefficientTensorToEnd_tmul`, `schwartzActionTensor_eq_of_coefficientTensorToEnd_eq`,
  `schwartzAction_apply_rho_of_mem`, and through its imports `schwartzAction`,
  `schwartzAction_eval`, `schwartzAction_mem_fixedVectors`, `continuous_coefficient`,
  `exists_nu_coefficient_ne_top`, `fixedFunctional`, `averageProjection` with
  `averageProjection_of_mem` and `averageProjection_apply`, `Space`, `nu`, `IsBiInvariant`,
  `CompactOpenSubgroup.inf` and `Jacquet.map_averageMap_of_forall_eq`;
- `Langlands.HarmonicAnalysis.HarishChandraSchwartz.TwistedCoefficientSmoothness`:
  `twistedCoefficientFamily` (the smooth function `z ↦ ∫_G f φ χ_z dμ`) with
  `twistedCoefficientFamily_apply`, and through its imports `finiteSmoothFamilies` and
  `torusCharacter` with `norm_torusCharacter`;
- `Langlands.HarmonicAnalysis.TorusFourierInversion`: torus characters on `J → Circle`.

## Provenance

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI 10.1017/S1474748003000082
(literature id `waldspurger-2003-plancherel`).

- Proof of Proposition VII.1.3, printed p. 316 (PDF p. 82): "Grâce au Lemme VII.1.2 et à la
  continuité de l'application `f ↦ f^{(P)}`, on est ramené au cas `M = G`. Fixons `(ω, E) ∈ O`
  et un sous-groupe ouvert compact `H` de `G`. Pour `v ∈ E^H`, `v̌ ∈ Ě^H`, `f ∈ C_H`,
  `χ ∈ Im X(G)`, posons `C_{v⊗v̌, f}(χ) = d(ω ⊗ χ) ⟨(ω ⊗ χ)(f̌) v, v̌⟩`. L'énoncé résulte des
  assertions suivantes: pour tous `v ∈ E^M`, `v̌ ∈ Ě^M`, on a: pour tout `f ∈ C_H`,
  `C_{v⊗v̌, f} ∈ C^∞(Im X(G))`; … Notons que `d(ω ⊗ χ) = d(ω)` pour tout `χ ∈ Im X(G)`."
  The superscripts `E^M`, `Ě^M` in this sentence are as printed (checked on the page image);
  the vectors are those of `E^H`, `Ě^H` fixed in the preceding definition.
- VII.1, printed p. 313 (PDF p. 79): `f̂(ω, G) = d(ω) ω(f̌)`, identified with an element of
  `E ⊗ Ě` by VII.1 (1).

The smoothness of the tensor family is source content (the first assertion above, for all
`v`, `v̌` at once). The coordinate formula `schwartzActionTensor_eq_sum`, the twist on `C(G)` and
the torus coordinates are derived. The module works with `ω(f χ_z)`, which is
`(ω ⊗ χ_z)(f)` by the definition of the twisted representation; that identification for the
Library's twisted representations is not proved here. The constant factor
`d(ω ⊗ χ) = d(ω)` is not part of this module.

### Correspondence with the source

- `(ω, E)` is an admissible smooth representation `A` of `G` with tempered coefficients
  (`hT`), and `ω(φ)` is `schwartzAction hw hA hT φ` for `φ ∈ C(G) = Space Ξ σ`. Its tensor in
  `E ⊗ Ě` (VII.1 (1)) is `schwartzActionTensor A hw hA hT φ`.
- `Im X(G)` is replaced by the torus `J → Circle`, and `χ(g)` by
  `χ_z(g) = torusCharacter (n g) z = ∏ⱼ zⱼ^{n(g)ⱼ}` for a supplied map `n : G → (J → ℤ)`. The
  twisted operator `(ω ⊗ χ_z)(φ) = ∫_G φ(g) χ_z(g) ω(g) dg` is `ω(φ χ_z)`, and `φ χ_z` is
  `Space.twist hn hK₀ z φ`. In the application `φ = f̌`.
- `C_{v⊗v̌, f}(χ)` corresponds, up to the constant `d(ω)`, to the coordinate `ℓ(π(f̌ χ_z) v)` of
  the tensor, with `ℓ` running over the smooth functionals `b.coord i ∘ e_K` attached to a basis
  `b` of `A^K`.

## Scope and hypotheses

### Twist section

`G` is a topological group, `Ξ σ : G → ℝ`, `J` a finite type, and `n : G → (J → ℤ)`.

- `twistedFunction n z f` and `nu_twistedFunction` need only the types.
- `IsBiInvariant.twistedFunction` uses the group structure, `hn : ∀ g h, n (g h) = n g + n h`,
  a subgroup `H` with `hH : ∀ k ∈ H, n k = 0`, and `hf : IsBiInvariant H f`.
- `twistedFunction_mem_schwartzSubmodule`, `Space.twist` and `Space.twist_apply` use
  `IsTopologicalGroup G`, `Nonempty (CompactOpenSubgroup G)`, `hn`, and a compact open subgroup
  `K₀` with `hK₀ : ∀ k ∈ K₀, n k = 0`.

### Tensor and family sections

`G` is a topological group with `MeasurableSpace`, `OpensMeasurableSpace`, `MeasurableMul` and
`Nonempty (CompactOpenSubgroup G)`; `μ` is a measure on `G` that is left and right invariant;
`A : SmoothRep ℂ G` with `hw : L2Weights μ Ξ σ`, `hA : IsAdmissible A.representation` and
`hT : HasTemperedCoefficients Ξ σ A.representation`.

- `sum_fixedFunctional_smul` uses only `A`, `hA`, a compact open subgroup `K` and a basis `b`
  of `A^K` indexed by a finite type, and `x ∈ A^K`.
- `schwartzActionTensor_eq_sum` also takes `hw`, `hT`, `K`, `b` and `f ∈ C(G)` with
  `hf : IsBiInvariant K f`.
- The family section adds `hn`, `K₀`, `hK₀`, `hnm : Measurable n` and
  `hnσ : ∀ g, ‖n g‖ ≤ C (1 + σ g)` for some real `C`. `smoothDual_schwartzAction_twist` does
  not use the right invariance of `μ`.

## Definitions

- `twistedFunction n z f : G → ℂ` is `g ↦ f(g) χ_z(g)`.
- `Space.twist hn hK₀ z : Space Ξ σ →ₗ[ℂ] Space Ξ σ` is `f ↦ f χ_z` on `C(G)`.

## Results

- `nu_twistedFunction`: `ν_r(f χ_z) = ν_r(f)`.
- `IsBiInvariant.twistedFunction`: `f χ_z` is bi-invariant under `H` if `f` is and `n`
  vanishes on `H`.
- `twistedFunction_mem_schwartzSubmodule`: `f χ_z ∈ C(G)` for `f ∈ C(G)`.
- `Space.twist_apply` (definitional): `(f χ_z)(g) = f(g) χ_z(g)`.
- `sum_fixedFunctional_smul`: for `x ∈ A^K`, `Σ_j ℓ_j(x) b_j = x`, where
  `ℓ_j = fixedFunctional … K (b.coord j)`.
- `schwartzActionTensor_eq_sum`: for `f` bi-invariant under `K`,
  `π(f) = Σ_{i,j} ℓ_j(π(f) b_i) b_j ⊗ ℓ_i` in `A ⊗ Ã`.
- `smoothDual_schwartzAction_twist`: `ℓ(π(f χ_z) w)` is the value at `z` of
  `twistedCoefficientFamily` for the coefficient `g ↦ ℓ(π(g) w)`, i.e.
  `∫_G f(g) ℓ(π(g) w) χ_z(g) dμ(g)`.
- `schwartzActionTensor_twist_mem_finiteSmoothFamilies`: `z ↦ π(f χ_z)` is a finite smooth
  family on `J → Circle` with values in `A ⊗ Ã`: a finite sum of `z ↦ c(z) t` with `c` smooth
  and `t` fixed.

## Proof notes

1. `nu_twistedFunction`: `|χ_z(g)| = 1`. `IsBiInvariant.twistedFunction`: `n(k₁ g k₂) = n(g)`
   for `k₁, k₂ ∈ H`.
2. `twistedFunction_mem_schwartzSubmodule`: if `f` lies in the level `C_H`, then `f χ_z` lies in
   `C_{H ∩ K₀}`.
3. `schwartzActionTensor_eq_sum`: by uniqueness of the tensor it suffices to compare
   endomorphisms. `π(f) b_i ∈ A^K` because `f` is left `K`-invariant, so
   `Σ_j ℓ_j(π(f) b_i) b_j = π(f) b_i` (`sum_fixedFunctional_smul`). Then
   `Σ_i ℓ_i(w) π(f) b_i = π(f)(e_K w) = π(f) w`, since `f` is right `K`-invariant.
4. `smoothDual_schwartzAction_twist`: `schwartzAction_eval` and reordering the integrand.
5. Family: choose `H` with `f ∈ C_H`. All `f χ_z` are bi-invariant under `K = H ∩ K₀`. Fix a
   basis `b` of the finite-dimensional `A^K`. By step 3 each value is
   `Σ_{i,j} c_{ij}(z) b_j ⊗ ℓ_i` with `c_{ij}(z) = ℓ_j(π(f χ_z) b_i)`, which is smooth by step 4.

## Relation to the Library

- `TwistedCoefficientSmoothness` proves the smoothness and estimate (2) of the twisted scalar
  coefficients. This module assembles them into the tensor family of VII.1.3 for `M = G`, using
  the explicit tensor of `π(f)` from `FourierTransform`.

## Open obligations

- The identification of `(ω ⊗ χ)(f)` for the Library's literal twist of `ω` with `ω(f χ)`, the
  equality `d(ω ⊗ χ) = d(ω)`, the passage from `Im X(G)` to torus coordinates with a lattice map
  `n`, and the reduction from general `M` to `M = G` through Lemma VII.1.2 are not done here.
- The continuity of `f ↦ C_{v⊗v̌, f}` (the second assertion) is covered in seminorm form for the
  scalar coefficients in `TwistedCoefficientSmoothness`; no topology on `C^∞(O, P)` is
  introduced.
