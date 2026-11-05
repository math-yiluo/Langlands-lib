# Haar volume of height balls in dynamic unipotent subgroups

Lean module: `Langlands.HarmonicAnalysis.HarishChandraSchwartz.UnipotentHeightVolume`.
The conjugation automorphism, the Haar iterate lemmas and `offIdentityNorm_le_glNorm` are in
the namespace `Langlands.HarishChandraSchwartz`. The local-field theorems are in the namespace
`Langlands.GroupScheme.MatrixRepresentation`.

## Purpose and provenance

Provenance: internal. Convergence arguments for intertwining integrals integrate a weight
against Haar measure on an opposite unipotent group `Ū(F)`. They need the Haar volume of the
height balls `{x : ‖x‖ ≤ R}` to grow at most polynomially in `R`. In Waldspurger, *La formule de
Plancherel pour les groupes p-adiques, d'après Harish-Chandra* (2003), this kind of growth bound
is used in II.3 and IV.1 together with the height estimates of II.2. It is not stated there in
the form proved here. This module proves the bound directly, for every closed subgroup `H` of
`Ū(F) = U(χ⁻¹)(F)` that is normalized by the image of the cocharacter `χ`. The proof uses the
contraction of `H` by conjugation with `χ(ϖ)` and the Haar character of that automorphism. It
does not transcribe a proof from the source.

## Setting and notation

- `Γ` is a topological group and `H` a subgroup of `Γ`. `Subgroup.normalizer (H : Set Γ)` is
  the normalizer of `H` in `Γ`.
- For a locally compact topological group `H`, `mulEquivHaarChar φ : ℝ≥0` (Mathlib) is the
  Haar character of a continuous automorphism `φ : H ≃ₜ* H`. Mathlib proves that it is positive
  and that `mulEquivHaarChar φ • ν (φ ⁻¹' X) = ν X` for every regular Haar measure `ν`
  (`mulEquivHaarChar_smul_preimage`).
- For a normed field `F`, a finite nonempty type `n` and `g ∈ GL_n(F)`, `entryNorm M` is the
  largest norm of an entry of a matrix `M`, `glNorm g = max (entryNorm g) (entryNorm g⁻¹)`
  (public `Height`), and `offIdentityNorm g = entryNorm (g - 1)` (public `DiagonalContraction`).
- In the local-field part, `F` carries `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]`. `q` is `LocalField.residueCardinality F`, and `F` is normed
  by `LocalField.residueNormalizedAbsoluteValue F`, which has `|ϖ| = q⁻¹` for the uniformizer
  `ϖ`. `G` is a group scheme over `Spec F` with `G.X.left` affine, and `G(F)` is
  `rationalPoints G`. In the theorems that use Haar measure, `G` is also locally of finite type
  over `F`, and `G(F)` carries the canonical point topology `rationalPointTopology F G.X`. With
  this topology `G(F)` is a locally compact topological group (public
  `rationalPoint_isTopologicalGroup`, `rationalPoint_locallyCompactSpace`).
- For a representation `ρ₀ : G ⟶ GL_N` on `Fin N`, `rationalMatrixNorm F ρ₀ x` is
  `glNorm (ρ₀.rationalMatrix x)`, the largest absolute value of an entry of `ρ₀(x)` or
  `ρ₀(x)⁻¹`. `IsClosedSubgroup ρ₀` says that `ρ₀` is a closed immersion.
- `χ : 𝔾_m ⟶ G` is a cocharacter and `χ(t) = gmRationalPoint t ≫ χ.hom.hom ∈ G(F)` for
  `t ∈ Fˣ`. The subgroup `Ū` is `Dynamic.unipotent` of the cocharacter `t ↦ χ(t⁻¹)`, written in
  Lean as `CommGroupScheme.groupHom (Gm.powerHom _ (-1)) ≫ χ`.

## Declarations

### Conjugation by a normalizing element

- `normalizerInvConj ha : H ≃ₜ* H` (definition), for `ha : a ∈ Subgroup.normalizer (H : Set Γ)`:
  the continuous automorphism `x ↦ a⁻¹ * x * a` of `H`, with inverse `x ↦ a * x * a⁻¹`.
- `coe_normalizerInvConj_apply` (simp): `(normalizerInvConj ha x : Γ) = a⁻¹ * x * a`.
- `coe_normalizerInvConj_iterate`: the `k`-th iterate sends `x` to `(a ^ k)⁻¹ * x * a ^ k`.

### Haar measure under iterated automorphisms

Here `H` is a locally compact topological group with a Borel measurable structure, `ν` is a
regular Haar measure on `H` and `φ : H ≃ₜ* H`.

- `measure_preimage_mulEquiv`: `ν (φ ⁻¹' X) = (mulEquivHaarChar φ)⁻¹ * ν X`.
- `measure_preimage_iterate_mulEquiv`:
  `ν (φ^[k] ⁻¹' X) = ((mulEquivHaarChar φ)⁻¹) ^ k * ν X`.
- `measure_le_of_iterate_mem`: if `φ^[k] x ∈ K` for every `x ∈ S`, then
  `ν S ≤ ((mulEquivHaarChar φ)⁻¹) ^ k * ν K`.

### Matrix norms

- `offIdentityNorm_le_glNorm`: for an ultrametric normed field `F` and `g ∈ GL_n(F)`,
  `offIdentityNorm g ≤ glNorm g`.

### Local fields

- `isCompact_rationalMatrixNorm_le`: for `G.X.left` affine, `ρ` a closed representation on a
  nonempty `Fin N` and `C : ℝ`, the set `{g ∈ G(F) | rationalMatrixNorm F ρ g ≤ C}` is compact
  in the point topology.
- `exists_measure_rationalMatrixNorm_le_pow` (main theorem). Let `G` be affine and locally of
  finite type over `F`, `χ` a cocharacter of `G`, and `ρ₀` a closed representation of `G` on
  `Fin N` with `N` positive. Let `H` be a subgroup of `G(F)` such that
  - `H` is closed in `G(F)`,
  - `H ≤ Ū(F)`, and
  - `χ(t)` lies in the normalizer of `H` for every `t ∈ Fˣ`.

  Give `H` any measurable structure for which it is a Borel space, and let `ν` be a regular Haar
  measure on `H`. Then there are `C, B : ℝ≥0` with
  `ν {x ∈ H | rationalMatrixNorm F ρ₀ x ≤ q ^ n} ≤ C * B ^ n` for every `n : ℕ`.
- `exists_measure_rationalMatrixNorm_le_mul_pow` (polynomial form). Under the same hypotheses
  there are `C : ℝ` and `D : ℕ` with
  `ν {x ∈ H | rationalMatrixNorm F ρ₀ x ≤ R} ≤ ENNReal.ofReal (C * R ^ D)` for every real
  `R ≥ 1`.

## Proofs as implemented

**Conjugation.** By `Subgroup.mem_normalizer_iff`, `y ∈ H` holds exactly when
`a * y * a⁻¹ ∈ H`. With `y = x` this gives `a x a⁻¹ ∈ H`; with `y = a⁻¹ x a` it gives
`a⁻¹ x a ∈ H`, because `a (a⁻¹ x a) a⁻¹ = x`. Both maps are continuous as products of constants with the inclusion of `H`. The iterate
formula is proved by induction on `k`, using `pow_succ` and `group`.

**Haar lemmas.** Mathlib's `mulEquivHaarChar_smul_preimage` gives
`mulEquivHaarChar φ * ν (φ ⁻¹' X) = ν X`. Multiplying by the inverse of the positive number
`mulEquivHaarChar φ` gives `measure_preimage_mulEquiv`. The iterate version follows by
induction, since `φ^[k + 1] ⁻¹' X = φ ⁻¹' (φ^[k] ⁻¹' X)`. For `measure_le_of_iterate_mem`, the
hypothesis says `S ⊆ φ^[k] ⁻¹' K`; apply monotonicity of `ν` and the iterate formula.

**`offIdentityNorm_le_glNorm`.** Each entry of `g - 1` is `g i j + (-δ_{ij})`. By the
ultrametric inequality its norm is at most `max ‖g i j‖ ‖δ_{ij}‖`. The first term is at most
`glNorm g`. The second is at most `entryNorm 1 = 1`, and `1 ≤ glNorm g` (public
`one_le_glNorm`).

**Compactness.** `glNorm M ≤ C` holds exactly when every entry of `M` and of `M⁻¹` has
absolute value at most `C` (public `norm_le_glNorm`, `norm_inv_le_glNorm`, `glNorm_le`). After
rewriting the set this way, compactness is `isCompact_rationalMatrix_entry_le` from
`OppositeUnipotentDisplacement`.

**Main theorem.**

1. *Diagonalize.* By public `exists_innerIso_comp_eq_diagonalCocharacter` there are
   `g₀ ∈ GL_N(F)` and weights `e₀ : Fin N → ℤ` such that `ρ₁ = ρ₀ ≫ innerIso g₀` satisfies
   `χ ≫ ρ₁ = diagonalCocharacter e₀`. The representation `ρ₁` is closed (public
   `IsClosedSubgroup.comp_iso`). By `rationalMatrix_comp_innerIso`, with `M = glNorm g₀ ≥ 1`
   (public `glNorm_mul_le`, `glNorm_inv`):
   `rationalMatrixNorm F ρ₁ x ≤ M ^ 2 * rationalMatrixNorm F ρ₀ x`.
2. *Matrices of `χ(t)` and of `H`.* By `rationalMatrix_gmRationalPoint_comp`, `ρ₁(χ(t))` is the
   diagonal matrix `diagonalUnits F e₀ t = diag(t^{e₀ i})`. For `x ∈ H ≤ Ū(F)`, public
   `Dynamic.mem_unipotent_iff_of_diagonal` together with
   `rationalMatrix_mem_blockUnipotentSubgroup_iff` shows that `ρ₁(x)` lies in
   `blockUnipotentSubgroup F (-e₀)`.
3. *Contraction.* Let `t = ϖ`, so `|t| = q⁻¹`, and let `φ = normalizerInvConj` of `χ(t)` on
   `H`. Choose `d` with `e₀ j - e₀ i ≤ d` whenever `e₀ i < e₀ j` (public
   `exists_weight_gap_le`), and `m₀` with `M ^ 2 < q ^ m₀`. Let `x ∈ H` with
   `rationalMatrixNorm F ρ₀ x ≤ q ^ n`, and put `k = n + m₀`. By the iterate formula and step 2,
   the matrix of `φ^[k] x` under `ρ₁` is `D⁻¹ ρ₁(x) D` with `D = diagonalUnits F e₀ (t ^ k)`.
   Public `offIdentityNorm_conj_le` gives
   `offIdentityNorm (D⁻¹ ρ₁(x) D) ≤ q^{-k} * offIdentityNorm ρ₁(x)`. Also
   `offIdentityNorm ρ₁(x) ≤ rationalMatrixNorm F ρ₁ x ≤ M ^ 2 * q ^ n ≤ q ^ k`, using
   `offIdentityNorm_le_glNorm`, step 1 and the choice of `m₀`. Hence
   `offIdentityNorm (D⁻¹ ρ₁(x) D) ≤ 1`. The conjugate is still in
   `blockUnipotentSubgroup F (-e₀)` (public `diagonalUnits_conj_mem`). By
   `glNorm_le_max_offIdentityNorm_pow` from `OppositeUnipotentDisplacement`, its `glNorm` is at
   most `max 1 (offIdentityNorm …) ^ (d + 1) = 1`. Thus `φ^[n + m₀]` maps the height ball
   `{x ∈ H | rationalMatrixNorm F ρ₀ x ≤ q ^ n}` into `K₀ = {y ∈ H | rationalMatrixNorm F ρ₁ y ≤ 1}`.
4. *Volume.* `H` is locally compact, because it is closed in the locally compact group `G(F)`.
   `K₀` is compact, as the preimage under the closed embedding `H → G(F)` of the compact set
   given by `isCompact_rationalMatrixNorm_le`. So `ν K₀ < ∞`. By `measure_le_of_iterate_mem`,
   the ball has volume at most `c⁻¹ ^ (n + m₀) * ν K₀`, where `c = mulEquivHaarChar φ`. Take
   `C = c⁻¹ ^ m₀ * ν K₀` and `B = c⁻¹`.

**Polynomial form.** Let `C, B` be as in the main theorem. Choose `D` with `B < q ^ D`
(`pow_unbounded_of_one_lt`, as `q > 1`). For `R ≥ 1`, Mathlib's `exists_nat_pow_near` gives
`n` with `q ^ n ≤ R < q ^ (n + 1)`, so `q ^ (n + 1) ≤ q * R`. The ball of radius `R` lies in
the ball of radius `q ^ (n + 1)`, whose volume is at most
`C * B ^ (n + 1) ≤ C * (q ^ (n + 1)) ^ D ≤ C * (q * R) ^ D = (C * q ^ D) * R ^ D`.

## Scope

The constants `C`, `B` and `D` depend on `H`, `ν`, `χ` and `ρ₀`. They are produced by the proof
and are not explicit: `B` is the inverse Haar character of conjugation by `χ(ϖ)` on `H`, which is
not computed in terms of roots or the modulus character. The theorems need `H` to be closed and
normalized by all of `χ(Fˣ)`; they do not show that a given subgroup, such as `Ū(F)` itself or an
intersection of unipotent radicals, has these properties. They give only upper bounds on volumes,
not lower bounds or asymptotics. Nothing here concerns quotient measures, Iwasawa
decompositions or the host conditional intertwining theorem.
