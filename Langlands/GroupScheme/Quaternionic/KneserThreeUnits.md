# The exterior-square map: units, naturality and an invariant polar matrix

Module `Langlands.GroupScheme.Quaternionic.KneserThreeUnits`, namespace
`Langlands.GroupScheme.KneserThree`. This is internal support for the explicit A₃ = D₃
comparison used to prove `KneserThreeSpinSubgroupStatement` (Kneser's argument as summarized in
Tits, Bourbaki 505, 1977, no. 1.1.6). It makes no literature claim beyond the identities proved
here. It extends the exterior-square map `Presentation.cmap` of `KneserThreeCore` in three ways:
it is natural in the coefficients, it is a homomorphism into unit matrices, and it preserves the
polar matrix `[[0, 1, 0], [1, 0, 0], [0, 0, μ]]` for a suitable involution of the first kind.
The module `KneserThreeModelHom` uses these results to build the group-scheme morphism.

Throughout, `P : Presentation A B` writes `B = ι(A) ⊕ j ι(A)` (module `KneserThreePresentation`),
`ā` is the involution `P.c.bar` of `A`, `θ l₁ l₂ w : A`, and `ℓ = P.elem l₁ l₂ = ι l₁ + j ι l₂`.
The unit hypothesis of `KneserThreeCore` is `hw : w · (θ · (l₁ l̄₁ - δ l₂ l̄₂)) = 1`.

## Naturality (`Presentation`, section `Map`)

Let `P' : Presentation A' B'`, `φA : A →+* A'` and `φB : B →+* B'`. Assume `φA` commutes with the
involutions (`hbar`) and sends `δ` to `δ'` (`hδ`). Assume also that `φB ∘ ι = ι' ∘ φA` (`hι`)
and `φB j = j'` (`hj`).

* `map_elem`: `φB (elem a a') = elem' (φA a) (φA a')` (uses `hι`, `hj`).
* `frame_map`, `frameInv_map`: the matrices `frame` and `frameInv` of `KneserThreeCore` are
  mapped entrywise to the corresponding matrices of `P'` at the mapped parameters (uses
  `hbar`, `hδ`).
* `adapted_map`: the same holds for `adapted θ l₁ l₂ w g`, with `g` mapped entrywise; this uses
  `ExteriorSquare.matrix_map`.
* `cmap_map`: `(cmap θ l₁ l₂ w g).map φB = cmap' (φA θ) (φA l₁) (φA l₂) (φA w) (g.map φA)`.

## Units (section `Units`)

`cmapUnits hθ hw f hf : G →* (Matrix (Fin 3) (Fin 3) B)ˣ`. Here `G` is a group,
`f : G →* (Matrix (Fin 4) (Fin 4) A)ˣ`, every `f g` is special unitary (`hf`), and
`hθ : θ̄ = -θ`. The value is `cmap (f g)` with inverse `cmap (f g⁻¹)`, by `cmap_mul` and
`cmap_one` of `KneserThreeCore`. Its value is recorded in `cmapUnits_val`.

## The polar matrix (section `Polar`)

* `polarMatrix μ = !![0, 1, 0; 1, 0, 0; 0, 0, μ]`, a `3 × 3` matrix over any ring.
* `elem_mul_self`: if `l̄₁ = -l₁` then `ℓ · ℓ = ι (l₁ l₁ + δ l̄₂ l₂)`.
* `skewHermitian_eq`: if `l̄₁ = -l₁` and `μ = -(ι θ · ℓ)`, then the matrix `skewHermitian θ l₁ l₂`
  of `KneserThreeCore` equals `polarMatrix μ · diag(ℓ, ℓ, ℓ)`.
* `cmap_mul_polarMatrix_mul_matrix`. Let `S` be a commutative ring with `[Algebra S B]`, and let
  `τ` be an involution of the first kind of `B` over `S` with `τ b = ℓ · bar b · ℓ⁻¹`. Here
  `ℓ⁻¹` is a right inverse `ℓinv` (`ℓ · ℓinv = 1`) and `bar` is the conjugation of `B` from
  `KneserThreePresentation`. Assume `θ̄ = -θ`, `l̄₁ = -l₁`, `hw` and `μ = -(ι θ · ℓ)`. Then for
  every special unitary `g`, with `X = cmap θ l₁ l₂ w g`,
  `X · polarMatrix μ · τ.matrix (Fin 3) X = polarMatrix μ`. Here `τ.matrix (Fin 3)` is the
  `τ`-conjugate transpose. The proof writes `τ.matrix X = diag(ℓ) · conjTranspose X · diag(ℓinv)`
  and applies `cmap_mul_skewHermitian_mul_conjTranspose` with `skewHermitian_eq`.
* `bar_add`, `bar_zero`: `Presentation.bar` is additive.

## Constant parameters for `QuatData` (namespace `QuatData`)

Let `Q : QuatData K D` (module `KneserThreeSplitting`), `L = field Q.c`, and let `R` be a
commutative `K`-algebra.

* `Q.bar d = ι (ā₀) - j ι a₁` where `d = ι a₀ + j ι a₁` (`a₀ = fst d`, `a₁ = snd d`), and
  `Q.elem a a' = ι a + j ι a'`.
* `Q.const R = Algebra.TensorProduct.includeLeft : L →ₐ[K] L ⊗[K] R`, `a ↦ a ⊗ 1`.
* `presentation_bar_tmul`: the conjugation of `Q.presentation R` sends `r ⊗ d` to
  `r ⊗ Q.bar d`.
* `presentation_elem_const`, `presentation_ι_const`, `presentation_bar_const`,
  `presentation_δ`: at constant parameters, `elem`, `ι`, the involution and `δ` of
  `Q.presentation R` are `1 ⊗ (Q.elem a a')`, `1 ⊗ ι a`, `const ā` and `const δ`.
* `presentation_bar_const_neg`: `ā = -a` implies the same for `const a`.
  `presentation_unit_const`: the unit hypothesis `hw` over `L` implies it for the constants over
  `L ⊗[K] R`.
* `mapA_const` (simp): `mapA φ (const a) = const a` for every `K`-algebra map `φ : R → R'`.
* `baseChange_eq`. Let `σ` be an involution of the first kind of `D` with
  `σ d = Q.elem l₁ l₂ · Q.bar d · ℓinv` for all `d`. Then its base change is
  `σ.baseChange R b = elem (const l₁) (const l₂) · bar b · (1 ⊗ ℓinv)` for all `b : R ⊗[K] D`.
  The proof is by induction on tensors.
* `QuatData.cmap_mul_polarMatrix_mul_matrix`: the polar identity above for `Q.presentation R`,
  the constant parameters `const θ, const l₁, const l₂, const w`, `τ = σ.baseChange R` and
  `μ = 1 ⊗ (-(ι θ · Q.elem l₁ l₂))`. The hypotheses are over `L`: `θ̄ = -θ`, `l̄₁ = -l₁`, `hw`
  (with `δ` replaced by `algebraMap K L Q.δ`), `Q.elem l₁ l₂ · ℓinv = 1` and the formula for `σ`.

## From the polar matrix to the quadratic class

For an involution of the first kind `τ` of an `S`-algebra `M` and `h : S` with `2 h = 1`:

* `mem_alternatingSubspace_of_neg`: if `τ d = -d` then `d = h d - τ (h d)` lies in
  `τ.alternatingSubspace`.
* `defect_mem_of_polar`: if `X (Q + τ Q) τ X = Q + τ Q`, then `X Q τ X - Q` lies in
  `τ.alternatingSubspace`. Indeed `d = X Q τ X - Q` satisfies `τ d = -d`.

In `KneserThreeModelHom` this turns preservation of the polar matrix into membership in the
isometry group of a quadratic form in Tits's sense (`FirstKindInvolution.QuadraticForms`) when
`2` is invertible.
