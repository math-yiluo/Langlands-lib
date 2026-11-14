# Left-axis cup and shuffle slant

This module is internal infrastructure in the namespace
`Langlands.Cohomology.Cech.KunnethDetection`. It extends the shuffle slant `L` of
[CechKunneth](CechKunneth.md) and [CechSlant](CechSlant.md). The setting is the same as there:

- `P` is a fibre product of `πX : X ⟶ Spec R` and `πY : Y ⟶ Spec R`, with projections `p₁` and
  `p₂` (`hP : IsPullback p₁ p₂ πX πY`).
- The section algebras are compatible with `secHom` (`halgX`, `halgY`).
- `U : ι → X.Opens` is finite and its double intersections are affine (`hU`). The
  intersections of `V : κ → Y.Opens` are affine (`hV`).
- The product cover is `prodCover p₁ p₂ U V`.

`L l m` sends an ordered `(m+1)`-cochain on the product cover to an `m`-cochain on `V`. It is the
alternating sum, over the shuffle paths `(σ 0, b 0), …, (σ 0, b s), (σ 1, b s), …, (σ 1, b m)`,
of the slant by `l` on `(∏_σ Γ(X, U_σ)) ⊗ Γ(Y, V_b) ≅ ∏_σ Γ(P, p₁⁻¹ U_σ ⊓ p₂⁻¹ V_b)`.

## Family slant

- `tensorEquivFam` and `slantFam` generalize `tensorEquiv` and `slant` from the index type
  `Fin 2 → ι` to an arbitrary finite family `O` of affine opens. `slantFam f W hW` is the
  additive map `∏ₐ Γ(P, p₁⁻¹ O a ⊓ p₂⁻¹ W) → Γ(Y, W)`: invert the tensor bijection, then apply
  `f ⊗ id` and `lid`.
- `slantFam_tensorFam` and `slantFam_mul` (`p₁^* x * p₂^* y ↦ f x • y`) describe it on tensors.
- `slantFam_add_left` and `slantFam_smul_left` give linearity in the functional.
- `slantFam_map` is the naturality statement. Let `Φ` be an additive map of section families and
  `φ` a linear map of first-factor families, with `Φ(tensorFam (x ⊗ y)) = tensorFam (φ x ⊗ y)`.
  Then the slant of `Φ F` by `f` equals the slant of `F` by `f ∘ φ`.
- `slant_eq_slantFam` states that `slant` is `slantFam` for the family `σ ↦ inter U σ`. It holds
  by `rfl`.

## Columns and the differential

- `dZeroLin` is the `R`-linear Čech differential from zero-cochains `∏_{τ : Fin 1 → ι}` to
  one-cochains. `dZeroLin_apply` states that it agrees with `Cech.d … 0`.
- `colSec c b` is the column of a cochain `c` at `b`, namely the family
  `τ ↦ c((τ 0, b 0), …, (τ 0, b m))` restricted to `p₁⁻¹ U_τ ⊓ p₂⁻¹ V_b`.
- `colSlant f c` is the cochain `b ↦ slantFam f (colSec c b)`.
- `slant_dZero`: the slant by `l` of the family `σ ↦ G(σ 1) - G(σ 0)` is the family slant of `G`
  by `l ∘ dZeroLin`.
- `L_d_col`: for every functional `l`, with no normalization hypothesis,
  `L l (n+1) (d c) = colSlant (l ∘ dZeroLin) c - d (L l n c)`.
  The proof is the Library proof of `L_d`. That proof used its hypothesis `hl` only to kill
  the two boundary terms of the shuffle sum `shuffle_sum`. Here those two terms are kept and
  identified with the column slant by `slant_dZero`.

## The left-axis cup

- `cupZeroLin x` is the `R`-linear map `f ↦ x ∪ f` (`cup₁`) from zero-cochains to
  one-cochains of `U`. `cupZeroLin_apply` gives `(x ∪ f)(σ) = x σ * f(σ 1)|`.
- `leftMulCol x W` sends a column family `G` to `σ ↦ p₁^*(x σ) * G(σ 1)|`. By
  `slant_leftMulCol`, its slant by `l` is the family slant of `G` by `l ∘ cupZeroLin x`.
- `L_cup_pull_left`: let `x` be a one-cocycle (`d x = 0`) and `e` an arbitrary cochain on the
  product cover. Then `L l m (p₁^* x ∪ e) = colSlant (l ∘ cupZeroLin x) e`. In the shuffle sum
  every path with `s ≥ 1` begins with the edge `((σ 0, b 0), (σ 0, b 1))`, where `p₁^* x` takes
  the value `x(σ 0, σ 0)`. That value is `0` for a cocycle (`appLE_cocycle_const`). Only the
  path with `s = 0` remains, and its value is `p₁^*(x σ) * e((σ 1, b 0), …, (σ 1, b m))`.

## Evaluation at a rational point

Let `x₀ : Spec R ⟶ X` be a section (`x₀ ≫ πX = 𝟙`), and let `i₂ : Y ⟶ P` be the axis, with
`i₂ ≫ p₁ = πY ≫ x₀` and `i₂ ≫ p₂ = 𝟙`. Let `i₀` be an index with `⊤ ≤ x₀⁻¹ U i₀`.

- `evalCol` is the functional `f ↦ evalSec (f (fun _ => i₀))` on zero-cochains, where `evalSec`
  is evaluation at `x₀`.
- `axis_le_prodCover` states `V k ≤ i₂⁻¹ (p₁⁻¹ U i₀ ⊓ p₂⁻¹ V k)`.
- `colSlant_evalCol`: `colSlant evalCol e` is the Čech pullback `pull i₂ … (fun k => (i₀, k)) e`
  of `e` along `i₂`, with index map `k ↦ (i₀, k)`. The proof reduces to the Library lemma
  `appLE_axis₂_tensorFam`.

## The combined formula

- `L_zero_cochain`: `L l m 0 = 0`.
- `L_cup_pull_left_eq`. Hypotheses: `x` is a one-cocycle, `e` is an `(n+1)`-cocycle on the
  product cover, and `ν` is a functional with
  `l ∘ cupZeroLin x = l x • evalCol + ν ∘ dZeroLin`. Conclusion:
  `L l (n+1) (p₁^* x ∪ e) = l x • pull i₂ e + d (L ν n e)`, pointwise in `Γ(Y, V_b)`.
  The proof combines `L_cup_pull_left`, linearity of `slantFam` in the functional,
  `colSlant_evalCol`, and `L_d_col` for `ν` (here `d e = 0` and `L ν (n+1) 0 = 0`).
- `exists_comp_eq_of_ker_le`: over a field `K`, let `g` be a functional on `V` with
  `ker dd ≤ ker g` for a linear map `dd : V →ₗ W`. Then `g = ν ∘ dd` for some functional `ν`
  on `W`. The proof factors `g` through `V / ker dd ≅ range dd` and extends the result by
  `LinearMap.exists_extend`.
- `exists_eq_smul_one_of_dZeroLin_eq_zero`: assume `U` covers `X` and every global function
  comes from `R` (`secHom πX ⊤` surjective). Then a zero-cochain `f` with `dZeroLin f = 0` equals
  `r • 1` for some `r : R`. This is the Library lemma `exists_eq_smul_one_of_cechD_eq_zero`
  applied to the family `τ ↦ inter U τ`. `inter_pair_le` is a helper.
- `cupZeroLin_one` (`x ∪ 1 = x`) and `evalCol_one` (`evalCol 1 = 1`).
- `exists_dual_correction`: over a field `K`, with `U` covering and `secHom πX ⊤` surjective,
  every functional `l` and one-cochain `x` admit a `ν` with
  `l ∘ cupZeroLin x = l x • evalCol + ν ∘ dZeroLin`. The difference
  `l ∘ cupZeroLin x - l x • evalCol` vanishes on constants, hence on `ker dZeroLin`.

## Provenance

The module is derived and internal. It introduces no external theorem. It extends the Library
definitions `L`, `ev`, `slant`, `tensorFam`, `cup₁`, `pull`, `evalSec` and
`appLE_axis₂_tensorFam`. The proof of `L_d_col` is the Library proof of `L_d` with the two
boundary terms of `shuffle_sum` kept. The mathematics is the cochain-level slant computation
of the Künneth decomposition for a product: the slant of `p₁^* x ∪ e` by a dual `l` is
`l(x)` times the restriction of `e` to the axis `{x₀} × Y`, up to a coboundary.
