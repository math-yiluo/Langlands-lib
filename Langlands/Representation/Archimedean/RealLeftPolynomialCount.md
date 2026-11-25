# Counting `U(𝔤)` modulo a Borel-shifted right ideal and along `Ad(N̄)`

Module `Langlands.Representation.Archimedean.RealLeftPolynomialCount`, namespace
`Langlands.Archimedean.LeftPolynomialCount`. Purely algebraic.

Notation: `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`, `U = U(𝔤)`, `U_d = degreeFiltration ℂ 𝔤 d`. Positions are pairs
`c = (i, j)` of `Fin n × Fin n`. Upper means `i ≤ j`, lower means `j < i`. `N = |LowIdx n|` is the
number of lower positions (module `RealLowerUnipotentRestriction`).

## Definitions

* `stdBasis n`: the basis `c ↦ 1 ⊗ E_c` of `𝔤` (`Algebra.TensorProduct.basis` of
  `Matrix.stdBasis`). `stdBasis_apply`. `gen c = ι(1 ⊗ E_c)` in `U`.
* `upList n`, `lowList c₀`, `orderList c₀ = upList n ++ c₀ :: lowList c₀`. These are the upper
  positions, then `c₀`, then the lower positions other than `c₀`. `orderList_nodup` (for lower
  `c₀`) and `mem_orderList`: it lists every position exactly once.
* `J μ c₀ k`, for `μ : Fin n × Fin n → ℂ`, a position `c₀` and `k : ℕ`: the complex span of the
  elements `(gen c - μ_c) z` (`c` upper, `z ∈ U`) and `gen c₀ ^ k · z` (`z ∈ U`).
* `spanFamily μ c₀ k d`: the classes in `U / J` of `gen c₀ ^ j · ∏_{c ∈ lowList c₀} gen c ^ (γ c)`,
  indexed by `j < k` and `γ` with values `≤ d`.
* `mono β`, for `β : LowIdx n → ℕ`: the monomial `v ↦ ∏_c v_c^(β c)` on `LowIdx n → ℝ`.
* `polyR n D`: the real span of the monomials of total degree `≤ D`.
* `polyU n D d`: the complex span of the functions `v ↦ mono β v • w` with `∑ β ≤ D` and
  `w ∈ U_d`.
* `adMap μ c₀ k : U → ((LowIdx n → ℝ) → U / J)`, `u ↦ (v ↦ [adU (nbar v) u])`, where `adU` is
  `Ad` on `U` (module `RealSmoothRightAction`) and `nbar v` the lower unipotent element with
  coordinates `v`.
* `fullFamily μ k D d`: the functions `v ↦ mono β v • (spanFamily element)` with `β` of values
  `≤ D`.
* `lowIdxEquiv`: `LowIdx n ≃ Σ i : Fin n, Fin i`.

## Results

* `sub_mem_J`, `pow_mul_mem_J`: the generators lie in `J`.
* `word_mul_sub_mem_J`: for a list `l` of upper positions,
  `word(l) · z - (∏_{c ∈ l} μ_c) z ∈ J`.
* `word_append`, `word_replicate`, `word_expand`, `orderedMonomial_eq`: the ordered monomial of
  `α` for the order `orderList c₀` is `word(upper part) · gen c₀ ^ (α c₀) ·
  ∏_{c ∈ lowList c₀} gen c ^ (α c)`.
* `mkQ_orderedMonomial_mem`, `map_mkQ_le_span` (**count modulo `J`**): for lower `c₀`, the image
  of `U_d` in `U / J` lies in the span of `spanFamily μ c₀ k d`. That family has
  `k (d + 1)^|lowList c₀|` members.
* `mono_mem_polyR`, `const_mem_polyR`, `coord_mem_polyR`, `mono_mul`, `mul_mem_polyR`
  (degrees add), `prod_mem_polyR`, `det_mem_polyR` (a determinant of a matrix with entries in
  `polyR n 1` lies in `polyR n n`), `nbarMat_mem_polyR`, `adjugate_nbarMat_mem_polyR`,
  `conj_mem_polyR`: the entries of `nbarMat v · X · adjugate (nbarMat v)` lie in `polyR n (1 + n)`.
* `polyU_mono`, `smul_mem_polyU`, `mul_mem_polyU` (pointwise products: degrees add in both
  indices), `adU_ι_mem_polyU`, `algebraMap_mem_polyU`, `adU_mem_polyU`: for `u ∈ U_d`,
  `v ↦ adU (nbar v) u` lies in `polyU n ((1 + n) d) d`.
* `adMap_apply`, `mkQ_polyU_mem`, `finrank_map_adMap_le` (**count along `Ad(N̄)`**): for lower `c₀`,
  `dim adMap(U_d) ≤ ((1 + n) d + 1)^N · (k (d + 1)^|lowList c₀|)`.
* `card_lowIdx_mul_two`: `2N = n (n - 1)`. `length_lowList_add_one`: `|lowList c₀| + 1 = N` for
  lower `c₀`.

## Provenance

Internal, for the proof of `RealLeftPolynomialGrowthStatement`. The first part is a
Poincaré–Birkhoff–Witt style reduction with the Library's ordered monomials (module
`Kostant/OrderedMonomials`). The second part records that `Ad(n̄)` is polynomial in the
coordinates of `n̄`. No statement is taken from the literature.

## Proofs

* `word_mul_sub_mem_J`: induction on `l`. Write `gen c · (W z) - μ_c (∏ μ) z` as
  `(gen c · Wz - μ_c Wz) + μ_c (Wz - (∏ μ) z)`. The first term is a generator, the second lies in
  `J` by induction.
* `orderedMonomial_eq`: `expand (orderList c₀) α` is the concatenation of the expansions of the
  three pieces. `word` turns concatenation into products and replications into powers.
* `mkQ_orderedMonomial_mem`: by `word_mul_sub_mem_J`, the class of the ordered monomial is
  `(∏ μ)` times the class of `y = gen c₀ ^ (α c₀) · ∏ gen c ^ (α c)`. If `α c₀ ≥ k`, then
  `y = gen c₀ ^ k · (…) ∈ J`. Otherwise `y` is a member of `spanFamily`, since `α c ≤ deg α ≤ d`
  (`Finsupp.le_degree`).
* `map_mkQ_le_span`: `U_d` is spanned by the ordered monomials of degree `≤ d` for any order
  (Library `degreeFiltration_le_orderedSpan`). Apply the previous result.
* The `polyR` and `polyU` closure results are span inductions, using
  `mono β · mono β' = mono (β + β')` and `U_d U_{d'} ⊆ U_{d+d'}` (`mul_mem_degreeFiltration`).
  `det_mem_polyR` expands the determinant as `∑_σ sign σ ∏_i M_{σ(i) i}`. The adjugate entries
  are determinants of `nbarMat v` with one row replaced (`Matrix.adjugate_apply`).
* `adU_ι_mem_polyU`: `adU (nbar v) (ι(z ⊗ X)) = ι(z ⊗ M)` with
  `M = nbarMat v · X · adjugate (nbarMat v)` (`nbar_val`, `nbar_inv_val`). Write
  `M = ∑_{i,j} M_ij E_ij`, so this is `∑_{i,j} M_ij • ι(z ⊗ E_ij)`, and `conj_mem_polyR` applies.
  General `x ∈ 𝔤` follows by tensor induction.
* `adU_mem_polyU`: induction on `d`. `U_0 = ℂ · 1`, and `adU` fixes scalars. Every element of
  `U_{d+1} = U_d · (ℂ 1 + ι(𝔤))` is a sum of products `a b`. `adU` is multiplicative, so
  `mul_mem_polyU` applies with degree `(1 + n) d + (1 + n) = (1 + n)(d + 1)`.
* `mkQ_polyU_mem`: on a generator `v ↦ mono β v • w`, write the class of `w` as a combination of
  `spanFamily` (`map_mkQ_le_span`). Each exponent satisfies `β c ≤ D`.
* `finrank_map_adMap_le`: `adMap(U_d)` lies in the span of `fullFamily μ k ((1 + n) d) d`, whose
  index type has `((1 + n) d + 1)^N · k (d + 1)^|lowList c₀|` elements (`finrank_range_le_card`).
* `card_lowIdx_mul_two`: through `lowIdxEquiv`, `N = ∑_{i < n} i`, and
  `Finset.sum_range_id_mul_two` gives `2N = n (n - 1)`. `length_lowList_add_one`: the lower
  positions other than `c₀` are the lower positions with `c₀` erased.
