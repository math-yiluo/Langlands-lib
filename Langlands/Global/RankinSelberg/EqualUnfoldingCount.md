# The counting and fiber hypotheses for `GL_n` in the equal-rank unfolding

This is an internal helper module for `EqualUnfoldingReduction.md`. Provenance: internal. It
verifies the two hypotheses of the abstract fiber computation (`EqualUnfoldingFiber.md`) for
`H = GL_n(𝔸)`, `n = r + 1`, `Z = GL_1(𝔸) = 𝔸^×`, `σ = scalarPoint`, `Γ₁ = GL_1(F)` and
`P = P_n(F)`. It concludes the fiber computation that Cogdell, *Analytic theory of
L-functions for GL_n* (2004), §2.3, printed p.210, uses when he unfolds the Eisenstein series.
Namespace: `Langlands.Global.RankinSelbergGlobal.EqualUnfolding`. `|g|` stands for the Library's
`detNorm F n g`.

## The slab (`Determinant`)

- `detNorm_inv_eq`: `|g⁻¹| = |g|⁻¹`.
- `slabSet F n = {g | 1 ≤ |g| < e^n}` (`slabSet_eq_preimage`, `measurableSet_slabSet`). This is
  the preimage in `GL_n(𝔸)` of the Library's `determinantSlab F n 1 (Real.exp n)`, which
  normalizes `centralQuotientMeasure`.

## Cosets of `P'_n(F)` (`Cosets`)

- `eisensteinCosetRep F r q`: the chosen representative of `q ∈ P'_n(F) \ GL_n(F)` (the index
  set `LeftCosetSpace (eisensteinParabolic F r)` of the Library's Eisenstein series), as a
  point of `GL_n(𝔸)`. It lies in `GL_n(F)` (`eisensteinCosetRep_mem`).
- `rationalPoint_mem_eisensteinRationalImage_iff`, and `existsUnique_eisensteinCosetRep`: every
  `γ ∈ GL_n(F)` lies in exactly one coset `P'_n(F) γ_q`. `countable_eisensteinCosets` holds.
- `eisensteinDomain F r = D' = ⋃_q γ_q D`, with `D` the Library's chosen fundamental domain
  `LeftCosetSpace.fundamentalDomain` of `GL_n(F)`. It is measurable, and every `x` has exactly
  one `l ∈ P'_n(F)` with `l x ∈ D'` (`existsUnique_mem_eisensteinDomain`). So `D'` is a strict
  fundamental domain of `P'_n(F)`.

## The counting identity (`Counting`)

- `detNorm_scalarPoint_mul_inv_mul`: `|diag(b, …, b) p⁻¹ w| = |w|` for `b ∈ GL_1(F)` and
  `p ∈ P_n(F)`, by the product formula (`detNorm_of_mem_rationalSubgroup`).
- `tsum_indicator_eisensteinDomain`: for every set `T` of reals and every `w`,
  `Σ_{b ∈ GL_1(F)} Σ_{p ∈ P_n(F)} 1_{D' ∩ {|·| ∈ T}}(diag(b, …, b) p⁻¹ w) = 1_{|·| ∈ T}(w)`.
  Proof: the norm is unchanged, and by `existsUnique_mem_eisensteinDomain`,
  `exists_scalarPoint_mul_inv` and `scalarPoint_mul_inv_injective` exactly one pair `(b, p)`
  lands in `D'`. With `T = [1, e^n)` this is hypothesis `hcount` for `A = D' ∩ slabSet`.
- `setOf_scalarPoint_inv_mul_mem_slabSet`: `{z | diag(a, …, a)⁻¹ x ∈ slabSet}` is the band
  `{c < |a| ≤ e c}` with `c = exp(log|x| / n - 1) = |x|^{1/n} / e`.
- `measure_inter_scalarPoint_inv_mul_mem_slabSet`: if every band `{c < |a| ≤ e c}` of a set
  `D₁ ⊆ GL_1(𝔸)` has `ν`-measure one, then so does every slice in the previous item. This is
  hypothesis `hfiber`.

## The fiber computation (`Fiber`)

- Instances `countable_rationalSubgroup` and `countable_mirabolicRationalImage`.
- `ideleDomain F` and `mirabolicDomain F r`: the Library's chosen fundamental domains of `GL_1(F)`
  in `GL_1(𝔸)` and of `P_n(F)` in `GL_n(𝔸)`.
- `integrable_and_integral_slabFiber`: assume the band masses
  `hslab : ∀ c > 0, d^×a(ideleDomain F ∩ {c < |a| ≤ e c}) = 1`. Then for every measurable
  left `P_n(F)`-invariant `K` that is integrable on `mirabolicDomain F r`, the function
  `(x, a) ↦ K(diag(a, …, a) x)` is integrable on `(D' ∩ slabSet) × 𝔸^×` and has the same integral
  as `K` on `mirabolicDomain F r`. This is `integrable_and_integral_fiber` with the two
  hypotheses above. `hslab` itself is discharged in `EqualUnfoldingReduction` by the Library's
  `ideleMeasure_fundamentalDomain_Ioc` (module `EqualUnfoldingIdele`).
