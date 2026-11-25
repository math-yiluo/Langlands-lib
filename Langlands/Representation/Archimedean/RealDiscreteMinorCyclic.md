# Lie cyclicity through products of bottom minors

Lean module: `Langlands.Representation.Archimedean.RealDiscreteMinorCyclic`, part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). All declarations are in the namespace
`Langlands.Archimedean.RealDiscreteMinorCyclic`.

## Purpose and provenance

The module proves no statement of record. It generalizes the single-minor argument
`RealTiedMinorProduct.eq_top_of_sphCyclic` (Library, `RealTiedMinorProduct`; after Wallach
1971, Theorem 3.2, see `RealTiedMinorProduct.md`) from one minor to a product of `N` minors.
All declarations are internal. It reuses from `RealTiedMinorProduct` and `RealTiedMinorScalar`
(Library): the minor functions `minorG A B g = det g_{A,B}`, bottom segments `IsBottom`, their
transformation under the upper triangular group (`minorG_borel_mul`), the right derivatives of
minors (`rightDerivative_minorG`), principal lists `IsPrincipal` and the description `mem_KF_iff`
of the `O(n)`-finite vectors of a principal series.

## Notation

* `R, C : Fin N → Finset (Fin n)`: row and column sets of `N` minors.
* `prodG R C g = ∏_j det g_{R_j, C_j}` on `GL_n(ℝ)`.
* `rowWeight R a = ∏_j ∏_{i ∈ R_j} a_i` for `a ∈ (ℝˣ)ⁿ`.
* `IsMinorShift n ps qs R` (structure): `ps` and `qs` are principal (`IsPrincipal`: lists of
  characters, no induction blocks), every `R_j` is a bottom segment, and the principal-series
  characters satisfy `χ_qs(a) = χ_ps(a) · rowWeight R a` for all `a`.
* `KF n ds`: the `O(n)`-finite vectors of `realStandardModule n ds`.

## Declarations

* `prodG`, `contMDiff_prodG`, `prodG_mem_kFiniteVectors`: `prodG R C` is smooth and
  `O(n)`-finite, as a finite product of polynomial functions of the matrix entries.
* `prodG_borel_mul`: for bottom segments `R_j`,
  `prodG R C (diag(a) · u · g) = rowWeight R a · prodG R C g` for `u` upper unipotent (product
  of the Library `minorG_borel_mul`).
* `rowWeight_sign_sq`: `rowWeight` of a sign vector squares to `1`.
* `rightDerivative_prodG_mem`: the right derivative of `prodG R C` along any `X` lies in the
  span of the functions `prodG R C'` with the same rows. Proof by induction on `N`, writing
  `prodG` over `Fin (N+1)` as a product of the first minor and the rest (`Fin.prod_univ_succ`);
  the derivative of a product is a sum of two products, and the derivative of one minor is a
  combination of minors with the same rows (Library `rightDerivative_minorG`).
* `mul_prodG_mem`, `mulProd`: under `IsMinorShift`, `h ↦ h · prodG R C` maps `KF n ps` into
  `KF n qs` (a linear map `mulProd hsh C`). The character condition `char` gives the
  left-equivariance; `O(n)`-finiteness and smoothness come from those of the factors.
* `mulProd_lie_mem` (**product rule**): if `W ⊆ KF n qs` contains every `mulProd hsh D h` and the
  Lie derivative of `mulProd hsh C h`, then it contains `mulProd hsh C (X · h)`. Indeed
  `prodG · (X h) = X(prodG · h) − h · X(prodG)`, and `h · X(prodG)` is a combination of the
  `mulProd hsh D h` by `rightDerivative_prodG_mem`.
* `pullback hsh W = {h : ∀ C, mulProd hsh C h ∈ W}` and `pullback_lie`: if `W` is stable under
  the Lie algebra, so is its pullback (complexify `Z = Σ c ⊗ X` and use `mulProd_lie_mem`).
* `coefP`, `coefVecP`: for `f ∈ KF n qs`, `coefVecP hsh f C ∈ KF n ps` is the vector whose
  restriction to `O(n)` is `κ ↦ f(κ) · prodG R C κ`, extended to `GL_n(ℝ)` by the Library
  `extension` of `ps` (`coefP_mem`; the sign condition of a principal series on `O(n)` follows
  from `coefP_signDiagonal` and `rowWeight_sign_sq`).
* `sum_minorG_sq`, `sum_prodG_sq`: on `O(n)`, `Σ_D det(κ_{A,D})² = 1` for every row set `A`
  (the Library lemma `sum_minor_sq`, a sum over column sets of size `|A|`; the terms
  with `|D| ≠ |A|` are zero), hence `Σ_C prodG R C κ ² = 1` (product over `j`).
* `sum_mulProd_coefVecP` (**spanning**): `Σ_C mulProd hsh C (coefVecP hsh f C) = f`. Both sides
  lie in the principal series of `qs` and agree on `O(n)` by `sum_prodG_sq`; the Library lemma
  `eq_of_eqOn_unitaryCompact_of_mem_principalSeries` concludes.
* `eq_top_of_cyclic` (**product reduction**). If `T ∈ KF n ps` generates `KF n ps` under the
  Lie algebra, then every Lie-stable subspace `W ⊆ KF n qs` containing all `mulProd hsh C T`
  is `⊤`. Proof: `pullback hsh W` is Lie-stable and contains `T`, so it is `⊤`. Hence every
  `coefVecP hsh f C` lies in it, and `f = Σ_C mulProd hsh C (coefVecP hsh f C) ∈ W`.
