# The elliptic loci are open in the regular loci

The module `Langlands.BaseChange.EllipticLocusClopen` (namespace `Langlands.BaseChange`)
proves the topological and conjugation-invariance facts about the regular elliptic set of
`GL_n(F)` and the σ-elliptic set of `GL_n(E)` that are needed to cut a test function off to
these sets. It carries out steps 1–3 of the proof idea in
`Langlands/BaseChange/EllipticTransferStatement.md`: ellipticity is read off the coefficients
of a characteristic polynomial, and by Krasner's lemma the factorization type of a separable
polynomial over a nonarchimedean local field does not change under small perturbations of its
coefficients. Everything here is derived from Mathlib and from the Library results named
below; the sets are those of Henniart–Lemaire 2011, II.1.2 (`G(F)_e` and `G(E)_{σ-e}`), in
characteristic zero, as explained in `Langlands/BaseChange/EllipticSupport.md`.

## Krasner neighbourhoods of polynomials

Let `K` and `L` be normed fields and `L` a normed `K`-algebra.

- `exists_pos_three_mul_le_norm_sub_rootSet f`: there is `r > 0` with `3 * r ≤ ‖a - a'‖`
  for any two distinct roots `a`, `a'` of `f` in `L` (`r` is the least of `1` and the
  distances between distinct roots divided by `3`).
- `exists_max_norm_one_le_rootSet f`: there is `B > 0` with `max ‖a‖ 1 ≤ B` for every root
  `a` of `f` in `L`.
- `exists_coeff_nhds_forall_root_near` (`L` algebraically closed): for monic `f` and `r > 0`
  there is `ε > 0` such that every monic `g` with `g.natDegree = f.natDegree` and
  `‖g.coeff i - f.coeff i‖ < ε` for all `i` has, for each root `a` of `f` in `L`, a root `b`
  with `‖a - b‖ < r`. The proof applies Mathlib's
  `exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt`, which gives
  `‖a - b‖ < ((d + 1) ε)^(1/d) · max ‖a‖ 1` for `d = f.natDegree > 0`, with
  `ε = (r / B)^d / (d + 1)`. (For `d = 0`, `f = 1` has no roots.)
- `exists_coeff_nhds_irreducible` (`L` algebraically closed, `IsKrasner K L`): a monic,
  separable, irreducible `f` has `ε > 0` such that every monic `g` as above is irreducible.
  Proof: take `r` from the first lemma, a root `a` of `f` and a root `b` of `g` with
  `‖a - b‖ < r`. Every conjugate `a' ≠ a` of `a` is a root of `f = minpoly K a`, so
  `‖a - b‖ < r < 3 * r ≤ ‖a - a'‖`, and Krasner's lemma (`IsKrasner.krasner`) gives
  `a ∈ K⟮b⟯`. Comparing degrees, `f.natDegree = [K⟮a⟯ : K] ≤ [K⟮b⟯ : K] = (minpoly K b).natDegree`,
  and `minpoly K b` divides the monic `g` of the same degree as `f`, so `g = minpoly K b` is
  irreducible.
- `exists_coeff_nhds_not_irreducible` (same hypotheses): a monic, separable, reducible `f`
  has `ε > 0` such that every monic `g` as above is reducible. Proof: suppose `g`
  irreducible. Choose for each root `a` of `f` a root `ψ a` of `g` with `‖a - ψ a‖ < r`; `ψ` is
  injective because the roots of `f` are `3r`-separated. Since `f` is separable it has
  `f.natDegree` distinct roots (`card_rootSet_eq_natDegree`), and `g` has at most
  `g.natDegree = f.natDegree`, so `ψ` is bijective and `g` is separable
  (`card_rootSet_eq_natDegree_iff_of_splits`). For a root `a₀` of `f` put `b = ψ a₀`, so that
  `g = minpoly K b`. Every conjugate `x ≠ b` of `b` is `ψ a'` with `a' ≠ a₀`, and
  `‖b - x‖ ≥ ‖a₀ - a'‖ - ‖a₀ - b‖ - ‖a' - x‖ > 3r - r - r = r > ‖b - a₀‖`. Krasner's lemma gives
  `b ∈ K⟮a₀⟯`, so `f.natDegree = g.natDegree ≤ (minpoly K a₀).natDegree`; as `minpoly K a₀`
  divides `f`, `f = minpoly K a₀` is irreducible, a contradiction.

## The coefficient space

`polynomialOfCoefficients b = X ^ n + ∑ i, C (b i) * X ^ i` is the monic polynomial with lower
coefficients `b : Fin n → R` (`Langlands.BaseChange.RegularOrbitParameters`).

- `coeff_polynomialOfCoefficients_sub`: the `k`-th coefficient of
  `polynomialOfCoefficients b - polynomialOfCoefficients b'` is `b k - b' k` for `k < n` and
  `0` otherwise.
- `setOf_mem_nhds_of_coeff_nhds`: let `F` be a nonarchimedean local field and use the norm
  `LocalGalois.localNormedField F`, whose topology is the given topology of `F`
  (`LocalGalois.localNormedField_topology`, by `rfl`). If a property `P` holds for every monic
  `g` of degree `n` whose coefficients are `ε`-close to those of `polynomialOfCoefficients b₀`,
  then `{b | P (polynomialOfCoefficients b)}` is a neighbourhood of `b₀`.
- `isOpen_separable_irreducible_polynomialOfCoefficients` and
  `isOpen_separable_not_irreducible_polynomialOfCoefficients` (`F` of characteristic zero):
  the sets `{b | (polynomialOfCoefficients b).Separable ∧ Irreducible (polynomialOfCoefficients b)}`
  and `{b | (polynomialOfCoefficients b).Separable ∧ ¬ Irreducible (polynomialOfCoefficients b)}`
  are open in `Fin n → F`. Each is the intersection of the open separable set
  (`isOpen_separable_polynomialOfCoefficients`) with a set that is a neighbourhood of each of
  its separable points by the two Krasner lemmas above, applied with
  `L = AlgebraicClosure F` carrying the spectral norm (`spectralNorm.nontriviallyNormedField`,
  `spectralNorm.normedAlgebra`). `F` is complete and ultrametric for its norm
  (`LocalGalois.localNormedField_complete`, `LocalGalois.localNormedField_ultrametric`), so
  `IsKrasner F (AlgebraicClosure F)` is Mathlib's instance `IsKrasner.of_completeSpace`.

## The general linear groups

Here `coefficients γ` are the lower coefficients of the characteristic polynomial of
`γ ∈ GL_n(F)` (`SigmaLiftCharacterIdentity.coefficients`), and for a cyclic algebra
`h : IsCyclicAlgebra σ l`, `normCoefficients h δ` are those of an element of `GL_n(F)`
associated with `δ ∈ GL_n(E)` (`Langlands.BaseChange.RegularOrbitParameters`).

- `isRegularElliptic_iff_coefficients`: `IsRegularElliptic γ` iff
  `polynomialOfCoefficients (coefficients γ)` is separable and irreducible
  (it is the characteristic polynomial, `polynomialOfCoefficients_coefficients`).
- `isSigmaElliptic_iff_normCoefficients`: `IsSigmaElliptic σ l δ` iff
  `polynomialOfCoefficients (normCoefficients h δ)` is separable and irreducible. If `δ` is
  associated with a regular elliptic `γ`, then `normCoefficients h δ = coefficients γ`
  (`normCoefficients_eq_of_associated`). Conversely, separability makes `δ` σ-regular
  (`isSigmaRegular_iff_separable_normCoefficients`), so `δ` is associated with some `γ`, whose
  characteristic polynomial is then separable and irreducible.
- `isRegularSemisimple_and_not_isRegularElliptic_iff_coefficients` and
  `isSigmaRegular_and_not_isSigmaElliptic_iff_normCoefficients`: the regular non-elliptic
  (resp. σ-regular non-σ-elliptic) elements are those whose polynomial is separable and
  reducible, by the previous lemmas and `isRegularSemisimple_iff_separable_coefficients`,
  `isSigmaRegular_iff_separable_normCoefficients`.
- `isRegularElliptic_conj_iff`: `IsRegularElliptic (x⁻¹ * γ * x) ↔ IsRegularElliptic γ`
  (`coefficients_conj`). `isSigmaElliptic_twistedConj_iff`:
  `IsSigmaElliptic σ l (x⁻¹ * δ * entrywiseAut σ n x) ↔ IsSigmaElliptic σ l δ`
  (`normCoefficients_twistedConj`).
- `isSigmaElliptic_iff_of_isNormAssociated`: if `δ` is associated with `γ`, then `δ` is
  σ-elliptic iff `γ` is regular elliptic (`normCoefficients_eq_of_associated`).
- For a nonarchimedean local field `F` of characteristic zero and `E` with
  `IsModuleTopology F E`: `isOpen_setOf_isRegularSemisimple_and_not_isRegularElliptic`,
  `isOpen_setOf_isSigmaElliptic` and `isOpen_setOf_isSigmaRegular_and_not_isSigmaElliptic`
  state that these three sets are open. They are preimages of the open coefficient sets above
  under the continuous maps `coefficients` (`continuous_coefficients`) and
  `normCoefficients h` (`continuous_normCoefficients`).

The openness of the regular elliptic set of `GL_n(F)` itself is `isOpen_regularElliptic` in
`Langlands.BaseChange.RegularEllipticOpen`, proved there by another argument.
