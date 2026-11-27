# A Cartan subalgebra through an integral grading element of a reductive Lie algebra

Module `Langlands.Algebra.ReductiveCartanData`, namespace
`Langlands.Algebra.ReductiveCartanData`.

`g` is a finite-dimensional complex Lie algebra. Reductive means `radical ℂ g = center ℂ g`
(Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §19.1).

## The complement of the centre

- `exists_isCompl_center`: the centre of a reductive `g` has a complementary Lie ideal `s`. This
  is the Library's complete reducibility theorem
  `WeylCompleteReducibility.exists_isCompl` for the adjoint module, on which the centre acts
  by `0`.
- `isCompl_toSubmodule`: the same as complementary subspaces.
- `eq_zero_of_killingForm`, `isKilling_complement`: the Killing form of `s` is nondegenerate
  (Mathlib's `LieAlgebra.IsKilling`). The Killing form of `s` is the restriction of that of `g`
  (`LieIdeal.killingForm_eq`). An `x ∈ s` orthogonal to `s` is orthogonal to the centre
  (`WeylCompleteReducibility.center_le_killingCompl_top`), hence lies in the Killing radical,
  which is contained in the solvable radical (Mathlib's `killingCompl_top_le_radical`, Cartan's
  criterion), that is in the centre; so `x = 0`.

## Cartan subalgebras through a given element

- `apply_eq_zero_of_pow_apply_eq_zero`: an endomorphism diagonal in some basis kills every
  vector killed by one of its powers.
- `exists_isCartanSubalgebra_mem`: if `ad x₀` kills every vector killed by a power of `ad x₀`,
  some Cartan subalgebra contains `x₀`. Let `C` be the Engel subalgebra of `x₀`, which is its
  centralizer. Mathlib's `LieAlgebra.exists_isCartanSubalgebra_engel` gives a Cartan subalgebra
  `𝔥_C` of `C`, an Engel subalgebra of some `x ∈ C`; it contains `x₀`. Its image `𝔥` in `L` is
  nilpotent. If `y` normalizes `𝔥`, then `⁅y, x₀⁆ ∈ C`, so `(ad x₀)² y = 0`, hence `y ∈ C`; then
  `y` normalizes `𝔥_C` in `C` and lies in it. So `𝔥` is self-normalizing.
- `ad_eq_zero_of_pow`: the hypothesis holds for an element `H` whose integral eigenvectors span
  `g`.

## Main theorem

`exists_cartanData`: for reductive `g` and `H` whose integral eigenvectors span `g`, there are

- a subspace `𝔥 ∋ H` with `⁅x, y⁆ = 0` for `x, y ∈ 𝔥`;
- a basis `b : Basis I ℂ g` and linear forms `wt i` on `𝔥` with `⁅h, b i⁆ = wt i h • b i`, such
  that `b i ∈ 𝔥` whenever `wt i = 0`;
- a nondegenerate symmetric invariant bilinear form `B` on `g`, nondegenerate on the centre.

Construction. Decompose `H = Hz + Hs` along `g = center ⊕ s`. The component `Hs` satisfies the
hypothesis of `exists_isCartanSubalgebra_mem` in `s`, giving a Cartan subalgebra `𝔥_s ∋ Hs` of
the Killing algebra `s`. Mathlib's theory of Killing algebras makes `𝔥_s` abelian
(`IsKilling.instIsLieAbelianOfIsCartanSubalgebra`), shows that its elements act on root spaces
by their roots (`IsKilling.lie_eq_smul_of_mem_rootSpace`), that the root spaces span `s`
(`LieModule.iSup_genWeightSpace_eq_top`), and that the zero root space is `𝔥_s`
(`rootSpace_zero_eq`). Put `𝔥 = center ⊕ 𝔥_s`. The common eigenvectors of `ad 𝔥` (the centre
and the root vectors of `s`) span `g`; a basis is extracted from them, and `wt i h` is read off
as the `i`-th coordinate of `⁅h, b i⁆`. A common eigenvector of weight `0` has its `s`-component
in the zero root space, hence in `𝔥`. The form is `B = κ + β`, where `κ` is the Killing form of
`g` and `β (x, y) = ∑ₐ fₐ(x) fₐ(y)` for the coordinates `fₐ` of the projection to the centre
along `s` in a basis of the centre. Invariance of `β` holds since brackets lie in `s`;
nondegeneracy combines the coordinates on the centre with the nondegeneracy of `κ` on `s`.

## Provenance

Internal assembly of the standard structure of reductive Lie algebras (decomposition into the
centre and a semisimple ideal, Cartan subalgebras, root decomposition) from Mathlib's Cartan
criterion, Engel subalgebras and Killing theory and the Library's complete reducibility theorem.
