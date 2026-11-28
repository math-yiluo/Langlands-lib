# Central simple algebras with unitary involution at a nonsplit completion

Module: `Langlands.Algebra.CentralSimple.LandherrNonsplit`.

Setting: `E/F` a separable quadratic extension with `CharZero F`, `r = skewRoot F E`,
`d = skewSq F E` (module `Langlands.Algebra.CentralSimple.LandherrQuadraticData`), `B` a
finite-dimensional central simple `E`-algebra which is an `F`-algebra through `E`, and `K` a
field over `F` in which `d` is not a square (the instance
`Fact (¬ IsSquare (algebraMap F K d))`). Then `E ⊗_F K` is a field, and this module
replaces it by an explicit model.

- `nonsplitField F E K` denotes `QuadraticAlgebra K d 0`, using the image of `d` in `K`.
  The lemma `omega_mul_omega_nonsplit` says `ω² = d`. Under the nonsquare hypothesis
  this algebra is the field `K(√d)`.
- `nonsplitEmbedding : E →ₐ[F] K(√d)` sends `r` to `ω`; `nonsplitAlgebra` makes `K(√d)` an
  `E`-algebra through it, with `nonsplit_isScalarTower` (`F → E → K(√d)`) and
  `nonsplit_smulCommClass`.
- `nonsplitAlg F E B K = K(√d) ⊗_E B` and `nonsplitMap : K ⊗_F B →ₐ[K] K(√d) ⊗_E B`,
  `k ⊗ b ↦ k ⊗ b`. It is surjective (`nonsplitMap_surjective`: `K(√d)` is spanned over `K`
  by `1` and `ω`, the image of `r`), both sides have `K`-dimension `dim_F B`
  (`finrank_nonsplitAlg`), so it is bijective (`nonsplitMap_bijective`), giving the
  `K`-algebra isomorphism `nonsplitEquiv`; `nonsplitEquiv_tmul`,
  `nonsplitEquiv_tmul_skewRoot`, `nonsplitEquiv_tmul_one` and
  `nonsplitEquiv_symm_algebraMap` compute it on generators and scalars.
- `nonsplitConj` is the conjugation `x + yω ↦ x - yω` of `K(√d)` over `K`
  (`nonsplitConj_omega`, `nonsplitConj_ne_one`); `nonsplitConj_embedding` says that it
  restricts to `conjugation F E` on `E`.
- `nonsplitInvolution F E B K τ` transports `τ.baseChange K` to `K(√d) ⊗_E B` along
  `nonsplitEquiv` (`nonsplitInvolution_equiv`). If `τ` acts on `E` by the conjugation (the
  hypothesis `hτ`), `nonsplitInvolution_isUnitary` shows that it is a unitary involution of
  the central simple `K(√d)`-algebra `K(√d) ⊗_E B` relative to `nonsplitConj`
  (`IsUnitaryInvolution`, module `Langlands.Algebra.UnitaryInvolutionStatements`): it is
  additive, reverses products, is involutive, and acts on scalars by `nonsplitConj`, which is
  checked on `K` and on `ω`, the image of `r`.

## Provenance

This is the identification `K ⊗_F B ≅ (E ⊗_F K) ⊗_E B` with `E ⊗_F K ≅ K(√d)` at a place
which does not split in `E`, and the observation that `τ ⊗ id` is then an involution of the
second kind of a central simple algebra over the local quadratic extension; compare Platonov
and Rapinchuk, *Algebraic Groups and Number Theory* (1994), §6.7, and Kneser, *Lectures on
Galois Cohomology of Classical Groups* (1969), §5.5, where local unitary groups at nonsplit
places are treated through such algebras.
