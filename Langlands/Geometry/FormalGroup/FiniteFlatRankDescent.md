# Descent of finite flat modules and multiplicativity of ranks

This module contains three commutative-algebra results used by the proof of
`Langlands.FormalGroup.ModuleLaw.Hom.FiniteKernelCompositionStatement` in
`Langlands.Geometry.FormalGroup.FiniteKernelComposition`. They are internal
helper lemmas, assembled from Mathlib's results on flat, finite and faithfully
flat modules. They are not quotations of numbered theorems from the literature.

## `finrank_quotient_tensor_eq_rankAtStalk`

Let `P` be a finite flat module over a commutative ring `F`, and let `Q` be a
maximal ideal of `F`. Then the dimension of the fibre `(F ⧸ Q) ⊗[F] P` over
the field `F ⧸ Q` equals `Module.rankAtStalk P` at the point `Q`.

Proof: `Module.rankAtStalk_eq` gives the rank as the dimension of the fibre
over the residue field `Q.ResidueField`. For a maximal ideal, the residue field
is a field extension of `F ⧸ Q`. The Lean proof cancels the base change
(`AlgebraTensorModule.cancelBaseChange`) and applies
`Module.finrank_baseChange` over that extension.

## `rankAtStalk_eq_mul_of_tower`

Let `R → L` be finite and flat, and let `C` be a finite flat `L`-module, also
viewed as an `R`-module through a scalar tower. Fix a prime `p` of `R`. Suppose
`Module.rankAtStalk C q = r` at every prime `q` of `L` lying over `p`. Then

`Module.rankAtStalk (R := R) C p = r * Module.rankAtStalk (R := R) L p`.

Proof: let `κ` be the residue field of `p`. The fibre ring `κ ⊗[R] L` is a
finite `κ`-algebra, hence Artinian. Each of its maximal ideals lies over a prime
of `L` over `p`, so by the previous lemma and `Module.rankAtStalk_baseChange`,
the finite flat `(κ ⊗[R] L)`-module `(κ ⊗[R] L) ⊗[L] C` has fibre dimension
`r` at every maximal ideal. Mathlib's `Module.nonempty_basis_of_flat_of_finrank_eq`
then gives a basis indexed by `Fin r`. Cancelling base change
(`Algebra.IsPushout.cancelBaseChange`) identifies `κ ⊗[R] C` with
`(κ ⊗[R] L)^r` as `κ`-vector spaces. Counting `κ`-dimensions gives the
product formula.

## `descent_of_tensor_equiv`

Let `R → L → B` be a scalar tower of commutative rings with `B` faithfully
flat over `L`. Let `C` be an `L`-module and `K` a finite flat `R`-module.
Suppose there is a `B`-linear equivalence `B ⊗[L] C ≃ B ⊗[R] K`. Then:

- `C` is finite and flat over `L`;
- for every prime `q` of `L`, `Module.rankAtStalk C q` equals the rank of `K`
  at the contracted prime `q.comap (algebraMap R L)`.

Proof: `B ⊗[R] K` is finite and flat over `B`, so `B ⊗[L] C` is too. Faithfully
flat descent then gives finiteness and flatness of `C`:
`Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` and
`Module.Flat.of_flat_tensorProduct`. For ranks, choose a prime `q'` of `B`
over `q`. Such a prime exists because `Spec B → Spec L` is surjective
(`PrimeSpectrum.comap_surjective_of_faithfullyFlat`). Then use invariance of
the stalk rank under base change and under the equivalence:
`Module.rankAtStalk_baseChange` and `Module.rankAtStalk_eq_of_equiv`.
