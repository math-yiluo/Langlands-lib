# The positive involution of the Hecke algebra of a compact open subgroup

Author: Worker 167. Module `Langlands.Shimura.LevelHeckeAlgebraInvolution`, namespace
`Langlands.Shimura.LevelHecke.LevelHeckeAlgebra`.

For an open subgroup `K` of a topological group `G`, the Library algebra
`LevelHeckeAlgebra ℂ K.toSubgroup` (module `Langlands.Shimura.LevelHeckeAlgebra`) is the
space of finitely supported `K`-invariant functions on `G ⧸ K` (the Hecke space
`ℂ[G/K]^K`), with the counting convolution
`(a * b)(z) = ∑_{q ∈ supp a} a(q) b((out q)⁻¹ z)` (Library `heckeMul_apply`) and unit the
indicator of the identity coset. This module equips it with the involution
`a*(gK) = conj(a(g⁻¹K))` and proves the facts needed to show that the Jacobson radical
vanishes when `G ⧸ K` is countable.

Provenance: this module is internal support for the bound `b ≤ c(G, K)` of Renard 2026,
VI.9.1 (route in `Langlands.Representation.Jacquet.CompressionSeparationBound`). The
involution and the positivity argument are the standard ones for Hecke algebras of
totally disconnected groups; the only cited source result is the unital separation lemma
of Renard 2026, Appendix B.III, used through the Library theorem
`Langlands.Renard.unitalSeparation`. With the counting convolution, the naive involution
is anti-multiplicative without any modular-function factor, so no unimodularity or Haar
measure is used.

## Declarations

* `coeffs K a : G ⧸ K →₀ ℂ`, the underlying function, with `ext_coeffs`, `coeffs_zero`,
  `coeffs_smul` and `coeffs_mk_mul` (left `K`-invariance), and `coeffs_out_inv_smul`
  (`b((out (hK))⁻¹ z) = b(h⁻¹ z)`, because `out (hK) ∈ hK`).
* `coeffs_mul_sum` and `coeffs_mul`: the convolution formula as a finite sum over
  `supp a` and as a `finsum` over all cosets; `support_mul_finite`.
* `involutionFun a z = conj(a((out z)⁻¹ K))`, and `involutionFun_mk`:
  `involutionFun a (gK) = conj(a(g⁻¹K))` for every representative `g` (left
  `K`-invariance of `a`).
* `finite_orbit` and `involutionFun_support_finite` (`K` compact): `K`-orbits on `G ⧸ K`
  are finite (Library `finite_heckeCosets`), and the support of `involutionFun a` lies in
  the finite union of the `K`-orbits of `(out q)⁻¹ K` for `q ∈ supp a`.
* `involution hK a`, the element of the Hecke algebra with coefficients `involutionFun a`;
  its `K`-invariance is `(k g)⁻¹ K = g⁻¹ K` for `k ∈ K`. Lemmas `coeffs_involution`,
  `coeffs_involution_mk`, `involution_involution` and `involution_zero`.
* `involution_mul`: `(a * b)* = b* * a*`. Proof: evaluate at `gK`, reindex the `finsum`
  by the permutation `hK ↦ g⁻¹hK` of `G ⧸ K`, and compare termwise: the term of
  `conj((a * b)(g⁻¹K))` at `g⁻¹hK` is `conj(a(g⁻¹hK)) · conj(b(h⁻¹K))`, which is
  `a*(h⁻¹gK) · b*(hK)`, the term of `(b* * a*)(gK)` at `hK` (after `coeffs_out_inv_smul`
  and `coeffs_involution_mk`; complex conjugation is multiplicative and the two factors
  commute).
* `involution_pow_of_involution_eq`: powers of a self-adjoint element are self-adjoint.
* `eq_zero_of_mul_involution_eq_zero` (positivity): the value of `a * a*` at the identity
  coset is `∑_{q ∈ supp a} |a(q)|²`, so `a * a* = 0` forces `a = 0`.
* `eq_zero_of_isNilpotent_of_involution_eq`: a self-adjoint nilpotent element vanishes.
  Strong induction on the nilpotency exponent `n`: for `n = m + 2`, the element
  `y^{⌊(m+1)/2⌋+1}` multiplied by its adjoint (itself) is a power of `y` of exponent at
  least `n`, hence zero; positivity makes it zero, which is a smaller exponent.
* `rank_le_aleph0`: if `G ⧸ K` is countable the Hecke algebra has rank at most `ℵ₀`, as a
  submodule of `G ⧸ K →₀ ℂ`.
* `eq_zero_of_forall_mem_isCoatom` (`K` compact, `G ⧸ K` countable): an element `b` lying
  in every maximal left ideal is zero. Proof: `y = b* b` lies in every maximal left ideal
  and is self-adjoint. If `y` were not nilpotent, `unitalSeparation` (countable rank)
  would give a maximal left ideal `I` with `y · (1 mod I) ≠ 0`, contradicting `y ∈ I`.
  So `y` is nilpotent, hence `y = 0`; positivity applied to `b*` gives `b* = 0`, and
  `b = b** = 0`.
