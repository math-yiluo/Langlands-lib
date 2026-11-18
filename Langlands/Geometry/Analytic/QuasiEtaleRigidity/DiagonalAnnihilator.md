# The diagonal trick for an annihilator of the Kähler differentials

Author: Worker 931.

This is a helper module of the proof of
`Langlands.Analytic.SaturatedAtlasPresentation.QuasiEtaleLiftCompatibilityStatement`
(`QuasiEtaleLiftCompatibilityProof`). It is pure commutative algebra over
arbitrary commutative rings `R → S`, with no analytic input. It is an internal
ingredient of the algebraic core of Berkovich's Key Lemma 7.2 (Berkovich,
*Vanishing cycles for formal schemes*, 1994, §7). Berkovich proves that lemma
with a generalized Krasner lemma (his Lemma 7.3). The route here is different,
and the module itself does not cite the source.

Write `J = KaehlerDifferential.ideal R S` for the kernel of the multiplication
map `S ⊗[R] S → S`, so that `Ω[S⁄R] = J/J²`.

- `ideal_eq_span_of_adjoin_eq_top`: if a finite set `G` generates `S` as an
  `R`-algebra, then `J` is spanned by the elements `1 ⊗ g - g ⊗ 1` for `g ∈ G`
  (`diagonalGenerator`). The proof follows Mathlib's `KaehlerDifferential.ideal_fg`:
  the two inclusions `S → S ⊗[R] S ⧸ I` agree on `G`, hence everywhere.
- `mul_mem_sq_of_mem_annihilator`: if `e` kills `Ω[S⁄R]`, then `(e ⊗ 1) x ∈ J²`
  for every `x ∈ J`. Here `S` acts on `Ω[S⁄R]` through `s ↦ s ⊗ 1`, and
  `Ideal.toCotangent_eq_zero` is applied.
- `exists_diagonal_annihilator`: for such `G` and `e` there are `n` and
  coefficients `c_g ∈ S ⊗[R] S` such that
  `t = (e ⊗ 1)ⁿ + ∑_g c_g (1 ⊗ g - g ⊗ 1)` kills `J`. Proof: multiplication by
  `e ⊗ 1` maps the finitely generated module `J` into `J • J`. Mathlib's
  Cayley–Hamilton theorem
  (`LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero`)
  gives a monic `p` of degree `n` whose `k`-th coefficient lies in `J^(n-k)`,
  with `p(e ⊗ 1) J = 0`. The non-leading part of `p(e ⊗ 1)` lies in `J`, so it
  is a combination of the generators.
- `eq_of_isUnit_image`: let `φ₁ φ₂ : S → C` be ring maps agreeing on `R`, and
  let `Ψ : S ⊗[R] S → C` satisfy `Ψ (a ⊗ b) = φ₁ a * φ₂ b`. If
  `φ₁ e ^ n + ∑_g Ψ(c_g) (φ₂ g - φ₁ g)`, which is `Ψ t`, is a unit, then
  `φ₁ = φ₂`. Indeed `Ψ t · (φ₂ s - φ₁ s) = Ψ (t (1 ⊗ s - s ⊗ 1)) = 0` for
  `s ∈ G`. Hence `φ₁` and `φ₂` agree on the generators, and therefore on `S`.
- `exists_tensorProduct_lift`: such a `Ψ` exists. It is
  `Algebra.TensorProduct.productMap` for the `R`-algebra structure on `C`
  induced by `φ₁`.
