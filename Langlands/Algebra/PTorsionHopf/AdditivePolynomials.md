# One-variable additive polynomials in prime characteristic

Author: Worker 1519, as internal infrastructure for the proof of
`Langlands.GroupScheme.RelativeRoot.SmoothCommutativePTorsionVectorStatement`.

Provenance: internal. These are standard facts about additive polynomials; the proofs are the
author's own. The degree computation uses Mathlib's Lucas-type lemma
`Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat`.

Throughout `k : Type u` is a field.

- `IsAdditivePoly f`: for every commutative `k`-algebra `R : Type u` and all `a b : R`,
  `aeval (a + b) f = aeval a f + aeval b f`. The quantification is over algebras in the
  universe of `k`.
- `IsAdditivePoly.sub`, `IsAdditivePoly.comp`: closure under differences and composition.
- `add_pow_char_pow_of_algebra p n a b`: in every commutative algebra over a field of
  characteristic `p`, `(a + b) ^ p ^ n = a ^ p ^ n + b ^ p ^ n` (trivial rings are handled
  separately; otherwise the algebra has characteristic `p`).
- `isAdditivePoly_C_mul_X_pow p c n`: `C c * X ^ p ^ n` is additive.
- `IsAdditivePoly.taylor_eq`: an additive `f` satisfies the two-variable identity
  `taylor X (f.map C) = f.map C + C f` in `k[X][X]`, i.e. `f(Y + X) = f(Y) + f(X)`.
- `IsAdditivePoly.natDegree_eq_pow p hf hf0` (**degrees of additive polynomials**): a
  nonzero additive polynomial over a field of characteristic `p` has positive degree, equal
  to a power of `p`.

  Proof as implemented. A nonzero constant is not additive. For `d = natDegree f` and
  `0 < i < d`, compare the coefficient of `Y ^ i X ^ (d - i)` in the two-variable identity:
  the left side gives `(d.choose i) * leadingCoeff f` through the Hasse derivative
  (`taylor_coeff`, `hasseDeriv_coeff`), the right side gives `0`. Hence `p ∣ d.choose i`
  for all such `i`, and the Lucas-type lemma gives `d = p ^ multiplicity p d`.
