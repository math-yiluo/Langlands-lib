# Termination of the smoothening sequence: graded independence from formal smoothness

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. It replaces the
regularity of the closure `Y` of the reduced integral points by the formal smoothness of its
coordinate ring. It uses Mathlib's `Algebra.FormallySmooth.liftOfSurjective` and
`MvPolynomial.funext`.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

- `Trunc k m = k[T]/(T^m)`. `truncMap n : Trunc k (n+2) → Trunc k 2` is surjective with nilpotent
  kernel (`truncMap_ker_nilpotent`).
- `firstOrder e l : E → Trunc k 2`, `y ↦ e y + l(dif e y) T`, is a `k`-algebra map for every linear
  form `l` on the cotangent module (it uses `dif_mul`).
- `psiMap e l n`: a lift of `firstOrder e l` to `Trunc k (n+2)`, given by formal smoothness of `E`.
  `psiMap_rep` gives representatives congruent to `e y + l(dy) T` modulo `T²`.
- `coeff_eq_zero_of_formallySmooth`: let `k` be infinite and `E` formally smooth with a point `e`.
  Let the `x j` lie in `ker e` with linearly independent differentials. If a homogeneous `P` of
  degree `n` has `P(x) ∈ (ker e)^(n+1)`, then every coefficient of `P` lies in `ker e`. Proof:
  for each `a ∈ k^t`, take `l` with `l(dx_j) = a_j` (`exists_functional`). The `n`-th coefficient
  of a representative of `psiMap (P(x))` is `(e P)(a)` and vanishes, so `e P = 0` by
  `MvPolynomial.funext`.
- `gradedIndep_of_formallySmooth`: the bridge to `GradedIndep ε ϖ x J`. Here `E` is a
  formally smooth algebra over the residue field, `π : C → E` is surjective with kernel `J`,
  `e ∘ π` is the reduction of `ε`, and the `x j` are independent modulo `J + I²` and `𝔪`.
