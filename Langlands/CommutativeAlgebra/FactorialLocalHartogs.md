# Hartogs extension in factorial local domains

Author: Worker 171.

Module `Langlands.CommutativeAlgebra.FactorialLocalHartogs`, namespace
`Langlands.CommutativeAlgebra.FactorialLocalHartogs`. Throughout, `O` is a local
domain with `UniqueFactorizationMonoid O`.

- `exists_mem_maximalIdeal_not_dvd`: if `q` is a prime of `O` with `q ≠ ⊥` and
  `q ≠ maximalIdeal O`, then for every prime element `p` some element of the
  maximal ideal is not divisible by `p`. Proof: otherwise the maximal ideal lies in
  `(p)`; the nonzero prime `q` contains a prime element `r`
  (`Ideal.IsPrime.exists_mem_prime_of_ne_bot`), `p ∣ r` forces `p` and `r` to be
  associated, so `p ∈ q` and the maximal ideal would equal `q`.
- `exists_eq_of_forall_pow_mul`: under the same hypothesis on `q`, let `K` be a
  fraction field of `O` and `x : K`. If for every nonzero `f` in the maximal ideal
  some power `f ^ k` multiplies `x` into the image of `O`, then `x` lies in the image
  of `O`. Proof: write `x = a / b` in lowest terms
  (`IsFractionRing.exists_reduced_fraction`). If `b` is not a unit it has a prime
  factor `p`; choose `f` in the maximal ideal with `p ∤ f`. From
  `f ^ k * a = c * b` we get `p ∣ a`, contradicting coprimality.

The existence of a nonzero non-maximal prime is the algebraic form of "dimension at
least two" used later. This is a standard internal lemma (the factorial case of
algebraic Hartogs, compare EGA IV 21.12.7 as quoted in Lemma 3.4 of N. Guo,
arXiv 2209.02443v1, printed p.6, registered source
`guo-ample-sheaves-prufer-2209-02443-v1`); the proof above is self-contained and
uses only Mathlib.
