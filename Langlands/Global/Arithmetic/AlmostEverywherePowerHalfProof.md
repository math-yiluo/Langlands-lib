# Proof that almost-everywhere local powers imply global half-powers

Authors: Worker 1244 and Worker 384.

The theorem `Langlands.Global.almostEverywherePowerHalfStatement.{u}` proves the
unchanged proposition `Langlands.Global.AlmostEverywherePowerHalfStatement.{u}`
from `Langlands.Global.Arithmetic.AlmostEverywherePowerHalfStatement`. For every
number field `K : Type u`, finite set `S` of finite places, positive natural `n`,
and `a : Kˣ`, if the image of `a` is a `(2 * n)`-th power in the units of every
finite completion outside `S`, then `a = b ^ n` for some `b : Kˣ`. Only the
standard axioms `propext`, `Classical.choice` and `Quot.sound` are used.

The mathematics is Artin and Tate, *Class Field Theory* (2009), Chapter IX,
Section 1, Theorem 1 and its proof, printed pp.65–66 (PDF pp.74–75), registered
as `artin-tate-2009-class-field-theory`. The Lean route is described in the
paired Markdown of the helper modules; this file records only the final
assembly.

## Helper modules

- `Langlands.Global.Arithmetic.PowerDescent` (Worker 384): unit/field root
  conversion, coprime-exponent assembly, norm descent, and the reduction
  `almostEverywherePowerHalf_of_prime_powers` of the target to positive
  prime-power exponents.
- `Langlands.Global.Arithmetic.CyclotomicPrimePowerGalois` (Worker 384, with
  Worker 1244's plan): degrees of cyclotomic extensions divide the totient, and
  `ℓ ^ (n + k)`-cyclotomic extensions of a field containing a primitive
  `ℓ ^ k`-th root are cyclic of `ℓ`-power degree when `k ≠ 0` and
  `k + 2 ≤ ℓ * k`.
- `Langlands.Global.Arithmetic.LocalPowerDescent` (Worker 1244): the Kummer,
  cyclic-descent, odd-prime and 2-power steps. It uses the published proofs
  `Langlands.Global.cyclicNonsplitPrimeStatement` and
  `Langlands.Global.cyclicPrimePowerLocalDegreeStatement` and the published
  `Langlands.Global.Arithmetic.KummerRadical` lemmas.

## The proof

The proof applies `PowerDescent.almostEverywherePowerHalf_of_prime_powers`. It
remains to show, for every number field `K`, finite set `S`, prime `p`, positive
`r` and `a : Kˣ`, that local `(2 * p ^ r)`-th unit powers outside `S` give
`a = b ^ p ^ r` with `b : Kˣ`.

First the hypothesis is restated for field elements on the cofinite filter: the
complement of `S` is cofinite (`Finset.eventually_cofinite_notMem`), and the value
of a local unit root is a root of the image of `a` in the completion. By
`PowerDescent.exists_unit_pow_eq_iff`, it suffices to find `b ∈ K` with
`b ^ p ^ r = a`. Since `a` is a unit, `(a : K) ≠ 0`.

- If `p = 2`, write `r = s + 1`. Then `2 * 2 ^ (s + 1) = 2 ^ (s + 2)`, so
  `LocalPowerDescent.exists_pow_eq_of_eventually_twoPow` gives
  `b ^ 2 ^ (s + 1) = a`.
- If `p ≠ 2`, a local root `c` of exponent `2 * p ^ r` gives the local root
  `c ^ 2` of exponent `p ^ r`, and
  `LocalPowerDescent.exists_pow_eq_of_eventually_oddPrimePow` gives
  `b ^ p ^ r = a`.

The factor two in the local exponent is used only at the prime two. There it
pays for the norm descent from `K(√-1)`, which recovers `a` only up to sign.
