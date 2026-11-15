# `Langlands.CommutativeAlgebra.Popescu.PurelyInseparableTensorLocal`

Helper lemmas for the proof of
`Langlands.CommutativeAlgebra.Popescu.GeometricRegularityKaehlerInjectiveStatement`
(Stacks, More on Algebra, Proposition 15.36.1 (07E5), implication (1) ⇒ (4)). That proof passes
from a geometrically regular algebra `Λ` over a field `k` of characteristic `p` and a prime `q` of
`Λ` to the base change `A' = Λ_q ⊗[k] k'` along a finite purely inseparable extension `k'/k`. It
needs three facts: `A'` is local, `A'` is regular local, and `dim A' ≤ dim Λ_q`. These are
internal helper results with standard proofs, given below. They are formulated with `Λ_q` on the
left, so that Mathlib's default instance `Algebra.TensorProduct.leftAlgebra` makes `A'` a
`Λ_q`-algebra; this is the form in which `FaltingsMain` and
`GeometricRegularityKaehlerInjectiveProof` use them.

All declarations live in the namespace `Langlands.CommutativeAlgebra.Popescu.Faltings`.

## Generic statements (any `k`-algebra `A`)

Here `k` and `k'` are fields, `k'/k` is purely inseparable (`IsPurelyInseparable k k'`, finiteness
not needed), and `A` is a commutative `k`-algebra.

- `exists_pow_eq_algebraMap (p) [ExpChar k p] [Nontrivial A] (z : A ⊗[k] k')`: there are `n` and
  `a : A` with `z ^ p ^ n = algebraMap A (A ⊗[k] k') a`.
- `isLocalRing_tensor [IsLocalRing A] : IsLocalRing (A ⊗[k] k')`.
- `isIntegral_tensor [Nontrivial A] : Algebra.IsIntegral A (A ⊗[k] k')`.
- `ringKrullDim_tensor_le [Nontrivial A] : ringKrullDim (A ⊗[k] k') ≤ ringKrullDim A`.
- `isRegularRing_of_isLocalization (M : Submonoid R) [IsLocalization M S] [IsRegularRing R] :
  IsRegularRing S`: a localization of a regular ring is regular.

## Statements at a prime of a geometrically regular algebra

Here `k k' : Type u`, `Λ : Type v`, `q` is a prime of `Λ`, and `IsPurelyInseparable k k'` holds.

- `isLocalization_tensor_atPrime`: `k' ⊗[k] Λ_q` is the localization of `k' ⊗[k] Λ` at the image
  of `Λ \ q` under `includeRight`. The algebra structure is `map id (Λ → Λ_q)`. This lemma does not
  use pure inseparability.
- `isLocalRing_tensor_atPrime : IsLocalRing (Localization.AtPrime q ⊗[k] k')` ((L3)(i)).
- `isRegularLocalRing_tensor_atPrime [FiniteDimensional k k'] (hΛ : GeometricallyRegular k Λ) :
  IsRegularLocalRing (Localization.AtPrime q ⊗[k] k')` ((L3)(ii)).
- `ringKrullDim_tensor_atPrime_le : ringKrullDim (Localization.AtPrime q ⊗[k] k') ≤
  ringKrullDim (Localization.AtPrime q)` ((L3)(iii)).

## Proofs

- `exists_pow_eq_algebraMap`: `A ⊗[k] k'` is nontrivial, because `includeLeft` is injective (`k'`
  is free over `k`, and `A` is flat over the field `k`). Hence `k → A ⊗[k] k'` is injective and
  `A ⊗[k] k'` has exponential characteristic `p`. Induct on the tensor. For `a ⊗ x`, pure
  inseparability gives `x ^ p ^ n = algebraMap k k' c`, and
  `(a ⊗ x) ^ p ^ n = a ^ p ^ n ⊗ (c • 1) = (c • a ^ p ^ n) ⊗ 1`. For a sum `z + w` with
  `z ^ p ^ n = a ⊗ 1` and `w ^ p ^ m = b ⊗ 1`, the Frobenius identity `add_pow_expChar_pow` gives
  `(z + w) ^ p ^ (n + m) = (a ^ p ^ m + b ^ p ^ n) ⊗ 1`.
- `isLocalRing_tensor`: let `p` be the exponential characteristic of `k` (`ExpChar.exists`). For
  `z` in the ring, take `z ^ p ^ n = a ⊗ 1`. Then `(1 - z) ^ p ^ n = (1 - a) ⊗ 1` by
  `sub_pow_expChar_pow`. One of `a` and `1 - a` is a unit in the local ring `A`, so one of
  `z ^ p ^ n` and `(1 - z) ^ p ^ n` is a unit, and therefore so is `z` or `1 - z`
  (`isUnit_pow_iff`, `p ^ n ≠ 0`). Conclude with `IsLocalRing.of_isUnit_or_isUnit_one_sub_self`.
- `isIntegral_tensor`: `z` is a root of the monic polynomial `X ^ p ^ n - C a`.
- `ringKrullDim_tensor_le`: the Library lemma
  `Langlands.GroupScheme.FiniteFieldTorsorPoint.ringKrullDim_le_of_isIntegral` applied to
  `isIntegral_tensor`.
- `isRegularRing_of_isLocalization`: `S` is Noetherian (`IsLocalization.isNoetherianRing`). For a
  prime `P` of `S`, `S_P` is the localization of `R` at `P ∩ R`
  (`IsLocalization.isLocalization_isLocalization_atPrime_isLocalization`). So it is isomorphic to
  `R_{P ∩ R}` (`IsLocalization.algEquiv`), which is regular local, and
  `IsRegularLocalRing.of_ringEquiv` transports this.
- `isLocalization_tensor_atPrime`: Mathlib's `IsLocalization.tensorProduct_tensorProduct_right`
  with the algebra structure and the scalar tower used in Mathlib's
  `IsLocalization.tensorProductEquivOfMapIncludeRight`.
- `isLocalRing_tensor_atPrime` and `ringKrullDim_tensor_atPrime_le`: the generic lemmas with
  `A = Λ_q`.
- `isRegularLocalRing_tensor_atPrime`: `k' ⊗[k] Λ` is regular by the definition of
  `GeometricallyRegular` (`hΛ.2 k'`), so its localization `k' ⊗[k] Λ_q` is regular
  (`isLocalization_tensor_atPrime`, `isRegularRing_of_isLocalization`). It is local, being
  isomorphic to `Λ_q ⊗[k] k'` through `Algebra.TensorProduct.comm`. Mathlib's
  `IsRegularLocalRing.of_isRegularRing_of_isLocalRing` then makes it regular local. Transport
  along `Algebra.TensorProduct.comm` gives the claim for `Λ_q ⊗[k] k'`.
