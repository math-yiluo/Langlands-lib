# Restricted-product comparisons for actual rational Tate modules

This module proves exactly the published proposition
`Langlands.GroupScheme.Tate.PrimeComparison.RationalRestrictedProductComparisons G T`
from `Langlands.AbelianScheme.Tate.RestrictedProductStatement`.
Its main theorem is
`Langlands.GroupScheme.Tate.PrimeComparison.rationalRestrictedProductComparisons`.
The component theorems are `rationalRestrictedProductComparison` (the full
comparison) and `rationalAwayRestrictedProductComparison` (the away comparison
for each `m : ℕ`) in the same namespace.

The parameters are an arbitrary scheme `S : Scheme.{u}`, a group object
`G : Grp (Over S)` with `[IsCommMonObj G.X]`, and a test scheme `T : Over S`.
No finiteness, rank, characteristic or finite-étaleness hypothesis is added.
The away comparison is proved for every natural `m`, including `m = 0` and
`m = 1`, by the same argument.

## Provenance and inputs

This is an internal proof of the derived obligation recorded in
`RestrictedProductStatement.md`. That Markdown explains how the statement
relates to Harris–Taylor, Chapter I, printed p.18. The proof follows the
route sketched there: local `p`-torsion-freeness, localization at `p`, and a
global denominator. The statement and every module it imports are unchanged.

The proof imports two published theorems by name from
`Langlands.AbelianScheme.Tate.PrimeComparisonProof`:
`fullPrimeProductComparison G T` and `awayPrimeProductComparison G T m`.
Each supplies an additive equivalence whose underlying homomorphism is
`toPrimeProduct G T` or `toAwayPrimeProduct G T m`. This module only uses
the resulting bijectivity of these integral coordinate maps. It does not
re-prove the integral decomposition.

The carriers are the actual ones from the imported modules.
`Rational G T P` is `ℚ ⊗[ℤ] Integral G T P` with
`toRational G T P = x ↦ 1 ⊗ x`. `PrimeAdic.Rational G T p` is
`ℚ_[p] ⊗[ℤ_[p]] PrimeAdic.Integral G T p` with
`PrimeAdic.toRational G T p = x ↦ 1 ⊗ x`. The integral subgroups of the
restricted products are the images `PrimeAdic.integralImage G T p`.

## Local lemmas (namespace `Langlands.GroupScheme.Tate.PrimeAdic`)

Fix a prime `p` (as `[Fact p.Prime]`).

- `eq_zero_of_prime_nsmul_eq_zero`: if `p • z = 0` for
  `z : Integral G T p`, then `z = 0`. Coherence gives
  `z n = transition (z (n+1))`. By `toSection_transition_succ`, the
  section of this transition is `p` times the section of `z (n+1)`, which is
  the section of `(p • z) (n+1) = 0`. Injectivity of `toSection` then gives
  `z n = 0`.
- `eq_zero_of_prime_pow_nsmul_eq_zero`: the same holds for `p ^ k • z`, by
  induction on `k`.
- `eq_zero_of_smul_eq_zero`: a nonzero `c : ℤ_[p]` acts injectively.
  Write `c = u * p ^ k` with a unit `u` (`PadicInt.unitCoeff_spec`).
  Cancel the unit, then apply the previous lemma.
- `isLocalizedModule_toRational`: `PrimeAdic.toRational G T p` is a
  localization at `nonZeroDivisors ℤ_[p]`. This holds because the tensor
  product is a base change to the fraction field `ℚ_[p]`. The proof applies
  Mathlib's `isLocalizedModule_iff_isBaseChange` to
  `TensorProduct.isBaseChange`.
- `toRational_injective`: if `1 ⊗ x = 1 ⊗ y`, then localization gives a
  nonzero `c` with `c • x = c • y`. The previous lemma gives `x = y`.
- `exists_prime_pow_nsmul_mem_integralImage`: every
  `y : PrimeAdic.Rational G T p` has some `p ^ k • y` in the integral image.
  Localization gives `s • y = 1 ⊗ x` for a nonzero `s = u * p ^ k`.
  Then `p ^ k • y = 1 ⊗ (u⁻¹ • x)`.
- `isUnit_natCast_of_not_dvd`: a natural number `N` with `¬ p ∣ N` is a
  unit in `ℤ_[p]`. Its norm is not below `1`
  (`PadicInt.norm_int_lt_one_iff_dvd`), so it equals `1`.
- `mem_integralImage_of_nsmul_mem`: if `¬ p ∣ N` and `N • w` is integral,
  then `w` is integral. The proof multiplies by the inverse unit; the
  integral image is a `ℤ_[p]`-submodule.

## Global denominator

`exists_nsmul_eq_toRational` (namespace
`Langlands.GroupScheme.Tate.PrimeComparison`) states the following. Every
`v : Rational G T P` has a positive natural `N` and an integral `x` with
`N • v = toRational G T P x`. The proof is by induction on tensors
(`TensorProduct.inductionOn`). For `q ⊗ x`, take `N = q.den` and integral
element `q.num • x`, using `q * q.den = q.num`. For a sum, take the product
of the two denominators.

## Generic comparison over an indexed family of primes

The private part of the proof works over an arbitrary index type `I`. It
takes an injective map `π : I → Nat.Primes`, a predicate `P` with
`hP : ∀ i n, P (π i ^ n)`, and the coordinates
`rationalToPrime G T P (π i) (hP i)`.

1. `eventually_rationalToPrime_mem`: for each `v`, all but finitely many
   coordinates lie in the integral image. Take `N • v = toRational x` as
   above. If `π i` does not divide `N`, then `N` times the coordinate is
   `PrimeAdic.toRational (toPrime x)`, by `rationalToPrime_toRational`.
   That lies in the integral image, so the coordinate is integral by
   `mem_integralImage_of_nsmul_mem`. The exceptional indices satisfy
   `π i ∣ N`, so `π i ≤ N`. Injectivity of `π` makes this set finite.
2. `restrictedCoordinates`: the additive homomorphism
   `v ↦ (i ↦ rationalToPrime G T P (π i) (hP i) v)` into the restricted
   product over `I` with respect to `Filter.cofinite`.
3. Injectivity, assuming the integral coordinate map
   `x ↦ (i ↦ toPrime G T P (π i) (hP i) x)` is injective. If every
   coordinate of `v` vanishes, write `N • v = toRational x`. Then every
   `PrimeAdic.toRational (toPrime x)` vanishes, so every `toPrime x`
   vanishes by `toRational_injective`. Injectivity of the integral
   coordinate map gives `x = 0`. Hence `(N : ℚ) • v = 0`, so `v = 0`
   because `N ≠ 0`.
4. Surjectivity, assuming the integral coordinate map is surjective. Let
   `y` be a restricted family and `E` its finite set of non-integral
   indices (`Filter.eventually_cofinite`). Choose exponents `k i` with
   `π i ^ k i • y i` integral, and set
   `N = ∏ i ∈ E, π i ^ k i`. Then `N • y i` is integral for every `i`. For
   `i ∈ E` the factor `π i ^ k i` divides `N`. Outside `E`, `y i` is
   already integral. Choose `z i` with `PrimeAdic.toRational (z i) = N • y i`,
   and use surjectivity to get `x` with `toPrime x = z i` for all `i`. The
   preimage is `(N : ℚ)⁻¹ • toRational x`. Its coordinates are
   `(N : ℚ)⁻¹ • (N • y i) = y i`, because `rationalToPrime` is `ℚ`-linear.
5. `restrictedComparison`: if the integral coordinate map is bijective,
   then `AddEquiv.ofBijective restrictedCoordinates` has coordinate
   `rationalToPrime G T P (π i) (hP i) v` at every `v` and `i`, by `rfl`.

## The two instances

- Full: `I = Nat.Primes`, `π = fun p => p`, `P = fun _ => True`. Bijectivity
  of `toPrimeProduct G T` comes from `fullPrimeProductComparison G T`. The
  coordinate is definitionally `rationalFullToPrime G T p v`, and the target
  is definitionally `RationalRestrictedProduct G T`.
- Away at `m`: `I = AwayPrime m`, `π = Subtype.val`, and
  `P = fun n => Nat.Coprime n m` with `hP p n = p.property.pow_left n`.
  Bijectivity of `toAwayPrimeProduct G T m` comes from
  `awayPrimeProductComparison G T m`. The coordinate is definitionally
  `rationalAwayToPrime G T p.val m p.property v`. The target is
  `RationalAwayRestrictedProduct G T m`. For `m = 0` both sides are trivial,
  and the argument needs no special case.

`rationalRestrictedProductComparisons G T` is the pair of these results.

## Scope

The equivalences are additive only, exactly as the statement requires. The
module adds no rational scalar structure on the restricted products, no
topology or continuity, and no finite-adelic comparison. The development
check used only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
