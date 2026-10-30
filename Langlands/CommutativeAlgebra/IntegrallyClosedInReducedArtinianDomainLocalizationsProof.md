# Proof: prime localizations of rings integrally closed in reduced Artinian rings

This module proves the Library proposition
`Langlands.CommutativeAlgebra.IntegrallyClosedInReducedArtinianDomainLocalizations`
from `Langlands.CommutativeAlgebra.IntegrallyClosedInReducedArtinianDomainLocalizationsStatement`:

```lean
theorem integrallyClosedInReducedArtinianDomainLocalizations.{u, v} :
    IntegrallyClosedInReducedArtinianDomainLocalizations.{u, v}
```

That is, for arbitrary independent universes `u` and `v`, commutative rings
`R : Type u` and `B : Type v` with `[Algebra R B]`, if `IsIntegrallyClosedIn R B`,
`IsReduced B` and `IsArtinianRing B`, then for every prime ideal `p` of `R` the
localization `Localization.AtPrime p` is a domain. No hypotheses beyond the
statement's are used.

## Provenance

The argument is internally derived. It follows the idempotent step in the
proof of Stacks Project Lemma 10.37.16 (Tag 030C, registered source
`stacks-integral-closure-idempotent-generic-fiber-2026-10-28`): an idempotent of
a product of fields is integral over any subring because it is a root of
`X^2 - X`, so it lies in an integrally closed subring. The Stacks lemma is
about a reduced ring with finitely many minimal primes and its total ring of
fractions; here the total ring of fractions is replaced by an arbitrary
reduced Artinian algebra, and the conclusion is about prime localizations.

## Auxiliary lemmas

Both are in the namespace
`Langlands.CommutativeAlgebra.IntegrallyClosedInReducedArtinian`.

- `isIntegral_of_isIdempotentElem`: if `e : B` is idempotent then `e` is integral
  over `R`. The witness is the monic polynomial `X ^ 2 - X`
  (monicity by `Polynomial.monic_X_pow_sub`), and `e ^ 2 - e = 0` because
  `e * e = e`.
- `exists_separating_idempotent`: in a reduced Artinian ring `B`, if `a * b = 0`
  then there is an idempotent `e` with `e * b = 0` and `(1 - e) * a = 0`. The
  proof uses the Mathlib isomorphism `IsArtinianRing.equivPi B` of `B` with the
  product of the fields `B ⧸ m` over its maximal ideals `m`. Take `e` to be the
  element whose `m`-component is `0` if the `m`-component of `a` is `0`, and `1`
  otherwise. Each identity is checked componentwise through the injective
  isomorphism. For `e * b = 0`: where the component of `a` is nonzero, the
  component of `b` is zero because the product of the components is zero in
  a field.

## Main proof

1. Injectivity of `algebraMap R B` comes from the injectivity built into
   `IsIntegrallyClosedIn` (`IsIntegralClosure.algebraMap_injective R R B`).
2. **Descent of separating idempotents.** If `a * b = 0` in `R`, then
   `exists_separating_idempotent` applied to the images of `a` and `b` gives an
   idempotent `e` of `B`. It is integral, so by
   `IsIntegrallyClosedIn.algebraMap_eq_of_integral` it is the image of some
   `r : R`. Since `algebraMap R B` is injective, `r` is idempotent,
   `r * b = 0` and `(1 - r) * a = 0` in `R`.
3. **No zero divisors.** Write `x = mk' a s` and `y = mk' b t` in
   `Localization.AtPrime p` (`IsLocalization.mk'_surjective`). If `x * y = 0`,
   then `IsLocalization.mk'_eq_zero_iff` gives `u ∉ p` with `u * (a * b) = 0`.
   Step 2 applied to `u * a` and `b` gives `r`. The localization is a local
   ring, so the image of `r` or of `1 - r` is a unit
   (`IsLocalRing.isUnit_or_isUnit_one_sub_self`).
   - If the image of `r` is a unit, then `r * b = 0` makes the image of `b`
     zero. `IsLocalization.map_eq_zero_iff` then gives `m ∉ p` with `m * b = 0`,
     so `y = 0`.
   - Otherwise `(1 - r) * (u * a) = 0` makes the image of `u * a` zero, so some
     `m ∉ p` has `m * (u * a) = 0`. Then `(m * u) * a = 0` with `m * u ∉ p`,
     so `x = 0`.
4. `Localization.AtPrime p` is nontrivial because it is a local ring. Together
   with step 3, `NoZeroDivisors.to_isDomain` makes it a domain.

The proof uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.
