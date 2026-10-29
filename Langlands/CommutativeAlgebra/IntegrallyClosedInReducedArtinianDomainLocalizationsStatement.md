# Domain prime localizations of rings integrally closed in reduced Artinian rings

`Langlands.CommutativeAlgebra.IntegrallyClosedInReducedArtinianDomainLocalizations.{u, v}`
is the following `Prop`-valued definition:

```lean
∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B],
  IsIntegrallyClosedIn R B → IsReduced B → IsArtinianRing B →
    ∀ (p : Ideal R) [p.IsPrime], IsDomain (Localization.AtPrime p)
```

It says: let `B` be a reduced Artinian commutative ring and `R` a commutative
ring with an algebra map `R → B`. If `R` is integrally closed in `B`, then the
localization `R_p` of `R` at every prime ideal `p` of `R` is a domain.

## The Mathlib notions used

All notions are Mathlib's existing ones; the module imports only Mathlib.

- `IsIntegrallyClosedIn R B` is Mathlib's abbreviation for
  `IsIntegralClosure R R B`. It has two fields: the algebra map `R → B` is
  injective (`IsIntegralClosure.algebraMap_injective`), and an element of `B` is
  integral over `R` exactly when it lies in the image of `R`
  (`IsIntegralClosure.isIntegral_iff`). So the hypothesis includes the
  injectivity of `R → B`; it is not only the condition that integral elements
  come from `R`.
- `IsReduced B` says that `B` has no nonzero nilpotent elements.
- `IsArtinianRing B` is `IsArtinian B B`: `B` is Artinian as a module over
  itself, that is, it satisfies the descending chain condition on ideals.
- `Ideal.IsPrime p` is supplied as an instance argument, and
  `Localization.AtPrime p` is the localization of `R` at the complement of `p`.
- `IsDomain` includes nontriviality as well as the absence of zero divisors.

## Scope

The universe parameters `u` of `R` and `v` of `B` are arbitrary and
independent. No other hypothesis is imposed. In particular `R` is not assumed
Noetherian, reduced, a domain, or to have finitely many minimal primes, and `B`
is not assumed finite, integral, or of finite type over `R`, nor to be the total
ring of fractions of `R`. The ring `B` need not be a domain or connected. The
conclusion concerns each prime localization of `R` separately; it does not say
that `R` itself is a domain.

If `B` is the zero ring, injectivity of `R → B` forces `R` to be the zero
ring, which has no prime ideals, so the conclusion holds vacuously.

## Derived provenance

This is an internally derived lemma, not a verbatim translation of a
published statement. Its motivation is the proof of Stacks Project
[Tag 030C](https://stacks.math.columbia.edu/tag/030C), Lemma 10.37.16. That
lemma concerns a reduced ring `R` with finitely many minimal primes and shows
that if `R` is integrally closed in its total ring of fractions `Q(R)`, then `R`
is a finite product of normal domains. Its proof writes `Q(R)` as a finite
product of fields and says: "If $R$ is integrally closed in $Q(R)$, then it
contains in particular the idempotents $e_ i$, and we see that $R$ is a product
of $n$ domains". The retained file is `030C.html` in literature source
`stacks-integral-closure-idempotent-generic-fiber-2026-10-28`, content SHA256
`66c72671cd84205183edcebc4e569179a3188b2b02898e669a1e172a56ac6abc`. The
page was downloaded on 28 October 2026, and its statement, proof and comments
were read directly. The Stacks Project has no separate errata file. The four
comments on the tag (#745, #757, #2180, #2207) concern the treatment of zero
divisors and the argument about the factors `R/p_i`. They record changes made in
2014 and 2016, which the retained proof text reflects. None affects the
idempotent step used here.

The proposition above replaces `Q(R)` by an arbitrary reduced Artinian ring
`B` containing `R` and keeps only the conclusion about prime localizations. The
following derivation explains why it is expected to hold; it is motivation, not
Lean evidence.

- A reduced Artinian commutative ring is a finite product of fields. In
  Mathlib this is `IsArtinianRing.equivPi`, an isomorphism from `B` to the
  product of the quotients `B ⧸ m` over the maximal ideals `m`.
- Every idempotent of `B` satisfies `X ^ 2 - X = 0`, so it is integral over
  `R`. Since `R` is integrally closed in `B` and `R → B` is injective, it is
  the image of a unique idempotent of `R`.
- Let `a b : R` with `a * b = 0`. In the product of fields, the idempotent `e`
  with components `1` exactly where the image of `a` is nonzero satisfies
  `e * b = 0` and `(1 - e) * a = 0` in `B`. Descending `e` to an idempotent `r`
  of `R` gives `r * b = 0` and `(1 - r) * a = 0` in `R`.
- The localization `R_p` is a local ring, so the image of `r` in `R_p` is `0`
  or `1`. Hence the image of `a` or of `b` vanishes in `R_p`. Clearing the
  denominators of a product of two fractions that vanishes in `R_p` reduces the
  absence of zero divisors in `R_p` to this case; `R_p` is nontrivial because
  `p` is prime.

The companion file `03GE.html` in the same source folder is Stacks
[Tag 03GE](https://stacks.math.columbia.edu/tag/03GE), Lemma 10.147.2, on
integral closure under étale base change. It motivates the intended downstream
application; it is not used for this statement.

## Relation to other targets

This module does not import or use
`Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizations`,
`Langlands.AlgebraicGeometry.SmoothDomainStalks`, or any pointed-morphism
rigidity target. It is intended as a generic input for the proof of
`Langlands.CommutativeAlgebra.SmoothAlgebraDomainLocalizations`; the smooth or
étale adapter that applies it belongs to that separate work.

## Proof boundary

The Lean file defines this proposition and supplies no proof. A separate proof
must establish this exact proposition.
