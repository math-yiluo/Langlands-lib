# Regular local rings are unique factorization domains

`Langlands.CommutativeAlgebra.RegularLocalFactorialStatement.{u}` defines exactly
the proposition

```lean
∀ (R : Type u) [CommRing R],
  IsRegularLocalRing R → UniqueFactorizationMonoid R
```

It states that every regular local commutative ring is a unique factorization
domain. The universe `u` is arbitrary. The Lean file defines this proposition
and supplies no proof or new axiom.

## Conventions

The imports are `Mathlib.RingTheory.RegularLocalRing.Defs` and
`Mathlib.RingTheory.UniqueFactorizationDomain.Defs`. All three ring notions in
the proposition are Mathlib's existing notions.

`IsRegularLocalRing R` extends `IsLocalRing R` and `IsNoetherianRing R`.
Its additional field is
`(IsLocalRing.maximalIdeal R).spanFinrank = ringKrullDim R`: the minimal number
of generators of the maximal ideal equals the Krull dimension. Thus this is the
usual Noetherian regular-local convention, with finite dimension. Equivalently,
the dimension of the cotangent space over the residue field equals the Krull
dimension, as expressed by
`IsRegularLocalRing.iff_finrank_cotangentSpace`. The local-ring class also
supplies `Nontrivial R`.

`UniqueFactorizationMonoid R` extends `IsCancelMulZero R`, supplies
well-founded strict divisibility, and asserts that irreducible elements are
exactly prime elements. For a nontrivial commutative ring, cancellation away
from zero implies the absence of zero divisors. Together these conditions
express the ordinary UFD property: the ring is a domain and every nonzero
nonunit factors into irreducibles, uniquely up to permutation and multiplication
of factors by units. Hence no separate `IsDomain R` premise is needed.

Regularity is an explicit implication premise, rather than an instance binder.
The assertion has no additional restriction on dimension, characteristic,
residue field, completeness, henselianity or excellence.

## Original source

This is a direct formalization of the Stacks Project, More on Algebra,
Lemma 15.123.2, [Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0):
“A regular local ring is a UFD.” The ordinary factorization convention is
Definition 10.120.4 in
[Section 10.120, Tag 034O](https://stacks.math.columbia.edu/tag/034O).

The originals are retained as `0AG0.html` and `034O.html` in the registered source
`stacks-regular-local-ufd-2026-10-29`, entitled
*Stacks Project - Regular local rings are UFDs and factorization definitions
(HTML snapshot 2026-10-29)*, with directory SHA256
`49b665ff41945fd15cc966fe79e70688059509c0487cc27f32167fe1e1baed31`.
The full 0AG0 statement and proof and the section page `0FJH.html` were read.
The lemma page has no comments. The two section comments, #6705 and #6908,
concern suggested power-series additions and do not correct this lemma.

The source proof proceeds by induction on dimension, using regularity of
localizations and the vanishing of the Picard group after inverting one
element (Lemma 15.123.1, Tag 0AFZ), to show that height-one primes are principal.
This describes the source argument; no part of it is implemented in this
statement module.

The assertion is intended as the generic ring prerequisite for factoriality of
prime localizations of smooth algebras over discrete valuation rings. It imports
no geometric extension result and adds no dependency on those later applications.
