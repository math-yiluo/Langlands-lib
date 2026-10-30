# Factorial stalks of smooth schemes over algebraically closed fields

`Langlands.AlgebraicGeometry.SmoothAlgClosedFactorialStalks.{u}` is the
following `Prop`-valued definition:

```lean
∀ (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
  (p : X ⟶ Spec (CommRingCat.of K)),
  Smooth p → ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)
```

Here `Scheme`, `Spec`, `Smooth`, `IsAlgClosed` and `UniqueFactorizationMonoid`
are Mathlib's existing notions, used unchanged. `X.presheaf.stalk x` is the
local ring of the structure sheaf at the point `x`, viewed as a commutative
monoid with zero under multiplication.

## The factoriality predicate

Mathlib's `UniqueFactorizationMonoid α` extends `IsCancelMulZero α`. It also
requires that `DvdNotUnit` is well founded on `α` (so every unique
factorization monoid is a `WfDvdMonoid`, which abbreviates that condition) and
that every irreducible element of `α` is prime. A stalk is a local ring, hence
nontrivial, so the cancellation part makes it a domain.

For a domain, Mathlib's class agrees with the Stacks definition of a unique
factorization domain ([Tag 034S](https://stacks.math.columbia.edu/tag/034S),
Definition 10.120.4): every nonzero nonunit factors into irreducibles, and two
such factorizations have the same length and agree up to a permutation and
associates. Mathlib proves the two directions as follows.

- From the class: `WfDvdMonoid.exists_factors` gives existence and
  `UniqueFactorizationMonoid.factors_unique` gives uniqueness up to
  associates, as multisets of irreducible factors.
- To the class: `UniqueFactorizationMonoid.of_existsUnique_irreducible_factors`
  builds the class from existence and uniqueness of irreducible
  factorizations in a cancellative monoid with zero.

The "irreducible iff prime" field corresponds to Stacks
[Tag 034T](https://stacks.math.columbia.edu/tag/034T), Lemma 10.120.5.
Stacks calls `x` irreducible when it is a nonzero nonunit and every
factorization `x = yz` has `y` a unit or an associate of `x`. Mathlib's
`Irreducible x` asks that `x` is a nonunit and that one of the two factors is
a unit. In a domain these agree, and zero is not irreducible in either sense.

## Generality

The conclusion holds at every point `x`, closed or not. The universe `u` is
arbitrary. The field `K` is algebraically closed of any characteristic. The
smooth scheme `X` is otherwise arbitrary: no quasi-compactness, separation,
properness, connectedness, dimension or group hypothesis is imposed. The empty
scheme satisfies the statement vacuously.

## Original sources

The proposition is the composite of two Stacks Project results, read in the
retained files listed below.

1. [Tag 056S](https://stacks.math.columbia.edu/tag/056S), Lemma 33.25.3: if
   `X → Spec(k)` is smooth and `k` is a field, then `X` is a regular scheme.
   The proof shows that every local ring `O_{X,x}` is a regular local ring.
   Retained file `056S.html` in literature source
   `stacks-smooth-connected-integral-2026-10-24`.
2. [Tag 0AG0](https://stacks.math.columbia.edu/tag/0AG0), Lemma 15.123.2: a
   regular local ring is a UFD. It lies in
   [Tag 0FJH](https://stacks.math.columbia.edu/tag/0FJH), Section 15.123, and
   its proof uses [Tag 0AFZ](https://stacks.math.columbia.edu/tag/0AFZ),
   Lemma 15.123.1. The UFD definition, Definition 10.120.4 (Tag 034S), lies in
   [Tag 034O](https://stacks.math.columbia.edu/tag/034O), Section 10.120.
   The retained files `0AG0.html`, `0FJH.html`, `0AFZ.html` and `034O.html`
   belong to literature source `stacks-regular-local-ufd-2026-10-29`, which
   also keeps the page comments. No comment changes the statements used here.

## Derived formulation

The statement is derived: no single source asserts it in exactly this form.
Composing the two lemmas gives the conclusion for a scheme smooth over any
field. That general-field case is true but is not stated here; this
definition keeps only the special case of an algebraically closed field.

The intended consumer is the existence of finite section seeds on abelian
group schemes over algebraically closed fields (task
`3ea19da5-0729-4710-aaa0-fddf297ac368` and its successors). There it turns
prime divisors through a point into invertible ideal sheaves.

## Proof boundary

The Lean file defines this proposition and supplies no proof. Regular local
rings and regular schemes appear only in the provenance above; no Lean
regularity notion or certificate is introduced. A separate proof must
establish this exact proposition.
