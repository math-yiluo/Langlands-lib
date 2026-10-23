# Essentially finitely presented algebras (Stacks 00QM)

Lean module: `Langlands.Algebra.EssFinitePresentation`.
Declaration: `Langlands.Algebra.EssFinitePresentation (R : Type u) (S : Type v)
[CommRing R] [CommRing S] [Algebra R S] : Prop`.

This file only introduces the predicate. It proves no theorem about it.

## Source

The Stacks Project, Commutative Algebra, Section 10.54, Definition 10.54.1
(tag 00QM), in the registered snapshot `07DR.html`:

> Let $R \to S$ be a ring map. [...] We say that $R \to S$ is *essentially of
> finite presentation* if $S$ is the localization of an $R$-algebra of finite
> presentation.

The comment thread on the same page (Comment #2262, by Johan, answering
Comment #2257) says what "localization" means in this section:

> Localization, when not otherwise specified, just means inverting some
> multiplicatively closed subset.

So the definition reads: there is a finitely presented $R$-algebra $A$ and a
multiplicatively closed subset $T \subseteq A$ such that $S \cong T^{-1}A$ as
$R$-algebras.

## Lean definition

```lean
def EssFinitePresentation (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    Prop :=
  ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)), I.FG ∧
    ∃ M : Submonoid (MvPolynomial (Fin n) R ⧸ I), Nonempty (Localization M ≃ₐ[R] S)
```

In words: there are a natural number $n$, a finitely generated ideal
$I \subseteq R[x_1, \dots, x_n]$, a submonoid $M$ of $A = R[x_1, \dots, x_n]/I$,
and an $R$-algebra isomorphism $M^{-1}A \cong S$.

## Comparison with the source

- **Finitely presented algebra.** A finitely presented $R$-algebra is one of the
  form $R[x_1, \dots, x_n]/(f_1, \dots, f_m)$, that is, a polynomial ring in
  finitely many variables modulo a finitely generated ideal. This is Stacks
  Definition 10.6.1 (tag 00F3). That tag is not in the registered snapshot, but
  the notion is standard. Mathlib's `Algebra.FinitePresentation` encodes the
  same notion, and `Algebra.FinitePresentation.iff` states that `A` is finitely
  presented over `R` if and only if
  `∃ n (I : Ideal (MvPolynomial (Fin n) R)) (_ : (MvPolynomial (Fin n) R ⧸ I) ≃ₐ[R] A), I.FG`.
  The Lean predicate uses exactly these standard quotients
  `MvPolynomial (Fin n) R ⧸ I` with `I.FG`.
- **Localization.** `M` is an arbitrary `Submonoid` of the quotient. A submonoid
  is a multiplicatively closed subset containing $1$. Since inverting $T$ and
  inverting $T \cup \{1\}$ give the same ring, this matches "inverting some
  multiplicatively closed subset". `Localization M` is Mathlib's localization of
  a commutative ring at a submonoid, with its induced `R`-algebra structure. No
  condition is placed on `M`. In particular `M` is not required to be the
  complement of a prime, and it may contain zero divisors. So the localization
  map $A \to M^{-1}A$ need not be injective, and $S$ is not required to contain a
  finitely presented subalgebra from which it is obtained.
- **"S is the localization".** The source identifies $S$ with $T^{-1}A$ as an
  $R$-algebra. The Lean statement asks for an `R`-algebra isomorphism
  `Localization M ≃ₐ[R] S`. Composing it with the canonical map
  `A → Localization M` gives the $R$-algebra map $A \to S$, which makes $S$ a
  localization of $A$ at $M$.
- **No extra hypotheses.** `R` and `S` are arbitrary commutative rings and `S` is
  an arbitrary `R`-algebra. There are no Noetherian, domain, local or flatness
  assumptions, as in the source.

## Universes, and why every presentation is covered

`R : Type u` and `S : Type v` live in independent universes. The finitely
presented algebra is not quantified over as an arbitrary type, since that would
force an extra universe parameter. It is always taken in the standard form
`MvPolynomial (Fin n) R ⧸ I`, which lives in `Type u`. This loses nothing.
Suppose $A$ is any finitely presented $R$-algebra, in any universe, and
$T \subseteq A$ is a submonoid with $S \cong T^{-1}A$ as $R$-algebras. Then:

1. By `Algebra.FinitePresentation.iff` there is an $R$-algebra isomorphism
   $e : R[x_1, \dots, x_n]/I \cong A$ with $I$ finitely generated.
2. Transport $T$ along $e$ to the submonoid $M = e^{-1}(T)$ of the quotient.
   Then $e$ induces an $R$-algebra isomorphism $M^{-1}(R[x_1, \dots, x_n]/I) \cong
   T^{-1}A$. Composing gives `Localization M ≃ₐ[R] S`.

In particular, every finitely presented $R$-algebra $S$ itself satisfies the
predicate. Take $M = \bot = \{1\}$. Localizing at a submonoid of units changes
nothing: Mathlib's `IsLocalization.atUnits` gives the isomorphism
$A \cong M^{-1}A$. Conversely, the witnesses of the Lean predicate are a
finitely presented algebra (by `Algebra.FinitePresentation.iff`), a
multiplicatively closed subset of it, and an identification of $S$ with the
localization. So the Lean predicate is equivalent to the Stacks definition.
This equivalence is the informal justification above. It is not proved in Lean
here.

## Provenance

The source is `stacks-algebra-flatness-criteria-2026-10-22`. Its folder SHA256
is `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`. The
relevant file is `07DR.html`, Definition 10.54.1 (tag 00QM), together with
Comment #2262 on the convention for "localization". The choice of the standard
`Fin n` polynomial-quotient form is a formalization device for universe safety,
as explained above. The pinned Mathlib has `Algebra.EssFiniteType` and
`Algebra.FinitePresentation` but no essentially-finitely-presented predicate.
