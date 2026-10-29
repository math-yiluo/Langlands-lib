# Prime-localization presentation of an essentially finitely presented local algebra

Lean module: `Langlands.Algebra.EssFinitePresentationPrimeLocalizationStatement`.
Declaration: `Langlands.Algebra.EssFinitePresentationPrimeLocalizationStatement.{u, v} : Prop`.

This file states a proposition. It does not prove it. The proof is a separate
task.

## Statement in words

Let $R$ be a commutative ring and $S$ a commutative $R$-algebra that is a local
ring. Suppose $S$ is essentially of finite presentation over $R$, in the sense of
the published predicate `Langlands.Algebra.EssFinitePresentation`. That predicate
says $S$ is the localization of $A = R[x_1, \dots, x_n]/I$, with $I$ finitely
generated, at some submonoid $M \subseteq A$. Then $S$ is the localization of such
a quotient at a prime ideal. That is, there are

- a natural number $n$,
- a finitely generated ideal $I \subseteq R[x_1, \dots, x_n]$, and
- a prime ideal $\mathfrak q$ of $A = R[x_1, \dots, x_n]/I$,

and an $R$-algebra isomorphism $A_{\mathfrak q} \cong S$.

## Lean statement

```lean
def EssFinitePresentationPrimeLocalizationStatement : Prop :=
  ∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S],
    EssFinitePresentation R S →
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) (_ : I.FG)
      (q : Ideal (MvPolynomial (Fin n) R ⧸ I)) (hq : q.IsPrime),
      letI := hq
      Nonempty (Localization.AtPrime q ≃ₐ[R] S)
```

The file imports only `Langlands.Algebra.EssFinitePresentation` and
`Mathlib.RingTheory.Localization.AtPrime.Basic`.

### Binders and instances

- `R` and `S` are universally quantified as explicit types. The instances
  `CommRing R`, `CommRing S`, `IsLocalRing S` and `Algebra R S` are bound as
  instance arguments. `IsLocalRing S` includes that $S$ is nontrivial.
- There is no locality hypothesis on `R`, and no `IsLocalHom (algebraMap R S)`
  hypothesis. Only the target `S` is assumed local.
- `(_ : I.FG)` is an anonymous proof binder inside the existential. It means the
  same as the conjunction `I.FG ∧ …`: the ideal of relations is finitely
  generated.
- `(hq : q.IsPrime)` asks for a proof that `q` is prime. `Localization.AtPrime q`
  needs an instance `q.IsPrime`, and `letI := hq` installs this witness as that
  instance. Unfolded, the conclusion is
  `Nonempty (@Localization.AtPrime _ _ q hq ≃ₐ[R] S)`.
- `Localization.AtPrime q` is Mathlib's localization of the quotient ring
  `MvPolynomial (Fin n) R ⧸ I` at the complement `q.primeCompl` of `q`. Its
  `R`-algebra structure is the canonical one through the quotient. So `R` acts
  through $R \to R[x_1, \dots, x_n] \to A \to A_{\mathfrak q}$.
- `≃ₐ[R]` is an `R`-algebra isomorphism, so it is a ring isomorphism compatible
  with the structure maps from `R`. `Nonempty` only asserts that such an
  isomorphism exists. No particular one is chosen.

### Universes

`R : Type u` and `S : Type v` live in independent universes. The polynomial ring,
its quotient and the localization all live in `Type u`. The isomorphism goes
between two universes. The declaration has the universe parameters `u` and `v`,
in this order. This matches `EssFinitePresentation`, which also takes its
finitely presented algebra in the standard form `MvPolynomial (Fin n) R ⧸ I`.

## Source

The Stacks Project, Commutative Algebra, Section 10.127, Lemma 10.127.11
(tag 00QV), in the registered snapshot `00QV.html`. The lemma assumes that
$R \to S$ is a local homomorphism of local rings and that $S$ is essentially of
finite presentation over $R$. The first sentence of its proof is:

> By assumption we may choose an isomorphism
> $\Phi : (R[x_1, \ldots, x_n]/I)_{\mathfrak q} \to S$ where
> $I \subset R[x_1, \ldots, x_n]$ is a finitely generated ideal, and
> $\mathfrak q \subset R[x_1, \ldots, x_n]/I$ is a prime. (Note that
> $R \cap \mathfrak q$ is equal to the maximal ideal $\mathfrak m$ of $R$.)

This proposition is the step "by assumption we may choose" in this sentence,
made into a standalone statement. Stacks does not prove it separately. The rest
of the proof of 00QV (generators of $I$, writing $R$ as a colimit, the system
$S_\lambda$) is not part of this unit. The same file `00QL.html` contains
Remark 10.127.12 (tag 00QW), which comes right after the lemma. That remark
shows that the system has to be chosen with care. The prime-localization form
here is what the construction in the proof of 00QV starts from.

### Derived, weaker hypotheses

The hypotheses here are weaker than those of 00QV. This change is derived; it is
not in the source.

- **Only $S$ is local.** 00QV assumes that $R$ and $S$ are local and that
  $R \to S$ is a local homomorphism. The conversion below uses only that $S$ is
  local. So `R` is an arbitrary commutative ring and the structure map is
  arbitrary.
- **The parenthetical $R \cap \mathfrak q = \mathfrak m$ is not asserted.** The
  Lean conclusion says nothing about the contraction of $\mathfrak q$ to $R$.
  Informally, for every witness the contraction of $\mathfrak q$ to $R$ equals the
  inverse image of the maximal ideal $\mathfrak m_S$ under $R \to S$. The reason
  is that $\mathfrak q$ is the inverse image of the maximal ideal of
  $A_{\mathfrak q}$, and the isomorphism maps maximal ideal to maximal ideal and
  is compatible with the maps from $R$. When $R \to S$ is a local homomorphism of
  local rings, this inverse image is $\mathfrak m$. This is the source's remark. It
  is explanation only, not a Lean conclusion.

## The conversion: contracting the maximal ideal of S

This describes the intended proof. It is not proved in this file.

Unpack `EssFinitePresentation R S`. This gives $n$, a finitely generated ideal
$I$, a submonoid $M$ of $A = R[x_1, \dots, x_n]/I$, and an $R$-algebra
isomorphism $e : M^{-1}A \cong S$. Keep $n$ and $I$, and replace $M$ by a prime
complement as follows.

1. **$M^{-1}A$ is local.** It is isomorphic to the local ring $S$ through $e$.
2. **The prime.** Let $\mathfrak q \subseteq A$ be the inverse image of the
   maximal ideal of $M^{-1}A$ under the localization map $A \to M^{-1}A$. It is
   prime, since it is the inverse image of a prime ideal. Since $e$ maps the
   maximal ideal of $M^{-1}A$ onto the maximal ideal $\mathfrak m_S$ of $S$,
   $\mathfrak q$ is also the contraction of $\mathfrak m_S$ along the composite
   $A \to M^{-1}A \xrightarrow{e} S$.
3. **$M \subseteq A \setminus \mathfrak q$.** Elements of $M$ become units in
   $M^{-1}A$, so they are not in its maximal ideal.
4. **$M^{-1}A$ is the localization of $A$ at $\mathfrak q$.** This is the
   published Library lemma
   `Langlands.Algebra.isLocalization_atPrime_of_local_target` (module
   `Langlands.Algebra.PrimeLocalizationCriterion`). It says that any localization
   with a local target is the localization at the contracted maximal ideal.
   Informally: every element of $A \setminus \mathfrak q$ maps outside the
   maximal ideal of the local ring $M^{-1}A$, so to a unit. Every element of
   $M^{-1}A$ is a fraction $a/m$ with $m \in M \subseteq A \setminus \mathfrak q$.
   Every element of the kernel of $A \to M^{-1}A$ is killed by some element of
   $M$.
5. **The isomorphism.** Two localizations of $A$ at the same submonoid are
   isomorphic as $A$-algebras (Mathlib's `IsLocalization.algEquiv`). This gives
   $A_{\mathfrak q} \cong M^{-1}A$. Restrict scalars from $A$ to $R$, which is
   possible since $R$ acts on both through $A$, and compose with $e$. The result
   is an $R$-algebra isomorphism $A_{\mathfrak q} \cong S$.

**The intended inverse.** The inverse $S \to A_{\mathfrak q}$ first applies
$e^{-1} : S \to M^{-1}A$. It then sends $a/m \mapsto a/m$ from $M^{-1}A$ into
$A_{\mathfrak q}$. This map is well defined because $M \subseteq A \setminus
\mathfrak q$, so every $m \in M$ is already a unit in $A_{\mathfrak q}$. By the
universal property of $M^{-1}A$ it is the unique $A$-algebra map
$M^{-1}A \to A_{\mathfrak q}$. The forward map $A_{\mathfrak q} \to M^{-1}A$
sends $a/s$ to $(a/1)(s/1)^{-1}$. Here $s/1$ is a unit because
$s \notin \mathfrak q$ and $M^{-1}A$ is local. The two maps are mutually inverse
because both composites are $A$-algebra endomorphisms of a localization of $A$,
hence identities.

**The converse is not stated.** Conversely, every witness of this conclusion
gives `EssFinitePresentation R S`: take $M = \mathfrak q^{c}$ (`q.primeCompl`),
and then `Localization.AtPrime q` is `Localization q.primeCompl` by definition.
This direction is immediate and is not part of the proposition.

## Comparison with LocalPolynomialPresentationStatement

The published `Langlands.Algebra.LocalPolynomialPresentationStatement` (for the
proof of Stacks 05UV) assumes that $R$ and $S$ are local, that $R \to S$ is a
local homomorphism, and only that $S$ is *essentially of finite type*. It gives a
prime $\mathfrak q$ of the polynomial ring itself and a *surjective* $R$-algebra
map $R[x_1, \dots, x_n]_{\mathfrak q} \to S$, with both maps local. It records no
relation ideal.

The present conclusion is stronger. It gives a full $R$-algebra *isomorphism*,
and it keeps a finitely generated ideal $I$ of polynomial relations, so the
presentation is finite. Its hypothesis is different: essential finite
presentation instead of essential finite type, but no locality of $R$ or of
$R \to S$. Neither proposition is used to state the other.

## Provenance

The source is `stacks-algebra-flatness-criteria-2026-10-22`. Its folder SHA256 is
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`. The relevant
locations are:

- `00QV.html`, Lemma 10.127.11, the hypotheses and the first sentence of the
  proof (quoted above);
- `00QL.html`, Remark 10.127.12 (tag 00QW), for context.

This standalone statement is derived. Stacks uses the presentation inside the
proof of 00QV without stating it separately. The weaker hypotheses (only $S$
local) and the omission of $R \cap \mathfrak q = \mathfrak m$ are derived
choices, explained above. The definition of essential finite presentation is the
published `Langlands.Algebra.EssFinitePresentation` (Stacks Definition 10.54.1,
tag 00QM). The conversion route uses the published Library lemma
`Langlands.Algebra.isLocalization_atPrime_of_local_target` and Mathlib's
uniqueness of localizations.
