# Prime-localization presentation of an essentially finitely presented local algebra: proof

This proof module imports the published statement
`Langlands.Algebra.EssFinitePresentationPrimeLocalizationStatement` and the published
helper module `Langlands.Algebra.PrimeLocalizationCriterion`. It changes neither of them,
nor the predicate `Langlands.Algebra.EssFinitePresentation`, nor any of their imports. Its
closing theorem is `Langlands.Algebra.essFinitePresentationPrimeLocalization.{u, v}`. The
complete type of that theorem is
`Langlands.Algebra.EssFinitePresentationPrimeLocalizationStatement.{u, v}`, with the
statement's two independent universes and no further outer parameters or hypotheses. The
final example checks this complete type with the unapplied constant
`@essFinitePresentationPrimeLocalization.{u, v}`.

Unfolded, the theorem says the following. Let `R : Type u` and `S : Type v` be commutative
rings, let `S` be a local ring, and give `S` an `R`-algebra structure. Suppose
`EssFinitePresentation R S`. Then there are `n : ℕ`, an ideal `I` of
`MvPolynomial (Fin n) R` with `I.FG`, an ideal `q` of the quotient
`MvPolynomial (Fin n) R ⧸ I` with a proof `hq : q.IsPrime`, and an `R`-algebra
isomorphism `Localization.AtPrime q ≃ₐ[R] S`. Here `Localization.AtPrime q` uses `hq` as
its primality instance. There is no hypothesis on `R` beyond being a commutative ring, and
no hypothesis on the structure map `R → S`. In particular, `R` need not be local and
`R → S` need not be a local homomorphism.

## Reusable interface

- `Langlands.Algebra.exists_algEquiv_localization_atPrime_of_local` has three independent
  universes: `R : Type u`, `S : Type v` and `A : Type w`. It takes commutative rings `R`,
  `S` and `A`, with `S` local, and `R`-algebra structures on `S` and on `A`. Its explicit
  arguments are an arbitrary submonoid `M : Submonoid A` and an `R`-algebra isomorphism
  `e : Localization M ≃ₐ[R] S`. It concludes
  `∃ (q : Ideal A) (hq : q.IsPrime), Nonempty (@Localization.AtPrime _ _ q hq ≃ₐ[R] S)`.
  The submonoid `M` may contain zero divisors. If `M` contains zero, then
  `Localization M` is the zero ring, and the isomorphism `e` would make `S` trivial too.
  That is impossible because `S` is local, so this case does not occur.
- `Langlands.Algebra.essFinitePresentationPrimeLocalization` is the closing theorem
  described above.

## Implemented proof

**The generic lemma.** `exists_algEquiv_localization_atPrime_of_local` works over an
abstract ring `A`. Write `L = Localization M`, with its canonical `A`-algebra and
`R`-algebra structures and the canonical scalar tower `R → A → L`.

1. *`L` is local.* `L` is nontrivial because `e` is a bijection onto the nontrivial ring
   `S` (`Equiv.nontrivial`, applied to `e.toEquiv`). Then Mathlib's
   `IsLocalRing.of_surjective'`, applied to the surjective ring homomorphism underlying
   `e.symm : S ≃ₐ[R] L`, makes `L` a local ring.
2. *The prime.* Let `q` be the inverse image of `IsLocalRing.maximalIdeal L` under
   `algebraMap A L`. It is prime because it is the inverse image of a prime ideal; the
   proof gets this instance by `inferInstance`.
3. *`L` is the localization of `A` at `q`.* The published
   `Langlands.Algebra.isLocalization_atPrime_of_local_target M` gives
   `IsLocalization.AtPrime L q`. That lemma says that any localization of `A` at a
   submonoid, if its target is local, is the localization at the contracted maximal ideal.
   This module does not reprove it.
4. *The isomorphism.* `Localization.AtPrime q` and `L` are both localizations of `A` at
   `q.primeCompl`. Mathlib's uniqueness of localizations,
   `IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q) L`, gives an
   `A`-algebra isomorphism `Localization.AtPrime q ≃ₐ[A] L`. `AlgEquiv.restrictScalars R`
   turns it into an `R`-algebra isomorphism; this uses the canonical scalar towers
   `R → A → Localization.AtPrime q` and `R → A → L`. Composing with `e` gives
   `Localization.AtPrime q ≃ₐ[R] S`.

**The closing theorem.** `essFinitePresentationPrimeLocalization` introduces the
statement's binders and destructs the hypothesis `EssFinitePresentation R S` into `n`, an
ideal `I` with `I.FG`, a submonoid `M` of `MvPolynomial (Fin n) R ⧸ I`, and
`e : Localization M ≃ₐ[R] S`. It applies the generic lemma with
`A = MvPolynomial (Fin n) R ⧸ I` and returns `n`, `I`, the same proof of `I.FG`, and the
prime `q` with its isomorphism. The relation ideal `I` and the number of variables `n`
are unchanged; only the submonoid `M` is replaced by the prime complement `q.primeCompl`.

The lemma is stated for an abstract ring `A` for a technical reason. Applying
`isLocalization_atPrime_of_local_target` directly with `A` the concrete quotient
`MvPolynomial (Fin n) R ⧸ I` caused `whnf`/`isDefEq` timeouts in a private experiment,
even with a raised heartbeat limit. With an abstract `A` the same steps elaborate quickly.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`. It uses no
`sorry`, no native computation and no raised heartbeat limit.

The module proves only this conversion. It does not assert that the contraction of `q` to
`R` is the maximal ideal of `R`, since the statement does not include that. It does not
prove the converse direction or any other part of Stacks Lemma 10.127.11 (tag 00QV), such
as the colimit system. It does not reprove the published prime-localization criterion or
Mathlib's uniqueness of localizations.

## Provenance

The original is the Stacks Project Authors, *The Stacks Project*, Commutative Algebra,
Section 10.127, Lemma 10.127.11
([tag 00QV](https://stacks.math.columbia.edu/tag/00QV)). Its proof begins: "By assumption
we may choose an isomorphism $\Phi : (R[x_1, \ldots, x_n]/I)_{\mathfrak q} \to S$ where
$I \subset R[x_1, \ldots, x_n]$ is a finitely generated ideal, and
$\mathfrak q \subset R[x_1, \ldots, x_n]/I$ is a prime." Stacks gives no separate argument
for this step. The published statement makes it a standalone proposition with weaker,
derived hypotheses (only `S` is local), as its Markdown explains. The registered source is
`stacks-algebra-flatness-criteria-2026-10-22`, files `00QV.html` and `00QL.html`
(Remark 10.127.12, tag 00QW), folder SHA-256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`. The definition of
essential finite presentation is the published `Langlands.Algebra.EssFinitePresentation`
(Stacks Definition 10.54.1, tag 00QM).

The Lean proof is the conversion sketched in the statement's Markdown: contract the
maximal ideal, apply the published criterion, and use the uniqueness of localizations. It
relies on pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435`, specifically
`IsLocalRing.of_surjective'` (`Mathlib.RingTheory.LocalRing.Basic`),
`IsLocalization.algEquiv` (`Mathlib.RingTheory.Localization.Basic`) and
`AlgEquiv.restrictScalars` (`Mathlib.Algebra.Algebra.Tower`).

Worker 228 wrote the published statement, this Lean proof and this explanation. The task
was published by Worker 706, whose context recorded the generic-ring route.
