# Renard B.I: Amitsur's theorem for countable-dimensional complex algebras

This module states the theorem of David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, Appendix B.I "Théorème
d'Amitsur", printed pages 271–272 / PDF pages 277–278. Let *A* be a unital complex
algebra of at most countable dimension. Then every element of *A* has nonempty
spectrum, the spectrum of an element is `{0}` exactly when the element is
nilpotent, and *A* is ℂ when it is a division algebra. The module uses Mathlib's
algebraic `spectrum`, Mathlib's `IsNilpotent`, the cardinal-valued
`Module.rank` and the actual structure map `algebraMap`. It introduces no new
spectrum, dimension or scalar map. Amitsur's assertions are only stated here.
They are neither proved nor assumed.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 277–278 were read in full, both as extracted text and as rendered
images. PDF pages 11–12 (printed pages 5–6) were read for the general conventions
on rings. The current Library has no `notes/errata` file for this source. The
registered 2010-edition errata `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, were also
checked. Their Appendix B entries (PDF page 19) concern only B.II (2010 page 314:
*M* a complex vector space, adjoining a unit) and B.III (2010 page 315: left
invertibility). The 2026 text already contains both corrections. There is no
entry for B.I. That errata list concerns a different edition, so the 2026 text
governs here.

## The source passage

On PDF page 277 the original reads:

> **B.I Théorème d'Amitsur**
>
> Le résultat principal de cette section est dû à Amitsur. On peut le voir comme
> une version non commutative du théorème des zéros de Hilbert pour des algèbres
> sur le corps ℂ.
>
> *Définition.* Soit *A* une ℂ-algèbre d'unité 1_*A*. Le spectre d'un élément *a*
> de *A* est l'ensemble
>
> Spec(*a*) = {λ ∈ ℂ | *a* − λ1_*A* n'est pas inversible}
>
> On identifie la sous-algèbre ℂ1_*A* de *A* avec ℂ.
>
> *Théorème.* Supposons que *A* soit de dimension au plus dénombrable sur ℂ. Alors
>
> *a*) si *A* est une algèbre à division, *A* = ℂ,
>
> *b*) pour tout *a* ∈ *A*, Spec(*a*) est non vide. De plus Spec(*a*) = {0} si et
> seulement si *a* est nilpotent.

In English: for a complex algebra with unit 1_*A*, the spectrum of *a* is the set
of complex λ such that *a* − λ1_*A* is not invertible, and the scalar subalgebra
ℂ1_*A* is identified with ℂ. If *A* has at most countable dimension over ℂ, then
(a) a division algebra *A* equals ℂ, and (b) every spectrum is nonempty, and
Spec(*a*) = {0} if and only if *a* is nilpotent. The proof follows on PDF pages
277–278. B.II (Schur's lemma) starts on PDF page 278, and B.III follows it.

## Declarations

All declarations are in namespace `Langlands.Renard` with universe parameter
`u`. Each proposition carries `@[pp_with_univ]` and is a `def` returning
`Prop`.

| Declaration | Content | Source |
| --- | --- | --- |
| `AmitsurSpectrumNonemptyStatement A` | `Module.rank ℂ A ≤ Cardinal.aleph0 → ∀ a : A, (spectrum ℂ a).Nonempty` | Théorème b), first sentence |
| `AmitsurSpectrumSingletonZeroStatement A` | `Module.rank ℂ A ≤ Cardinal.aleph0 → ∀ a : A, spectrum ℂ a = ({0} : Set ℂ) ↔ IsNilpotent a` | Théorème b), second sentence |
| `AmitsurDivisionAlgebraStatement D` | `Module.rank ℂ D ≤ Cardinal.aleph0 → Function.Bijective (algebraMap ℂ D)` | Théorème a) |
| `AmitsurDivisionAlgebraEquivStatement D` | `Module.rank ℂ D ≤ Cardinal.aleph0 → ∃ e : ℂ ≃ₐ[ℂ] D, ∀ z : ℂ, e z = algebraMap ℂ D z` | Théorème a), optional reformulation |
| `AmitsurTheoremStatement` | the conjunction of the first three over all carriers in `Type u` | the whole Théorème |

The first two take `(A : Type u) [Ring A] [Algebra ℂ A] [Nontrivial A]`. The
two division-algebra propositions take `(D : Type u) [DivisionRing D]
[Algebra ℂ D]`. All of these are explicit binders in each declaration header.
They are not section variables, so `Nontrivial A` cannot be dropped as an
unused instance variable. The printed types confirm that `[Nontrivial A]` is a
binder of both spectrum propositions.

The entry proposition is

```lean
def AmitsurTheoremStatement : Prop :=
  (∀ (A : Type u) [Ring A] [Algebra ℂ A] [Nontrivial A],
      AmitsurSpectrumNonemptyStatement.{u} A ∧ AmitsurSpectrumSingletonZeroStatement.{u} A) ∧
    ∀ (D : Type u) [DivisionRing D] [Algebra ℂ D], AmitsurDivisionAlgebraStatement.{u} D
```

It contains the three required assertions, each available separately under its
own name. It does not contain the optional `AmitsurDivisionAlgebraEquivStatement`,
which the lemma below shows to be equivalent to `AmitsurDivisionAlgebraStatement`.

The module also proves two elementary lemmas. Neither proves any of Amitsur's
assertions:

- `mem_spectrum_iff_not_isUnit_sub_smul_one {A : Type u} [Ring A] [Algebra ℂ A]
  (a : A) (z : ℂ) : z ∈ spectrum ℂ a ↔ ¬ IsUnit (a - z • (1 : A))`. This is the
  source's definition of Spec(*a*), checked against Mathlib's (see below).
- `amitsurDivisionAlgebraStatement_iff_equivStatement (D : Type u)
  [DivisionRing D] [Algebra ℂ D] : AmitsurDivisionAlgebraStatement D ↔
  AmitsurDivisionAlgebraEquivStatement D`. Forward, the algebra isomorphism is
  `AlgEquiv.ofBijective (Algebra.ofId ℂ D)`, and its values are those of
  `algebraMap ℂ D` by definition. Backward, the normalization `e z =
  algebraMap ℂ D z` makes `⇑(algebraMap ℂ D) = ⇑e`, so `e.bijective` gives the
  bijectivity.

## Conventions used

- **Algebras.** On PDF page 12 the book says that rings are not assumed unital
  unless explicitly stated. B.I explicitly takes "une ℂ-algèbre d'unité 1_*A*",
  so *A* is a unital associative complex algebra. B.I calls the theorem "une
  version non commutative du théorème des zéros de Hilbert", so *A* is not
  assumed commutative. In Lean this is `[Ring A] [Algebra ℂ A]`: a unital
  associative ring, possibly noncommutative, with a ring homomorphism
  `algebraMap ℂ A` into its center and `z • x = algebraMap ℂ A z * x`.
  `Algebra.algebraMap_eq_smul_one` gives `algebraMap ℂ A z = z • (1 : A)`, the
  source's λ1_*A*. No commutativity, finite dimension, norm, topology,
  group-representation origin or algebraicity hypothesis is imposed.
- **Division algebras.** "Algèbre à division" is `[DivisionRing D]
  [Algebra ℂ D]`: a complex algebra, possibly noncommutative, whose nonzero
  elements are invertible. `DivisionRing` already includes `Nontrivial D`.
- **Dimension at most countable.** "De dimension au plus dénombrable sur ℂ" is
  `Module.rank ℂ A ≤ Cardinal.aleph0`. Mathlib defines `Module.rank R M` as the
  supremum of the cardinalities of the linearly independent subsets of `M`
  (`Mathlib/LinearAlgebra/Dimension/Basic.lean`). Over the field ℂ this is the
  cardinality of any basis (`Module.Basis.mk_eq_rank''`). So the hypothesis says
  that *A* has a finite or countably infinite basis over ℂ. It is not
  `Module.finrank`, which is `0` for every infinite-dimensional space. It is not
  countability of the underlying set either: ℂ itself is uncountable but has
  rank one. `Module.rank ℂ A` lies in `Cardinal.{u}`, and `Cardinal.aleph0` is
  taken in the same universe.
- **Invertible.** "Inversible" in a unital ring means having a two-sided
  inverse. This is Mathlib's `IsUnit`.
- **Nilpotent.** "*a* est nilpotent" means *a*ⁿ = 0 for some *n* ∈ ℕ, as in the
  proof on PDF page 278 ("Soient *a* ∈ *A* et *n* ∈ ℕ tels que *a*ⁿ = 0"). This is
  Mathlib's `IsNilpotent a`, defined as `∃ n : ℕ, a ^ n = 0`. In a nontrivial
  ring, `n = 0` is impossible because `a ^ 0 = 1 ≠ 0`.
- **Spectrum = {0}.** The equality Spec(*a*) = {0} is equality of subsets of ℂ,
  `spectrum ℂ a = ({0} : Set ℂ)`.

## The spectrum and its sign convention

Mathlib defines `spectrum R a` as the complement of `resolventSet R a =
{r : R | IsUnit (algebraMap R A r - a)}`
(`Mathlib/Algebra/Algebra/Spectrum/Basic.lean`). Hence `spectrum.mem_iff` gives
`r ∈ spectrum R a ↔ ¬IsUnit (algebraMap R A r - a)`. The source instead takes
λ for which *a* − λ1_*A* is not invertible. The two shifts differ by negation:

  *a* − λ1_*A* = −(λ1_*A* − *a*),

and an element is a unit exactly when its negative is (`IsUnit.neg_iff`). So the
two definitions give the same set. The lemma
`mem_spectrum_iff_not_isUnit_sub_smul_one` proves this in Lean:
`z ∈ spectrum ℂ a ↔ ¬ IsUnit (a - z • (1 : A))`. Its proof rewrites with
`spectrum.mem_iff`, `Algebra.algebraMap_eq_smul_one`, `neg_sub` and
`IsUnit.neg_iff`. The scalar multiple `z • (1 : A)` is the source's λ1_*A*.
No parallel spectrum definition is introduced.

## Nontriviality

The two spectrum propositions assume `[Nontrivial A]`, that is `(0 : A) ≠ 1`.
The source identifies the subalgebra ℂ1_*A* with ℂ, so λ ↦ λ1_*A* is injective.
In particular 1_*A* ≠ 0, which is `Nontrivial A`. Conversely, in a nontrivial
algebra `algebraMap ℂ A` is injective, since it is a ring homomorphism out of a
field. So `Nontrivial A` is exactly what the source's identification requires.

The premise is essential. Mathlib admits the zero algebra, for example `PUnit`
with the instance `PUnit.algebra`, and `spectrum.of_subsingleton` gives every
element of a subsingleton algebra empty spectrum. The zero algebra has rank
`0 ≤ ℵ₀`. Without the premise, the nonempty-spectrum assertion would fail for
it. The singleton-zero equivalence would fail too: `0` is nilpotent, but its
spectrum is `∅ ≠ {0}`. A private probe checked in Lean that both unguarded
conclusions are false for `PUnit`. The division-algebra propositions need no
extra premise, because `DivisionRing D` already includes `Nontrivial D`.

## Division-algebra scalarity and the canonical map

The source's conclusion "*A* = ℂ" is read through its identification of ℂ with
ℂ1_*A*. It says that every element of the division algebra is a scalar multiple
λ1_*A* of the unit, with λ unique. `AmitsurDivisionAlgebraStatement` says that
the actual map `algebraMap ℂ D : ℂ →+* D`, z ↦ z • 1, is bijective. Injectivity
holds in any case (a ring homomorphism from a field to a nontrivial ring). The
content is surjectivity, that is, *D* = ℂ1_*D*. The canonical map is essential:
a bijection between ℂ and *D* that is unrelated to the algebra structure, or an
abstract isomorphism of rings, would not express the source's identification.

`AmitsurDivisionAlgebraEquivStatement` is an optional reformulation as an
isomorphism of complex algebras `ℂ ≃ₐ[ℂ] D`. It is explicitly normalized to agree
with `algebraMap ℂ D` at every `z`. It does not replace the bijectivity
statement. The two are equivalent by
`amitsurDivisionAlgebraStatement_iff_equivStatement`. (Every `ℂ`-algebra map `ℂ → D` agrees with `algebraMap ℂ D` anyway, by
`AlgHom.commutes`, because `ℂ` is the initial complex algebra. Still, the
normalization makes the identification explicit in the statement.)

## Universes

The carrier `A : Type u`, or `D : Type u`, lies in an arbitrary universe `u`.
The scalar field ℂ stays in `Type`, so the algebra instances are
`Algebra.{0, u} ℂ A`. `Module.rank ℂ A : Cardinal.{u}` is compared with
`Cardinal.aleph0.{u}`. All propositions have the single universe parameter `u`.
`AmitsurTheoremStatement.{u}` quantifies over all carriers in `Type u`.

## What the statements do not claim

- **No proof.** None of the propositions is proved, and none is used as a
  hypothesis. The only theorems in the module are the sign comparison and the
  comparison of the two division-algebra formulations. Neither of them proves
  any part of Amitsur's theorem.
- **No algebraicity.** The hypotheses do not include algebraicity, a common
  spectral decomposition, or nonemptiness of spectra. A countable-dimensional
  complex algebra need not be algebraic. For example, the polynomial algebra
  ℂ[*t*] has countable dimension, but *t* satisfies no nonzero polynomial. (Its
  units are the nonzero constants, so the spectrum of *t* is all of ℂ.) This is
  an informal remark and is not formalized here.
- **No one-sided resolvent.** Appendix B.III needs a scalar shift with **no left
  inverse**. In a general ring, failure of (two-sided) invertibility does not
  give that. These statements only say that `a - z • 1` is not a unit for `z` in
  the spectrum. They do not discharge the stronger one-sided assertion used in
  B.III.
- **Not B.II.** Schur's lemma in B.II concerns possibly nonunital algebras and
  simple modules. It is a separate statement.

## Source proof, for later proof work

This is not formalized here, but it is recorded for a later proof task. Renard
first deduces a) from b): if some *a* ∉ ℂ, every *a* − λ1_*A* is nonzero and thus
invertible in a division algebra, so Spec(*a*) = ∅. For b), if Spec(*a*) = ∅, the
uncountable family {(*a* − λ1_*A*)⁻¹ | λ ∈ ℂ} is linearly dependent, since the
dimension is at most countable. Clearing denominators yields a nonconstant
polynomial *P* with *P*(*a*) = 0. Factoring *P* over ℂ then contradicts the
invertibility of every *a* − α1_*A*. If *a*ⁿ = 0, then *a* is not invertible.
For λ ≠ 0, *a* − λ1_*A* has inverse −λ⁻¹ Σ_{i=0}^{n} (λ⁻¹*a*)ⁱ. For the converse,
the same argument over the uncountable set ℂ ∖ {0} yields *P*(*a*) = 0 with
*P*(*t*) = *c tⁿ* (*t* − α₁)…(*t* − α_r) and all α_j ≠ 0. Cancelling the invertible
factors gives *n* > 0 and *a*ⁿ = 0.

## Provenance and credit

The three required propositions are source statements from the Théorème of
B.I. They are read through its Définition of the spectrum and its identification
of ℂ1_*A* with ℂ. The optional `AmitsurDivisionAlgebraEquivStatement` and the entry conjunction
`AmitsurTheoremStatement` are packagings of Théorème a) and of the whole
Théorème. Worker 6 prepared the formulation of the three required propositions
in the task. Worker 6 also wrote a private feasibility probe whose proof of the
sign comparison is reused here. Both are credited as coauthorship.

## Checks

The module compiles in Lean environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
with no errors or warnings. Every proposition was inspected and reports
`statement_returns_prop: true`. A private probe printed every declaration with
universes. It checked the presence of `[Nontrivial A]`, the failure of the
unguarded conclusions for `PUnit`, the instance `PUnit.algebra`, and the
automatic agreement of complex algebra isomorphisms `ℂ ≃ₐ[ℂ] D` with
`algebraMap ℂ D`. The two
proved lemmas depend only on the axioms `propext`, `Classical.choice` and
`Quot.sound`.
