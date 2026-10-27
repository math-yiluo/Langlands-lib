# Renard B.III: the separation lemma, unital case, through actual left-ideal quotients

`Langlands/Algebra/SeparationStatements.lean` states four `Prop`-valued
definitions for the separation lemma of Renard's Appendix B.III in the unital
case. They are the lemma itself, with its simple module realized as an actual
quotient `A ⧸ I` by a maximal left ideal, and the steps of the source proof that
lead to it. None of these propositions is proved or assumed here. The module
contains no theorems. Its `example`s only check the typing of the declarations,
the scalar structure of the quotient module, and the calculation on the class
of `1`.

## Source and errata

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Appendix B.III, printed page 273 / PDF page 279, was read in full as extracted
text and as a rendered image. B.I (Amitsur's theorem and its proof, PDF pages
277–278) and B.II (PDF page 278) were read for context.

The current Library has no `notes/errata` file for this source. The registered
2010-edition list *corrections et compléments*
(`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`) has, on its
PDF page 19, this entry for the 2010 edition's B.III: "p. 315, l.11 : enlever
« soit diviseur de zéro à droite, et donc », ce qui rend l'assertion fausse.
Lire simplement : d'après le théorème d'Amitsur B.I et sa démonstration, il
existe λ ∈ ℂ^× tel que a − λ1_A non inversible à gauche." The 2026 text already
reads this way. That list belongs to a different edition, so the 2026 text
governs here.

## The source passage

On PDF page 279 the original reads:

> **B.III Lemme de séparation**
>
> Montrons le résultat de séparation suivant :
>
> **Lemme.** *Soit A une algèbre sur ℂ de dimension dénombrable. Soit a un
> élément non nilpotent de A. Alors il existe un module simple à gauche M tel
> que a · M ≠ 0.*
>
> *Démonstration.* Quitte à remplacer *A* par *Ã* = *A* ⊕ **1**_*A*, on peut
> supposer que *A* admet une unité. Comme *a* est non nilpotent, d'après le
> théorème d'Amitsur B.I et sa démonstration, il existe λ ∈ ℂ^× tel que
> *a* − λ**1**_*A* soit non inversible à gauche. Alors
>
> *A* → *A*, *b* ↦ *b*(*a* − λ**1**_*A*)
>
> n'est pas surjectif (**1**_*A* n'est pas atteint) et le module
> *N* = *A*/*A*(*a* − λ**1**_*A*) est donc non nul. Comme *N* est de type fini,
> d'après la proposition A.VI.3, *N* admet un quotient simple *M*. On a alors
> *a* · *M* ≠ 0. En effet, si *M* = *N*/*I*, où *I* est un sous-module de *N*, et
> si *Ĩ* est l'image inverse de *I* dans *A*, alors *Ĩ* est un idéal de *A* qui
> contient *A*(*a* − λ**1**_*A*). Si de plus, on suppose que *a* · *M* = 0, alors
> *Ĩ* contient *a* · *A*. Mais alors *Ĩ* contient
> *a* − (*a* − λ**1**_*A*) = λ**1**_*A*, donc contient **1**_*A* et donc
> *Ĩ* = *A*. Comme *M* ≃ *A*/*Ĩ*, on aboutit à une contradiction. □

In English: **Lemma.** Let *A* be a complex algebra of countable dimension and
let *a* be a nonnilpotent element of *A*. Then there is a simple left module *M*
with *a* · *M* ≠ 0. *Proof.* Replacing *A* by *Ã* = *A* ⊕ 1_*A*, one may assume
that *A* has a unit. Since *a* is not nilpotent, by Amitsur's theorem B.I and its
proof there is λ ∈ ℂ^× such that *a* − λ1_*A* has no left inverse. Then the map
*A* → *A*, *b* ↦ *b*(*a* − λ1_*A*), is not surjective (1_*A* is not reached), so
the module *N* = *A*/*A*(*a* − λ1_*A*) is nonzero. As *N* is finitely generated,
Proposition A.VI.3 gives a simple quotient *M* of *N*. Then *a* · *M* ≠ 0.
Indeed, write *M* = *N*/*I* for a submodule *I* of *N*, and let *Ĩ* be the
preimage of *I* in *A*. Then *Ĩ* is an ideal of *A* containing *A*(*a* − λ1_*A*).
If moreover *a* · *M* = 0, then *Ĩ* contains *a* · *A*. But then *Ĩ* contains
*a* − (*a* − λ1_*A*) = λ1_*A*, hence 1_*A*, hence *Ĩ* = *A*. Since
*M* ≃ *A*/*Ĩ*, this is a contradiction.

## Declarations

All declarations are in namespace `Langlands.Renard`, have the single universe
parameter `u`, carry `@[pp_with_univ]`, and are `def`s returning `Prop`. Write
`A : Type u`.

| Declaration | Binders | Body | Source |
| --- | --- | --- | --- |
| `NonnilpotentLeftResolventStatement A` | `[Ring A] [Algebra ℂ A]` | `Module.rank ℂ A ≤ Cardinal.aleph0 → ∀ a : A, ¬ IsNilpotent a → ∃ z : ℂ, z ≠ 0 ∧ ∀ b : A, b * (a - algebraMap ℂ A z) ≠ 1` | proof, sentence 2 |
| `PrincipalLeftIdealProperStatement A` | `[Ring A]` | `∀ x : A, (Submodule.span A ({x} : Set A) ≠ ⊤ ↔ ∀ b : A, b * x ≠ 1)` | internal auxiliary for the map *b* ↦ *b*(*a* − λ1_*A*) |
| `LeftShiftSimpleQuotientStatement A` | `[Ring A] [Algebra ℂ A]` | `∀ (a : A) (z : ℂ), z ≠ 0 → (∀ b : A, b * (a - algebraMap ℂ A z) ≠ 1) → ∃ I : Submodule A A, IsCoatom I ∧ Submodule.span A {a - algebraMap ℂ A z} ≤ I ∧ IsSimpleModule A (A ⧸ I) ∧ a • I.mkQ 1 ≠ 0` | proof, from "Alors" to the end |
| `UnitalSeparationStatement A` | `[Ring A] [Algebra ℂ A]` | `Module.rank ℂ A ≤ Cardinal.aleph0 → ∀ a : A, ¬ IsNilpotent a → ∃ I : Submodule A A, IsCoatom I ∧ IsSimpleModule A (A ⧸ I) ∧ a • I.mkQ 1 ≠ 0` | Lemme, unital case |

`A` and its instances are explicit binders in each declaration header, not
section variables. `PrincipalLeftIdealProperStatement` has no complex-algebra
binder because its formula uses none. These are four separate propositions.
The module has no entry conjunction and no implication between them. Those
implications are the work of later proofs; the informal route is recorded below.

## Conventions used

- **Algebras.** By the book's convention (PDF page 12) rings need not be unital.
  The source proof first reduces to a unital algebra. This module states only
  that unital case: `[Ring A] [Algebra ℂ A]` is a unital associative ring, possibly
  noncommutative, with a ring homomorphism `algebraMap ℂ A` into its center.
  `Algebra.algebraMap_eq_smul_one` gives `algebraMap ℂ A z = z • (1 : A)`, the
  source's λ1_*A* with λ = `z`. No commutativity, finite dimension, topology,
  norm, algebraicity or representation origin is assumed.
- **Countable dimension.** "De dimension dénombrable" is
  `Module.rank ℂ A ≤ Cardinal.aleph0`: the algebra has a finite or countably
  infinite basis over ℂ. This matches B.I, whose hypothesis the proof invokes,
  "de dimension au plus dénombrable". The rank is Mathlib's cardinal-valued
  `Module.rank`, not `Module.finrank` and not countability of the underlying set.
- **Nilpotent.** `IsNilpotent a` is `∃ n : ℕ, a ^ n = 0`.
- **No left inverse.** "Non inversible à gauche" is the exact product condition
  `∀ b : A, b * (a - algebraMap ℂ A z) ≠ 1`. This is stronger than
  `¬ IsUnit (a - algebraMap ℂ A z)` in a general ring. For example (an informal
  remark, not formalized), in the countable-dimensional algebra ℂ⟨*x*, *y*⟩/(*xy* − 1)
  the element *y* has the left inverse *x* but is not a unit, because *yx* ≠ 1.
  The shift `z ≠ 0` is the source's λ ∈ ℂ^×.
- **Left ideals.** A left ideal of *A* is `Submodule A A`, an `A`-submodule of
  the regular left module (`z • x = z * x`). This is Mathlib's `Ideal A`, which
  Mathlib documents as a left ideal. No two-sided ideal (`Ideal.IsTwoSided`) and no
  quotient ring is used. The source writes "idéal" for the preimage *Ĩ*, but *Ĩ*
  is the preimage of a submodule of *N*, so it is a left ideal. It need not be
  two-sided.
- **Principal left ideal.** *A*(*a* − λ1_*A*) is
  `Submodule.span A {a - algebraMap ℂ A z}`. By `Submodule.mem_span_singleton`,
  its elements are exactly the `b • x = b * x`, so it is the image of the map
  *b* ↦ *b*(*a* − λ1_*A*).
- **Maximal left ideal.** `IsCoatom I` says that `I ≠ ⊤` and that no left ideal
  lies strictly between `I` and `⊤`. Mathlib's `Ideal.IsMaximal I` is this
  property wrapped in a class (`Ideal.isMaximal_def`).
- **Simple module.** The class `IsSimpleModule A M` extends
  `IsSimpleOrder (Submodule A M)`: the module has exactly two submodules,
  `⊥ ≠ ⊤`. In particular a simple module is
  nonzero, as in A.VI.3. For a quotient of the regular module,
  `isSimpleModule_iff_isCoatom` gives `IsSimpleModule A (A ⧸ I) ↔ IsCoatom I`.
  The two conjuncts are therefore equivalent. Both are stated: `IsCoatom I`
  is the source's ideal *Ĩ*, and `IsSimpleModule A (A ⧸ I)` its simple module *M*.

## The quotient module and the class of 1

The quotient `A ⧸ I` is Mathlib's quotient of the left module `A` by the
submodule `I`. It has only the structures Mathlib gives it:

- the left `A`-module structure `Submodule.Quotient.module I`, with
  `b • I.mkQ x = I.mkQ (b * x)`;
- the complex vector space structure `Submodule.Quotient.module' I`, inherited
  through `IsScalarTower ℂ A A` from the algebra, with
  `z • I.mkQ x = I.mkQ (z • x)` (true by `rfl`);
- the scalar tower `IsScalarTower ℂ A (A ⧸ I)` (`Submodule.Quotient.isScalarTower`),
  so `algebraMap ℂ A z • m = z • m` (`algebraMap_smul`).

The module's `example`s check that these instances are found, and the two
equations. A private probe checked that the inferred complex structure is
`Submodule.Quotient.module' I` by `rfl`. No other scalar action is introduced.

The separating vector is the class `I.mkQ 1` of the unit. Its image under `a` is
`a • I.mkQ 1 = I.mkQ (a * 1) = I.mkQ a`. By `Submodule.Quotient.mk_eq_zero` it is
nonzero exactly when `a ∉ I`. The module proves both facts in an `example`.

So the conclusion `a • I.mkQ 1 ≠ 0` gives the source's conclusion
*a* · *M* ≠ 0, with *M* = `A ⧸ I`. Since `I` is only a left ideal, it says more
than that: *a* · *M* ≠ 0 means *aA* ⊄ *I*, whereas `a ∉ I` is a single
element. But it is exactly what the source proof shows: from *a* · *M* = 0 the
proof uses only *a* = *a* · 1_*A* ∈ *Ĩ*. In the unital case nothing is lost
(informal remark): if *M* is any simple left module and *a* · *m* ≠ 0, then
*m* ≠ 0, *Am* = *M*, the annihilator *I* of *m* is a maximal left ideal,
*M* ≃ *A*/*I* sends the class of 1 to *m*, and *a* ∉ *I*.

## Universes

The carrier `A : Type u` lies in an arbitrary universe `u`. The scalar field ℂ
is in `Type`, so the algebra instance is `Algebra.{0, u} ℂ A`. `Module.rank ℂ A`
is a `Cardinal.{u}` and is compared with `Cardinal.aleph0.{u}`. The quotient
`A ⧸ I` is `HasQuotient.Quotient.{u, u} A I : Type u`. So the simple module lives
in the carrier universe of the algebra. The source asserts the existence of
some simple module *M*. Here *M* is the concrete quotient that the source proof
constructs (*M* ≃ *A*/*Ĩ*), rather than an unspecified module in an unspecified
universe.

## Zero cases and the role of the hypotheses

- **No `Nontrivial A` premise.** In the zero algebra every element is nilpotent,
  so `NonnilpotentLeftResolventStatement` and `UnitalSeparationStatement` hold
  vacuously. `PrincipalLeftIdealProperStatement` holds with both sides false:
  the only submodule is `⊤`, and `b * x = 1` always holds. The premise of
  `LeftShiftSimpleQuotientStatement` is false because `0 * x = 1`. A private
  probe proved all four propositions for `PUnit` with the instance
  `PUnit.algebra`. This differs from the published B.I statements, whose
  conclusions fail for the zero algebra and which therefore assume
  `[Nontrivial A]`.
- **`z ≠ 0` matters.** For `z = 0` the premise of
  `LeftShiftSimpleQuotientStatement` would put `a` itself in `I`, and then
  `a • I.mkQ 1 = 0`. The source's argument uses λ ≠ 0 to pass from λ1_*A* ∈ *Ĩ*
  to 1_*A* ∈ *Ĩ*.
- **Nilpotent elements in the quotient step.** `LeftShiftSimpleQuotientStatement`
  has no nonnilpotence premise. It needs none: if `a` is nilpotent and `z ≠ 0`,
  then `a - algebraMap ℂ A z` is a unit and the premise is false.
- **No dimension bound in the quotient step.** The dimension bound is used only
  to obtain the shift; `LeftShiftSimpleQuotientStatement` and
  `PrincipalLeftIdealProperStatement` hold in every unital ring or algebra.

## Nonunital boundary

The source lemma concerns a possibly nonunital algebra *A* and adjoins a unit,
*Ã* = *A* ⊕ 1_*A*. (B.II and the 2010 errata write this unitization as
*A* ⊕ ℂ1_*A*, which is the meaning here too.) These declarations state only the
unital case that the source proof reaches after this reduction. They do not
state the nonunital lemma. They also do not discharge the reduction: the
countable dimension of the unitization, the comparison of nonnilpotence of the
original element in *A* and in *Ã*, the restriction of the action of *Ã* to *A*,
and the comparison of simple complex modules over *A* with simple modules over
*Ã*. Those remain separate obligations.

## Relation to B.I

The Library's `Langlands.Algebra.AmitsurStatements` states Amitsur's theorem
B.I with Mathlib's two-sided `spectrum` (`IsUnit`) and `[Nontrivial A]`. For a
nonnilpotent `a` those statements give a nonzero `z` with
`a - algebraMap ℂ A z` not a unit. They do not give a shift with no left
inverse, which is what B.III needs. This module does not import them.
`NonnilpotentLeftResolventStatement` is a separate, stronger proposition. The
source obtains it from B.I "et sa démonstration", that is, by running the proof
of B.I with left inverses.

## Informal proof route, for later proof work

This is not formalized here.

1. `NonnilpotentLeftResolventStatement`. Let `A` be nontrivial (otherwise `a` is
   nilpotent). Suppose every `a - z` with `z ≠ 0` has a left inverse `b_z`. Then
   `b_z ≠ b_w` for `z ≠ w`: otherwise `b (a - z) = 1 = b (a - w)` gives
   `(w - z) b = 0`, so `b = 0` and `0 = 1`. The uncountable family `(b_z)` is linearly dependent, since
   the dimension is countable: `Σ μ_i b_{z_i} = 0` with distinct `z_i` and some
   `μ_k ≠ 0`. Multiplying on the right by `Π_j (a - z_j)` (the factors commute)
   gives `Q(a) = 0` for `Q(t) = Σ_i μ_i Π_{j≠i} (t - z_j)`, and
   `Q(z_k) = μ_k Π_{j≠k} (z_k - z_j) ≠ 0`. Factor
   `Q = c · Π_k (t - α_k) · t^m` with `c ≠ 0` and all `α_k ≠ 0`. Multiplying
   `Q(a) = 0` on the left by the left inverses `b_{α_k}` in turn gives
   `c a^m = 0`, so `a` is nilpotent. This is a contradiction.
2. `PrincipalLeftIdealProperStatement`. The span is `⊤` exactly when it contains
   `1`, which by `Submodule.mem_span_singleton` means `b * x = 1` for some `b`.
3. `LeftShiftSimpleQuotientStatement`. The principal left ideal is proper by 2.
   `Ideal.exists_le_maximal`, which holds for left ideals in any semiring, gives a
   maximal left ideal `I` containing it, and `isSimpleModule_iff_isCoatom` makes
   `A ⧸ I` simple. If `a ∈ I`, then `algebraMap ℂ A z = a - (a - algebraMap ℂ A z) ∈ I`,
   so `1 = algebraMap ℂ A z⁻¹ * algebraMap ℂ A z ∈ I`, and `I = ⊤`. This
   contradicts `IsCoatom I`. So `a ∉ I`, that is `a • I.mkQ 1 ≠ 0`. This is the
   source's argument with *Ĩ* = `I` and *M* = `A ⧸ I`. Proposition A.VI.3 (a
   finitely generated module has a simple quotient) is replaced by
   `Ideal.exists_le_maximal`. The simple quotients of *N* = *A*/*A*(*a* − λ1_*A*)
   are exactly the quotients `A ⧸ I` by maximal left ideals `I` containing
   *A*(*a* − λ1_*A*).
4. `UnitalSeparationStatement` follows from 1 and 3.

## Provenance and credit

`UnitalSeparationStatement` is the Lemme of B.III in the unital case, with
the simple module realized as the quotient that the source proof builds and the
separating vector that the proof uses. `NonnilpotentLeftResolventStatement` is
the first step of the source proof. `LeftShiftSimpleQuotientStatement` is the
rest of the source proof, with *Ĩ* = `I` and *M* = `A ⧸ I`.
`PrincipalLeftIdealProperStatement` is internal. It is a general ring-theoretic
equivalence describing the source's remark that *b* ↦ *b*(*a* − λ1_*A*) is not
surjective because 1_*A* is not reached. The source does not state this
general formula.

Worker 6 prepared the four formulas and the private feasibility probe that tested
them, including the instance checks on the quotient and the calculation on the
class of `1`. Worker 221 wrote this module and this note. Both are credited as
coauthors.

## Checks

In Lean environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` the module compiles
with no errors or warnings. Each of the four propositions was inspected
separately and reports `statement_returns_prop: true`; the inspected axioms are at
most `propext`, `Classical.choice` and `Quot.sound`. A private probe printed the
full type and body of each declaration with universes. It also checked the
quotient's complex structure by `rfl` and proved all four propositions for the
zero algebra `PUnit`.
