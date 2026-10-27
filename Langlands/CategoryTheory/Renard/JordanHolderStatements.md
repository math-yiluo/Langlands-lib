# Renard A.VI.3: the Jordan–Hölder assertion

This module defines one proposition, `Langlands.Renard.JordanHolderStatement C`.
It states the Jordan–Hölder theorem of David Renard, *Représentations des
groupes réductifs p-adiques* (French edition dated 9 July 2026), Appendix
A.VI.3, printed page 263 / PDF page 269. It works in an arbitrary abelian
category and uses the published composition chains of
`Langlands.CategoryTheory.Renard.CompositionChains`, which it imports unchanged.
This is a statement only: nothing is proved here.

## The declaration

```lean
def JordanHolderStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (n m : ℕ) (c : CompositionChain X n) (d : CompositionChain X m),
    n = m ∧ ∃ e : Fin n ≃ Fin m, ∀ i : Fin n,
      Nonempty (c.factor i ≅ d.factor (e i))
```

It lives in namespace `Langlands.Renard` and has universe parameters `u, v`.

### Ambient category and universes

- `C : Type u` is the type of objects. `[Category.{v} C]` puts morphisms in
  `Type v` and `[Abelian C]` makes `C` an abelian category (Mathlib's
  `CategoryTheory.Abelian`).
- The object universe `u` and the Hom universe `v` are independent. Nothing
  forces `u = v` or a small category.
- No other hypothesis on `C` appears. In particular there is no Grothendieck
  axiom (AB5), AB4/AB4*, products or coproducts beyond those in `Abelian`,
  generators or separators, the source's local finite type condition "AB6",
  well-poweredness, local smallness, concreteness, module structure, finite
  dimension, or Jordan–Hölder lattice instance.

### Quantifiers, one by one

1. `∀ (X : C)`: an arbitrary object `X`, the source's `M`.
2. `∀ (n m : ℕ)`: two natural numbers. `n = 0` and `m = 0` are allowed.
3. `∀ (c : CompositionChain X n)`: a composition chain of `X` with `n`
   successive factors. It consists of subobjects
   `0 = B 0 < B 1 < ⋯ < B n = X` of `X` (strictly increasing, with both endpoint
   equations `B 0 = ⊥` and `B (Fin.last n) = ⊤`) whose `n` successive factors
   are simple.
4. `∀ (d : CompositionChain X m)`: a second composition chain of the same `X`,
   with `m` successive factors.
5. Conclusion, first part, `n = m`: the two chains have the same length.
6. Conclusion, second part, `∃ e : Fin n ≃ Fin m`: there is a bijection `e`
   between the factor indices of `c` and those of `d`.
7. `∀ i : Fin n, Nonempty (c.factor i ≅ d.factor (e i))`: for every factor
   index `i` of `c`, the `i`-th factor of `c` is isomorphic to the `(e i)`-th
   factor of `d`. Here `≅` is Mathlib's categorical isomorphism `Iso` in `C`,
   and `Nonempty` asserts that such an isomorphism exists without choosing one.

The source's hypothesis "if `M` admits a composition series" is the existence
of `c`. Its conclusion about "all composition series" is the universal
quantification over the two chains `c` and `d`.

### The actual factors

`c.factor i` is the published `CompositionChain.factor`. It is the actual
categorical cokernel of the actual inclusion
`Subobject.ofLE (c.subobject i.castSucc) (c.subobject i.succ) _`, that is, the
quotient `B (i + 1) / B i`. The same holds for `d.factor (e i)`. The factors
are not replaced by isomorphism classes, by abstract factors, or by elements of
an assumed Jordan–Hölder lattice.

**Indexing.** The statement keeps the published indexing repair: a chain with
`n` steps has the `n` factors `B (i + 1) / B i` for `i : Fin n`. The source
writes `B_i / B_{i-1}` for `i = 0, …, n`. That range has one index too many,
and `i = 0` would need `B_{-1}`. The intended factors are those for
`i = 1, …, n`, which are exactly the published ones.

### Multiplicities

Because `e` is a bijection, every factor of `d` is matched with exactly one
factor of `c`. So each isomorphism type occurs equally often among the factors
of `c` and among those of `d`. A weaker conclusion, such as equality of the sets
of factor isomorphism classes, would forget multiplicities and is not what is
stated.

The equation `n = m` follows from the existence of `e` (`Fintype.card_fin`).
It is kept as a separate explicit conjunct because the source states equal
lengths as its own conclusion, and it can be used directly.

### Length zero

No premise `0 < n`, `0 < m` or `¬ IsZero X` is imposed, and both endpoint
equations of the chains are kept for every length. For `n = 0` the published
endpoints force `⊥ = ⊤` in `Subobject X`. By the published
`hasCompositionChainOfLength_zero_iff`, a chain of length zero exists exactly
when `X` is a zero object. If `n = m = 0`, the conclusion holds with the empty
bijection `Fin 0 ≃ Fin 0`, and there are no factors to match. If `n = 0` and `m`
is arbitrary, the statement asserts that `m = 0`: a zero object has no
composition chain of positive length.

### Finiteness

The statement asks for no global finiteness. The supplied chains `c` and `d`
already show that `X` has finite length in the published sense
(`IsFiniteLength X`). No numerical length of an object and no chosen multiset of
factors appears: they are well defined only after a proof of this statement.

## Source correspondence

The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`, at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 268–270 were read. At A.VI.3 on PDF page 269 the source sets "Soit
`A` une catégorie abélienne" and defines simple objects and composition series.
It then says that the Jordan–Hölder theorem asserts that if `M` admits a
composition series, then all composition series have the same length and their
factors are isomorphic, up to order ("toutes les suites de composition sont de
même longueur et leurs facteurs sont isomorphes, à l'ordre près").

| Source | Lean |
| --- | --- |
| abelian category `A` | `C : Type u`, `[Category.{v} C]`, `[Abelian C]` |
| object `M` | `X : C` |
| composition series `0 = B_0 ⊂ ⋯ ⊂ B_n = M` | `c : CompositionChain X n`, `d : CompositionChain X m` |
| same length | `n = m` |
| factors isomorphic, up to order | `∃ e : Fin n ≃ Fin m, ∀ i, Nonempty (c.factor i ≅ d.factor (e i))` |

The source introduces its Grothendieck assumption (AB4* and AB5) and its
condition "AB6" (every object is a sum of finite-type subobjects) only after
this theorem, for the later results of A.VI.3. They are not premises here.

**Proof provenance.** The source gives no proof. It says that the theorem
follows from the Noether isomorphisms A.VI.2, 9 ("se démontre à partir des
isomorphismes de Noether"). This is recorded as provenance only; no proof is
implemented in this module. A separate proof unit must prove this statement.

**Errata.** The 2010 corrections (`renard-2010-corrections-complements`) are
for a different edition and are supplementary. Their final pages (PDF pages
17–19), which hold all appendix entries, were read; none concerns this
theorem. The only nearby appendix entry (2010 page 305) repairs the Zorn-lemma
argument of the later proposition. No errata file was found in the workspace,
the current Library or the project notes. This is a bounded lookup, not a claim
that no erratum exists elsewhere.

## Not included

This module defines no numerical length of an object and no chosen multiset of
composition factors. It states neither the simple-quotient proposition nor the
`JH` identities of PDF page 270, nor anything about AB6 or semisimplicity. It
does not compare with the representation-specific Jordan–Hölder modules
elsewhere in the Library. Each of these is a separate unit.

## Lean check

The module compiles in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with
no errors or warnings. Inspection reports `statement_returns_prop: true`,
universe parameters `u, v`, and only the axioms `propext`, `Classical.choice`
and `Quot.sound`.
