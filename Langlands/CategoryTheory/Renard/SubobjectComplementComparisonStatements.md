# Canonical subobject decompositions and lattice complements

Module: `Langlands.CategoryTheory.Renard.SubobjectComplementComparisonStatements`.
All declarations are in `Langlands.Renard`. This is an internal statement unit:
it defines three propositions and proves none of the comparison assertions.

## Source and provenance

The governing reference is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original is retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF269–271 were read directly; PDF269 and PDF271 were also checked visually.
The file's SHA256 was rechecked and the extracted text of PDF269–271 reread
before submission.

A.VI.2(9), printed263/PDF269, concludes that subobjects with zero intersection
and full sum give a direct-sum decomposition:

> En supposant de plus que 𝐴∩𝐵=0, et 𝐴+𝐵=𝐶, (𝑖𝑖) donne 𝐶≃𝐴⊕𝐵.

A.VII condition (iii), printed265/PDF271, asks that every subobject admit a
complement giving such a decomposition:

> (𝑖𝑖𝑖) Pour tout sous-objet 𝐸′ de 𝐸, il existe un sous-objet 𝐸″ de 𝐸 tel que
> 𝐸=𝐸′⊕𝐸″.

The source writes `≃` and `=` for these decompositions. Reading them as
invertibility of the map induced by the two subobject inclusions is the
normalization already used by both published companions below; it is not a
separate printed statement. The complete pointwise equivalence and its comparison with
Mathlib's `ComplementedLattice` are derived internal specifications, not
separately printed results. They explain how the published canonical-map
predicate relates to order-theoretic complements.

The published companions
`Langlands.CategoryTheory.RenardNoetherIsomorphismStatements` and
`Langlands.CategoryTheory.RenardSemisimplicity` were read. The latter is imported
unchanged. In particular, its `EverySubobjectHasComplement` is used directly;
there is no replacement definition.

The registered 2010-edition corrections,
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
have appendix entries on PDF18–19, which were read. Those entries give no
correction to these two source passages; a bounded search of their full
extracted text for Noether, complement and semisimplicity terms found no
correction to them. This is a limited observation about a different edition.
No current-edition errata file for this source was found at the workspace's or
pinned Library's `notes/errata` locations. The registered snapshot of Renard's
author page (26 October 2026) links only the 2010-edition erratum; it lists no
separate erratum for the 2026 edition.

## Scope and actual constructions

Each declaration takes exactly `C : Type u`, `[Category.{v} C]`, and
`[Abelian C]`, with independent object and Hom universes `u` and `v`.
`Subobject X` is the actual Mathlib type of equivalence classes of
monomorphisms into `X`, ordered by factorization. The infimum, supremum, bottom
and top are its existing bounded-lattice operations. No separate order or
chosen complete-lattice structure is supplied. With `pp.explicit`, the
elaborated bodies use exactly Mathlib's `Subobject.semilatticeInf`,
`Subobject.semilatticeSup`, `Subobject.orderBot` and `Subobject.orderTop` in
the first statement, and `Subobject.instLattice` with `Subobject.boundedOrder`
for `ComplementedLattice (Subobject X)` in the second. Mathlib's
`CompleteLattice (Subobject X)` instance needs local smallness,
well-poweredness, wide pullbacks and arbitrary coproducts at some universe, and
is not used.

For `P Q : Subobject X`, the map in the first statement is exactly

```lean
coprod.desc P.arrow Q.arrow : (P : C) ⨿ (Q : C) ⟶ X
```

It is determined by the two inclusion equations
`coprod.inl ≫ coprod.desc P.arrow Q.arrow = P.arrow` and
`coprod.inr ≫ coprod.desc P.arrow Q.arrow = Q.arrow`.
The source uses direct sum for the categorical coproduct in an abelian
category (A.VI.1, printed261/PDF267); the public companions explain this
normalization. Binary coproducts exist from the actual abelian structure.
The comparison concerns these inclusions, so invertibility cannot be replaced
by an unrelated abstract isomorphism between `X` and a binary sum.

There is no arbitrary-coproduct, well-poweredness, local-smallness, generator,
Grothendieck, local-finite-type, Noetherian, module or finite-dimensionality
premise. Neither `X` nor its subobjects are required to be nonzero.

## Exact statements

`CanonicalSubobjectComplementStatement C` is

```lean
∀ (X : C) (P Q : Subobject X),
  IsIso (coprod.desc P.arrow Q.arrow) ↔
    P ⊓ Q = ⊥ ∧ P ⊔ Q = ⊤
```

The right-to-left direction is, in curried form
(`A ⊓ B = ⊥ → A ⊔ B = ⊤ → IsIso (coprod.desc A.arrow B.arrow)`), the assertion
already named `ComplementarySubobjectsSumStatement C` in the public
Noether-isomorphisms module. A private development check confirmed that
`CanonicalSubobjectComplementStatement C` implies it by
`fun h X A B h₁ h₂ => (h X A B).2 ⟨h₁, h₂⟩`; this module does not import the
Noether module or record that implication. The left-to-right direction is the
additional internal comparison.
`P ⊓ Q = ⊥` expresses disjointness and `P ⊔ Q = ⊤` expresses that the two
subobjects generate `X`.

`EverySubobjectComplementedLatticeStatement C` is

```lean
∀ X : C,
  EverySubobjectHasComplement X ↔ ComplementedLattice (Subobject X)
```

The left-hand side unfolds to
`∀ P : Subobject X, ∃ Q : Subobject X,
  IsIso (coprod.desc P.arrow Q.arrow)`.
Mathlib's `ComplementedLattice` is a Prop-valued class with field
`∀ P, ∃ Q, IsCompl P Q` (`complementedLattice_iff`). In a bounded lattice
`IsCompl P Q` is equivalent to `P ⊓ Q = ⊥ ∧ P ⊔ Q = ⊤`; for `Subobject X` a
private development check obtained this by
`rw [isCompl_iff, disjoint_iff, codisjoint_iff]`, so the bottom and top of
`Subobject.boundedOrder` agree with those in the first statement. The
statement places this class on the right of an equivalence; it is never
assumed as a typeclass parameter.

`SubobjectComplementComparisonStatement C` is the closed conjunction

```lean
CanonicalSubobjectComplementStatement C ∧
  EverySubobjectComplementedLatticeStatement C
```

Every statement is a transparent `def … : Prop` with the same category and
abelian-instance binders. Each has universe parameters `u, v` in this order and
the full unapplied type
`∀ (C : Type u) [Category.{v} C] [Abelian C], Prop`, checked by assigning the
unapplied constant directly. Each body unfolds by `rfl` to the displayed
formula. The universe of actual subobjects is `max u v`; there is no
independent indexing universe or size restriction. The imported
`EverySubobjectHasComplement` has universe parameters `v, u`.

## Proof and coverage boundary

The existing Noether aggregate proof task
`d0241956-6d80-41a2-8ca8-88db6bad7b32` retains the
lattice-equalities-to-canonical-map direction. This unit neither duplicates
nor discharges that obligation. A later proof of the comparison may consume
its accepted public proof and add the converse and the global logical
packaging. It must target this exact aggregate after publication.

The source's three-way semisimplicity lemma assumes its Grothendieck and local
finite-type hypotheses. That lemma, its subobject corollary, the arbitrary-sum
arguments, AB5/AB6 reasoning, and module or representation adapters remain
separate obligations. A statement of this binary comparison alone supplies
none of those proofs.
