# Renard A.VI.3: simple objects, composition chains and simple subquotients

This module defines the constructions introduced at the start of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, Appendix A.VI.3 "Suites de Jordan-Hölder et facteurs de
composition", printed pages 263–264 / PDF pages 269–270. These are simple
objects, `Irr(A)`, composition chains (suites de composition) with their
lengths and composition factors, finite length, and `JH(M)`.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF pages 269–270 were read in full. The prompt Library has no `notes/errata`
directory. Its Appendix A discrepancy note `notes/renard/appendix-a-corrections.md`
covers A.III.1, A.IV.1–2 and A.VI.1 and records nothing for A.VI.3. The registered `renard-2010-corrections-complements` lists errata for
the 2010 edition, a different edition. Its appendix entries on PDF pages 18–19
were read. None of them corrects the definition of a simple object, a
composition chain, its length or factors, finite length, or `JH`. The only entry
there about chains of subobjects (2010 p. 305) repairs a Zorn-lemma argument in
a proof.

## Source text and its formal reading

The source works in an arbitrary abelian category `A`, before it adds the
Grothendieck and local-finite-type ("AB6") assumptions further down PDF page 269.
It says:

1. A nonzero object `M` is *simple* if every subobject of `M` is either `0`
   or `M`.
2. `Irr(A)` is the set of equivalence classes of simple objects.
3. A *composition series* (or Jordan–Hölder series) of `M` is an increasing
   sequence of subobjects of `M`, all different,
   `0 = B_0 ⊂ B_1 ⊂ ⋯ ⊂ B_n = M`, whose successive quotients
   `B_i / B_{i-1}`, `i = 0, …, n`, are simple. The integer `n` is its *length*,
   and the quotients `B_i / B_{i-1}` are the *composition factors* of `M`.
4. An object admitting a composition series is of *finite length*. Its length
   is the length of any one of its composition series.
5. On PDF page 270, `JH(M)` is the set of simple subquotients of `M`.

The source then states the Jordan–Hölder theorem: all composition series of an
object have the same length, and their factors agree up to isomorphism and
order. The source gives no proof here; it remarks that the theorem follows from
the Noether isomorphisms of A.VI.2, 9. That theorem, the
simple-quotient proposition and the three `JH` identities on PDF page 270 are
**not** part of this module (see "Scope" below).

## Ambient category and universes

Everything except the class quotient takes arbitrary `C : Type u`,
`[Category.{v} C]` and `[Abelian C]`. The object universe `u` and Hom universe
`v` are independent. The module assumes no smallness, well-poweredness,
concreteness, Grothendieck axiom, finite-type hypothesis or Jordan–Hölder
lattice instance. Subobjects are Mathlib's actual `Subobject X`: equivalence
classes of monomorphisms into `X`, ordered by factorisation. Quotients are
actual categorical cokernels.

## Declarations

All declarations are in namespace `Langlands.Renard`.

### Isomorphism classes of objects

- `ObjectClass C : Type u` is an `abbrev` for
  `Quotient (isIsomorphicSetoid C)`. Its relation is Mathlib's
  `IsIsomorphic`, that is `Nonempty (X ≅ Y)`. This section assumes only
  `[Category.{v} C]`. The quotient lies in the object universe `u`, whatever
  `v` is.
- `objectClass X : ObjectClass C` is the class map `Quotient.mk`.
- `objectClass_eq_iff : objectClass X = objectClass Y ↔ Nonempty (X ≅ Y)`
  ties equality of classes to actual categorical isomorphisms (`Quotient.eq`).
- `objectClass_surjective` says that every class is the class of an object.

The source's "classes d'équivalence d'objets simples" are read as these
isomorphism classes. The later `JH` sets are read in the same sense.

### Simple objects and `Irr`

- `IsSimpleObject X : Prop` is the source definition verbatim:
  `¬ IsZero X ∧ ∀ P : Subobject X, P = ⊥ ∨ P = ⊤`. Here `⊥` is the zero
  subobject and `⊤` is `X` itself. The nonzero clause is essential: without it
  the zero object, whose subobject lattice has one element, would satisfy the
  two-way alternative.
- `isSimpleObject_iff_simple : IsSimpleObject X ↔ Simple X` is a short intrinsic
  comparison lemma. Mathlib's `Simple X` requires every monomorphism into `X`
  to be an isomorphism exactly when it is nonzero. The proof rewrites with
  Mathlib's `simple_iff_subobject_isSimpleOrder`
  (`Simple X ↔ IsSimpleOrder (Subobject X)`). `IsSimpleOrder` is nontriviality
  together with the bottom-or-top alternative.
  - Forward: nontriviality of `Subobject X` comes from
    `Subobject.nontrivial_of_not_isZero`.
  - Backward: if `X` were zero, `Subobject.subsingleton_of_isZero` would force
    `⊥ = ⊤`, contradicting `IsSimpleOrder.bot_ne_top`.

  The remaining declarations use Mathlib's `Simple` directly; the comparison
  lemma converts between the two forms.
- `simpleClasses C : Set (ObjectClass C)` is the source's `Irr(C)`. Its
  membership is `∃ Y : C, Simple Y ∧ objectClass Y = q`.
- `objectClass_mem_simpleClasses_iff : objectClass X ∈ simpleClasses C ↔ Simple X`
  shows that membership does not depend on the representative. The proof
  transports simplicity along the isomorphism from `objectClass_eq_iff`
  (`Simple.of_iso`).

### Composition chains

`CompositionChain X n` is a structure (a `Type`, not a `Prop`) with fields:

- `subobject : Fin (n + 1) → Subobject X`, the source's `B_0, …, B_n`;
- `strictMono : StrictMono subobject`, the source's "suite croissante …, tous
  différents";
- `subobject_zero : subobject 0 = ⊥`, the source's `0 = B_0`;
- `subobject_last : subobject (Fin.last n) = ⊤`, the source's `B_n = M`;
- `simple_factor : ∀ i : Fin n, Simple (cokernel (Subobject.ofLE (subobject i.castSucc) (subobject i.succ) (strictMono i.castSucc_lt_succ).le))`.

`Subobject.ofLE A B h : (A : C) ⟶ (B : C)` is the actual inclusion morphism
between the underlying objects of two subobjects with `A ≤ B`. Its cokernel is
the actual quotient object `B / A`, as in source A.VI.2.

**Indexing repair.** The source writes the factors as `B_i / B_{i-1}` for
`i = 0, …, n`. The index `i = 0` would need `B_{-1}`, and the chain has `n`
gaps, not `n + 1`. Following the task contract, this module uses the `n`
factors `B_{i+1} / B_i` for `i = 0, …, n - 1`. In Lean the index is `i : Fin n`,
with `i.castSucc` for `i` and `i.succ` for `i + 1`. These are the same `n`
quotients the source means by `B_i / B_{i-1}` for `i = 1, …, n`.

**Endpoints and length zero.** Both endpoint equations are kept for every `n`.
For `n = 0`, `Fin 1` has one element, which is both `0` and `Fin.last 0`. The
endpoint equations then force `⊥ = ⊤` in `Subobject X`, and there are no
factors. `hasCompositionChainOfLength_zero_iff` below shows that length zero
occurs exactly for zero objects. No positive length is imposed on the zero
object.

**Redundancy kept on purpose.** Simplicity of each factor already forces
`B_i ≠ B_{i+1}`, because a simple object is nonzero. The source still states
"tous différents" separately, and the module keeps `strictMono` as a field to
match it. The field also supplies the inequality proofs used to form the
inclusions.

Accessors in namespace `CompositionChain`, for `c : CompositionChain X n`:

- `c.length : ℕ` is the number `n` of successive factors, the source's length.
  `length_eq : c.length = n` holds by `rfl`.
- `c.subobject i` gives the underlying subobjects; `c.le_succ i` is
  `c.subobject i.castSucc ≤ c.subobject i.succ`.
- `c.inclusion i : (c.subobject i.castSucc : C) ⟶ (c.subobject i.succ : C)` is
  the adjacent inclusion `Subobject.ofLE`. It is a monomorphism (instance), and
  `inclusion_arrow` records that it commutes with the arrows into `X`.
- `c.factor i : C` is `cokernel (c.inclusion i)`, the composition factor
  `B_{i+1} / B_i`. It is definitionally the cokernel in the `simple_factor`
  field. `c.factorπ i` is the actual quotient map `cokernel.π`.
- `factor_simple` is the instance `Simple (c.factor i)`.
- `c.factorClass i : ObjectClass C` is the isomorphism class of the factor.
  `factorClass_mem_simpleClasses` places it in `simpleClasses C`.

### Existence of chains and finite length

- `HasCompositionChainOfLength X n : Prop` is `Nonempty (CompositionChain X n)`.
- `hasCompositionChainOfLength_iff` unfolds it to the explicit existential
  `∃ (B : Fin (n + 1) → Subobject X) (hB : StrictMono B), B 0 = ⊥ ∧ B (Fin.last n) = ⊤ ∧ ∀ i : Fin n, Simple (cokernel (Subobject.ofLE (B i.castSucc) (B i.succ) (hB i.castSucc_lt_succ).le))`.
- `hasCompositionChainOfLength_zero_iff : HasCompositionChainOfLength X 0 ↔ IsZero X`.
- `IsFiniteLength X : Prop` is `∃ n : ℕ, HasCompositionChainOfLength X n`, the
  source's "objet admettant une suite de composition".

**No numerical length of an object.** The source defines the length of a
finite-length object as the length of any one of its composition series. That
is well defined only once the Jordan–Hölder theorem is proved. This module does
not define a numerical length of an object: there is no chosen chain and no
assumption that chain length is independent of the chain. Only the length of a
supplied chain, `CompositionChain.length`, is defined.

### Simple subquotient classes `JH`

- `simpleSubquotientClasses X : Set (ObjectClass C)` is the source's `JH(X)`.
  Membership of `q` means
  `∃ (A B : Subobject X) (h : A ≤ B), Simple (cokernel (Subobject.ofLE A B h)) ∧ objectClass (cokernel (Subobject.ofLE A B h)) = q`.
  So `JH(X)` is the set of isomorphism classes of actual simple subquotients
  `B / A` of `X`. It is defined for every object, without assuming finite
  length. It lives in the same `ObjectClass C` as `simpleClasses C`, and classes
  are compared only through `objectClass`, never through chosen
  representatives.
- `simpleSubquotientClasses_subset_simpleClasses : simpleSubquotientClasses X ⊆ simpleClasses C`.
- `CompositionChain.factorClass_mem_simpleSubquotientClasses` says that every
  composition factor class of a chain of `X` lies in `JH(X)`. The witness is
  `A = B_i`, `B = B_{i+1}`.

## Status of the lemmas in this file

The definitions are `ObjectClass`, `objectClass`, `IsSimpleObject`,
`simpleClasses`, `CompositionChain` with its accessors (`length`, `inclusion`,
`factor`, `factorπ`, `factorClass`), `HasCompositionChainOfLength`,
`IsFiniteLength` and `simpleSubquotientClasses`. The `Prop`-valued ones are
predicates. None of them is a statement target awaiting proof.

The theorems proved here are short intrinsic construction laws that make the
definitions usable:

- `objectClass_eq_iff` and `objectClass_surjective`;
- `isSimpleObject_iff_simple` and `objectClass_mem_simpleClasses_iff`;
- `CompositionChain.length_eq`, `le_succ`, `inclusion_arrow`, the `Mono` and
  `factor_simple` instances, `factorClass_mem_simpleClasses` and
  `factorClass_mem_simpleSubquotientClasses`;
- `hasCompositionChainOfLength_iff` and `hasCompositionChainOfLength_zero_iff`;
- `simpleSubquotientClasses_subset_simpleClasses`.

None of them is a source theorem.

## Scope: source results left to later units

The following source assertions are neither stated nor assumed here:

- the Jordan–Hölder theorem (equal lengths, factors isomorphic up to order);
- the well-definedness of the length of a finite-length object;
- the simple-quotient proposition (a nonzero finite-type object has a simple
  quotient; an object that is not of finite type has a simple subquotient);
- the `JH` identities: `JH(M) = JH(M') ∪ JH(M/M')`, `JH(M) = ∅ ↔ M = 0`, and
  `JH(∑ M_i) = ⋃ JH(M_i)`;
- the source's Grothendieck and "AB6" (local finite type) assumptions.

The simple-quotient proposition and the `JH` identities depend on those
assumptions. Each of these items belongs to a separate statement or proof
unit.

## Lean check

The module compiles in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with
no errors or warnings. Its declarations use only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
