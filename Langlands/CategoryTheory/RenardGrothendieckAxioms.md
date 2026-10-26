# Renard's AB4, AB4*, AB5 and Grothendieck-category conventions

This definition unit translates the axioms AB4, AB4* and AB5 and the definition of a Grothendieck category from Renard's Appendix A.VI.2, printed page 263 / PDF269. It provides eight Prop-valued predicates in namespace `Langlands.Renard`, module `Langlands.CategoryTheory.RenardGrothendieckAxioms`. It supplies definitions only. The source's later assertion A.VI.2(10), the existence of sums of subobjects, and all comparisons with Mathlib's exactness axioms remain successor statement and proof obligations.

## Source and reading record

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The retained file is `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`; its hash was recomputed at authoring. PDF268–270 (printed pages 262–264) were read in full. PDF269 was also rendered and checked visually, including the displayed AB5 formula.

On PDF269 the source states, in translation:

- **AB4.** Every family of objects has a product in the category.
- **AB4\*.** Every family of objects has a direct sum in the category.
- An abelian category satisfying AB4 is called *complete*; one satisfying AB4\* is called *cocomplete*.
- **AB5.** The category is cocomplete, and for every filtered increasing system `Mᵢ` of subobjects of `M` and every subobject `N` of `M`, one has `N ∩ (∑ᵢ Mᵢ) = ∑ᵢ (N ∩ Mᵢ)`. The source remarks that these sums exist by AB4\*.
- A *Grothendieck category* is a cocomplete abelian category satisfying AB5.

No separate project errata note `notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` existed in the published Library notes or project notes at authoring. The published note `notes/renard/appendix-a-corrections.md` concerns A.III.1, A.IV.1–A.IV.2 and A.VI.1, not this passage. The registered author correction list for the 2010 edition, `renard-2010-corrections-complements`, was read at its Appendix A entries on PDF18–19; none addresses these definitions. This limited check does not establish that every possible later erratum has been found. No repair of the printed wording is made in this unit.

## Universes and ambient data

Throughout, `C : Type u` carries `Category.{v} C`. Families are indexed by types `I : Type w`. The three universes `w`, `v` and `u` are independent; every declaration has level parameters in the order `w, v, u`, so `SourceAB5.{w} C` fixes the family size. Each declaration carries `@[pp_with_univ]`, so printed types show this size, as for Mathlib's `AB5OfSize`. The source writes "every family" without a size bound; this unit records the bound explicitly at size `w`.

The predicates for complete, cocomplete, AB5, Grothendieck and the directed-sum condition take actual `[Abelian C]` data as an instance argument, visible in their complete types, for example

```lean
Langlands.Renard.SourceAB5.{w, v, u} :
  (C : Type u) → [inst : Category.{v, u} C] → [Abelian C] → Prop
```

`SourceAB4`, `SourceAB4Star` and `HasIndexedSubobjectSums` do not need abelian data. No `WellPowered`, `LocallySmall`, essential-smallness, generator or separator assumption is made.

Subobjects are Mathlib's `CategoryTheory.Subobject X`, the isomorphism classes of monomorphisms into `X`, with its existing partial order: `P ≤ Q` when the inclusion of `P` factors through that of `Q`. A sum of subobjects is a least upper bound (`IsLUB`) in this order. The intersection `N ⊓ M` is Mathlib's `Subobject.inf`, the pullback intersection, available from the instance `Abelian.hasPullbacks`; this is the intersection of A.VI.2(3). No `CompleteLattice (Subobject X)` instance or other alternate order is introduced.

## Definitions

| Declaration in `Langlands.Renard` | Kind | Abelian data | Meaning |
| --- | --- | --- | --- |
| `SourceAB4.{w} C` | `abbrev` | no | `HasProducts.{w} C`: every `w`-indexed family of objects has a product. |
| `SourceAB4Star.{w} C` | `abbrev` | no | `HasCoproducts.{w} C`: every `w`-indexed family of objects has a coproduct. |
| `IsSourceComplete.{w} C` | `abbrev` | yes | The abelian category satisfies `SourceAB4.{w} C`. |
| `IsSourceCocomplete.{w} C` | `abbrev` | yes | The abelian category satisfies `SourceAB4Star.{w} C`. |
| `DirectedSubobjectSumsDistribute.{w} C` | `def` | yes | Intersection distributes over sums of nonempty directed `w`-indexed families of subobjects. |
| `SourceAB5.{w} C` | `def` | yes | `IsSourceCocomplete.{w} C ∧ DirectedSubobjectSumsDistribute.{w} C`. |
| `IsSourceGrothendieck.{w} C` | `def` | yes | `SourceAB5.{w} C`. |
| `HasIndexedSubobjectSums.{w} C` | `def` | no | Comparison condition: every `w`-indexed family of subobjects, including the empty one, has a least upper bound. |

All eight return `Prop`, and none is registered as a typeclass. The `abbrev`s are transparent aliases: `SourceAB4.{w} C ↔ HasProducts.{w} C` and `SourceAB4Star.{w} C ↔ HasCoproducts.{w} C` hold by `Iff.rfl`.

### AB4, AB4\*, complete and cocomplete

Source AB4 and AB4\* assert only existence of products and coproducts. Neither asserts any exactness. `IsSourceComplete` and `IsSourceCocomplete` record the source terminology for an abelian category satisfying these existence axioms. The `[Abelian C]` argument appears in their types but not in their bodies; it records that the source uses these words only for abelian categories. In particular, `IsSourceComplete` asserts only the existence of `w`-indexed products, not of all limits; the source's derivation of general limits is assertion (10), a separate obligation.

### The directed-sum condition

`DirectedSubobjectSumsDistribute.{w} C` is exactly

```lean
∀ (X : C) (I : Type w), Nonempty I →
  ∀ F : I → Subobject X, Directed (· ≤ ·) F →
    ∀ N : Subobject X, ∃ U : Subobject X,
      IsLUB (Set.range F) U ∧
        IsLUB (Set.range fun i => N ⊓ F i) (N ⊓ U)
```

Here `U` is the source sum `∑ᵢ Mᵢ`, and the second conjunct says that `N ∩ U` is the sum `∑ᵢ (N ∩ Mᵢ)`. Both sums are required to exist. The condition is therefore not conditional on the existence of sums and cannot hold merely because sums are absent. Least upper bounds are taken of the range of the family: the sum of a family depends only on its set of members.

The formula chooses `U` after `N`. Least upper bounds in a partial order are unique, so every such `U` is the same subobject, namely the sum of the family. The version choosing `U` once before quantifying over `N` therefore expresses the same condition. This equivalence was checked in a private Lean diagnostic and is not part of the unit.

**Filtered increasing systems.** A filtered increasing system of subobjects of `X` consists of a nonempty index set `I` with a directed preorder and an order-preserving map `F : I → Subobject X`. Such a family satisfies `Directed (· ≤ ·) F`: given `i` and `j`, choose `k` above both; then `F i ≤ F k` and `F j ≤ F k`. Mathlib's `Monotone.directed_le` provides this step. Conversely, a directed family `F` over a nonempty type `I` is an increasing filtered system for the preorder pulled back from `Subobject X`, in which `i` precedes `j` exactly when `F i ≤ F j`; this preorder is directed by hypothesis, and the subobjects, hence the sums, are unchanged. A system indexed by the objects of a filtered category gives a directed family of its values in the same way. The predicate therefore quantifies over the source's filtered increasing systems indexed in `Type w`, using one uniform form.

The empty family is excluded explicitly by `Nonempty I`, following the convention that filtered systems are nonempty.

### AB5 and Grothendieck categories

`SourceAB5.{w} C` is the conjunction `IsSourceCocomplete.{w} C ∧ DirectedSubobjectSumsDistribute.{w} C`, matching the source's two clauses. The source remarks that the sums in the formula exist by AB4\*. That existence statement is not formalized here: the directed-sum condition requires the sums to exist instead. Once a successor proves that, for abelian `C` with `HasCoproducts.{w} C`, every `w`-indexed family of subobjects has a least upper bound, the existence part of the second conjunct becomes a consequence of the first. Neither conjunct is an extra hypothesis beyond the source formula, which itself asserts equality of the two sums.

`IsSourceGrothendieck.{w} C` is defined as `SourceAB5.{w} C` for actual abelian `C`. The source's "cocomplete abelian category satisfying AB5" repeats cocompleteness, which is already the first conjunct of AB5, and the abelian structure is the `[Abelian C]` argument. The definition has no generator or separator clause, and it imposes no local smallness, because the source definition has none.

### Optional comparison condition

`HasIndexedSubobjectSums.{w} C` is exactly

```lean
∀ (X : C) (I : Type w) (F : I → Subobject X),
  ∃ U : Subobject X, IsLUB (Set.range F) U
```

It includes empty families, whose least upper bound is a least subobject, and it uses the existing categorical order. It is named for successor tasks only. It is not a conjunct or hypothesis of `SourceAB5` or `IsSourceGrothendieck`, and this unit does not prove that it follows from coproduct existence.

## Naming differences from Mathlib

The pinned Mathlib commit `5ed2965256430c3649e86755f9576b54eca72435` uses the same letters for different conditions. Its definitions in `Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic.lean` and `Mathlib/CategoryTheory/Abelian/GrothendieckCategory/Basic.lean` are:

- `CategoryTheory.AB4OfSize.{w} C`, given `HasCoproducts.{w} C`: coproducts indexed by `Type w` are exact. Source AB4 is existence of products.
- `CategoryTheory.AB4StarOfSize.{w} C`, given `HasProducts.{w} C`: products indexed by `Type w` are exact. Source AB4\* is existence of coproducts.
- `CategoryTheory.AB5OfSize.{w, w'} C`, given filtered colimits of that size: colimits over filtered categories `J : Type w'` with `Category.{w} J` are exact. Source AB5 is cocompleteness together with the subobject distributivity law above.
- `CategoryTheory.IsGrothendieckAbelian.{w} C`, for abelian `C`: `LocallySmall.{w} C`, filtered colimits of size `w`, `AB5OfSize.{w, w} C` and a separator. The source Grothendieck convention has no separator and no local-smallness clause.

These are differences of convention, not claims that a source theorem is false and not author-issued errata. The present predicates are not defined via these Mathlib classes, and no comparison between them is stated or proved here.

## Deferred obligations and provenance

This unit follows the source definitions and Worker 6's task specification for task `99601a3d-50ed-4a01-a5d7-0503d8ede01a`. The following remain separate statement and proof obligations:

- Existence of sums of arbitrary `w`-indexed families of subobjects in an abelian category with `w`-indexed coproducts, via the image of the coproduct map `Sigma.desc`, with its least-upper-bound law. This is the source remark that sums exist by AB4\*.
- Source A.VI.2(10): complete (resp. cocomplete) abelian categories have all limits (resp. colimits) of diagrams, at precise size bounds.
- Comparisons between `SourceAB5` or `IsSourceGrothendieck` and Mathlib's `AB5OfSize` or `IsGrothendieckAbelian`, under explicitly justified extra hypotheses.
- Source A.VI.3 AB6, which the source footnote defines as being locally of finite type and distinguishes from Tohoku AB6, together with finite length, the Jordan–Hölder theorem, composition-factor identities and the module-category examples on PDF270.

The only imports are Mathlib's `CategoryTheory.Abelian.Basic` and `CategoryTheory.Subobject.Lattice`. The file contains no theorems, proof holes or new axioms.
