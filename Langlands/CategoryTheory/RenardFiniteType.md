# Renard's finite-type objects and Noetherian-category convention

This definition unit translates Renard's Appendix A.I.2–A.I.3, printed pages 248–249 / PDF254–255, using Mathlib's actual categorical subobjects. It provides six Prop-valued predicates in namespace `Langlands.Renard`. It supplies definitions only; the equivalences and examples discussed in the source remain successor statement and proof obligations.

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, registered source `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The retained file is `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`. PDF254–255 were read in full and visually checked. The current project note `notes/renard/appendix-a-corrections.md` was consulted; its three other Appendix A discrepancies concern different passages. No dedicated `notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` was present in the published or project notes at authoring.

The supplementary registered source `renard-2010-corrections-complements`, SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, is the author's correction list for the 2010 edition, retained at `/home/taskhub/pilot/literature/Renard — Représentations des groupes réductifs p-adiques- corrections et compléments (2010 edition errata).pdf`. Its PDF18–19, including the Appendix A corrections, were read. Those pages do not address the A.I.3 repairs below. This limited check does not assert that the entire errata document was audited or that these repairs are author-issued corrections.

## Actual subobject order and universe scope

Throughout, `C : Type u` has `Category.{v} C`, with independent object and Hom universes. No abelian structure, zero object, essential smallness, or `WellPowered` instance is required.

`CategoryTheory.Subobject X` is Mathlib's quotient of monomorphisms into `X` by isomorphism over `X`. Its existing partial order is factorization of the inclusion arrows: `P ≤ Q` means the arrow for `P` factors through that for `Q`. This is the source order in A.I.2. The top subobject is the class of the identity of `X`. Every `IsLUB` in the file uses this order. The file introduces no alternate order or complete-lattice data.

The size convention quantifies over `Set (Subobject X)`, the subsets of the actual, possibly large subobject type at the given universes. For a family of subobjects represented by a function, its range is such a subset, so multiplicities do not affect its upper bounds. No small representative type is chosen and no smallness theorem is claimed.

## Definitions

All six declarations below are ordinary transparent `def`s returning `Prop`; none is registered as a typeclass.

| Declaration in `Langlands.Renard` | Meaning |
| --- | --- |
| `HasSubobjectUnions X` | Every subset of `Subobject X` has a least upper bound. |
| `HasAllSubobjectUnions C` | `HasSubobjectUnions X` holds for every object of `C`. |
| `IsFiniteTypeObject X` | Unions exist for `X`, and every nonempty chain of proper subobjects has a proper union. |
| `HasFiniteSubcoverProperty X` | Unions exist for `X`, and every subobject cover of `X` has a finite subcover. |
| `IsNoetherianObject X` | Every nonempty subset of `Subobject X` has a maximal element. |
| `IsNoetherianCategory C` | All subobject unions exist, and every finite-type object is Noetherian. |

`HasSubobjectUnions X` is exactly

```lean
∀ S : Set (Subobject X), ∃ U : Subobject X, IsLUB S U
```

There is no nonemptiness restriction here. In particular, it includes existence of the empty union, which is a least subobject in the existing order. The predicate asserts existence without choosing any union operation.

The second conjunct of `IsFiniteTypeObject X` is exactly

```lean
∀ S : Set (Subobject X), S.Nonempty → IsChain (· ≤ ·) S →
  (∀ P ∈ S, P ≠ ⊤) → ¬ IsLUB S ⊤
```

Together with its first conjunct `HasSubobjectUnions X`, this says that the union of each such chain exists and is proper. Indeed, least upper bounds in a partial order are unique: once the existing union is supplied, excluding top as a least upper bound excludes equality of that union with top. Under Renard's standing `HasAllSubobjectUnions C` assumption, the first conjunct is already available for every object, so the predicate recovers his chain condition exactly. Retaining it in the object predicate prevents the condition from holding merely because unions are unavailable.

The second conjunct of `HasFiniteSubcoverProperty X` is

```lean
∀ S : Set (Subobject X), IsLUB S ⊤ →
  ∃ T : Finset (Subobject X),
    (T : Set (Subobject X)) ⊆ S ∧
      IsLUB (T : Set (Subobject X)) ⊤
```

Its first conjunct is again `HasSubobjectUnions X`. This is a named comparison condition, not a definition of finite type and not an assumed or proved equivalence with the chain condition. Neither the covering subset nor its finite subcover is required to be nonempty.

`IsNoetherianObject X` directly formalizes the primary source definition on PDF254:

```lean
∀ S : Set (Subobject X), S.Nonempty →
  ∃ P ∈ S, ∀ Q ∈ S, P ≤ Q → Q = P
```

The witness is a maximal element of the subset, not necessarily its greatest element. This predicate has no union-existence assumption. Its equivalence with Mathlib's `CategoryTheory.IsNoetherianObject X`, defined via `WellFoundedGT (Subobject X)`, is explicitly deferred to a successor; the current file does not silently identify them.

Finally, `IsNoetherianCategory C` is

```lean
HasAllSubobjectUnions C ∧
  ∀ X : C, IsFiniteTypeObject X → IsNoetherianObject X
```

Thus unavailable unions cannot make the category predicate vacuous. This preserves the all-unions context of the source's PDF255 category convention. Mathlib's `CategoryTheory.Noetherian` instead requires essential smallness and Noetherianity of every object. That different category predicate is neither used nor asserted equivalent here.

## Repairs to the printed wording

These are internal mathematical diagnoses verified against the rendered original, not claims of an author-issued erratum.

1. At the start of A.I.3 on PDF254, the source selects a subset `U` of the subobjects of `X` and an element `A` in `U`, but then calls `X` maximal in `U`. The surrounding criterion compares `A` with `B`, so the element called maximal must be `A`. The Lean formula accordingly chooses `P ∈ S` and tests its maximality.
2. At the top of PDF255, the compactness paragraph prints the cover equation with right side `A`. The object being characterized and the concluding finite-cover equation use `X`; the cover hypothesis therefore has right side `X`. In the subobject order, this becomes `IsLUB S ⊤`.
3. The source's maximal-element characterization by chains must quantify over nonempty chains: the empty chain has no maximal element, including for a Noetherian zero object. Likewise, the chain in the finite-type definition must be nonempty. For a zero object, the empty union is already the top subobject; admitting the empty chain would therefore exclude zero from finite type, contrary to the source's finitely generated module example. This file puts `S.Nonempty` explicitly in the finite-type predicate. It does not yet state the maximal-chain equivalence. Empty finite subcovers remain allowed, as needed for zero.
4. The source glosses a proper subobject as not isomorphic to `X`. Here properness means inequality of the subobject class with top, or equivalently that its inclusion arrow is not an isomorphism. Mathlib's `Subobject.isIso_arrow_iff_eq_top` and `Subobject.isIso_iff_mk_eq_top` express this distinction intrinsically. An abstract isomorphism between the domain of a monomorphism and `X` does not make that particular monomorphism invertible, so abstract domain nonisomorphism cannot replace `P ≠ ⊤`.

## Deferred mathematical obligations and provenance

The implementation follows the source definitions with the explicit repairs and existence conjuncts above, incorporating Worker 6's passage audit and task specification. It proves no maximal-subset/chain/stabilizing-sequence equivalence; no chain/finite-cover or `IsCompactElement ⊤` equivalence; no Noetherian/all-subobjects-finite-type equivalence; and no comparison with finite generation in actual `ModuleCat R` or with a left Noetherian ring. The source's left-module convention matters for that eventual ring comparison. The later A.VI.3 locally finite-type and composition-factor assertions also remain separate.

Renard cites [25], Proposition 1.6.1 and Lemma 3.6.1, and [37], 4.10 Theorem 1, for some of those claims. Those references were not read for this unit and supply no verified proof evidence here. Categorical finite presentability is not used. The only imports are the pinned Mathlib subobject-lattice and preorder-chain APIs; no new axioms or proof holes occur.
