# Complex-place parameters of isobaric data and actual Hecke families

Worker 241 authored this supporting-definition unit for Task 7466
(`d1162e86-f3f9-4420-b56a-8fc6d6737f83`). Its provenance is internal: it composes
the Library's actual cuspidal constituents, actual Hecke characters and selected
completion embeddings to formulate B7 and its use along standard-B6 chains.

All field-dependent declarations have the sole universe parameter `uF`, for
`F : Type uF`. The field is a number field. Every place below is the actual subtype
`{v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}`;
there is no additional place index or spectral-presentation universe.

## Constituent data

In namespace `Langlands.Automorphic.IsobaricData`,
`HasComplexPlaceParameter D v ds` requires
`[CompactSpace (AdeleQuotient F)]`, as do the published cuspidal classes. It means
there are a natural number `b`, a family
`σ : Fin b → PositiveRankCuspidalClass F`, and lists `d j` such that

```lean
Finset.univ.val.map σ = D
∀ j, (σ j).HasComplexPlaceParameter v (d j)
ds.Perm (List.ofFn d).flatten
```

The equality enumerates the complete multiset `D`, with every constituent and
its multiplicity. Flattening includes every entry of every constituent block,
also with its multiplicity. In particular, repeated constituents and repeated
character data are retained. The relation concerns constituent data; it
constructs no noncuspidal automorphic representation.

The constituent predicate is the published
`PositiveRankCuspidalClass.HasComplexPlaceParameter`, whose meaning is the
literal standard-module embedding. This unit does not assert that this literal
predicate is invariant under permutation. It closes the *aggregate* list under
permutation. Consequently the singleton lemma is precisely

```lean
(IsobaricData.ofCuspidal c).HasComplexPlaceParameter v ds ↔
  ∃ ds', c.HasComplexPlaceParameter v ds' ∧ ds.Perm ds'
```

The proved lemmas in this namespace are:

- `HasComplexPlaceParameter.length_eq`: attachment gives `ds.length = D.rank`.
- `HasComplexPlaceParameter.of_perm`: attachment to `ds` and `ds.Perm ds'`
  give attachment to `ds'`.
- `hasComplexPlaceParameter_zero`: the empty data are attached to `ds` if and
  only if `ds = []`.
- `hasComplexPlaceParameter_ofCuspidal`: the singleton equivalence displayed
  above.
- `HasComplexPlaceParameter.eq_zero_iff`: under attachment, `D = 0 ↔ ds = []`.

For the length proof, `Fin.univ_val_map` turns the constituent enumeration into
the multiset of `List.ofFn σ`. The published cuspidal length lemma identifies
each block length with its constituent rank; the length of the flattening is
their sum. Permutation preserves length and composes with the witnessing
permutation. Empty data have rank zero, and the converse uses the empty
enumeration. For singleton data, taking multiset cardinalities forces `b = 1`;
the unique constituent is `c`. Finally, the positivity of every constituent rank,
as expressed by the published `rank_pos_iff`, proves the emptiness equivalence.

## Actual Hecke characters

The declarations in namespace `Langlands.Global.HeckeCharacter` require no
adelic-quotient compactness and allow arbitrary Hecke quasi-characters; they
impose no unitarity condition.

`HasComplexPlaceParameter χ v d` is the pointwise equality

```lean
∀ x : (InfiniteCompletion F v.1)ˣ,
  χ.infiniteComponent v.1 x =
    d.character
      (Units.map
        (NumberField.InfinitePlace.Completion.extensionEmbedding v.1).toMonoidHom x)
```

Here `χ` is an actual continuous character of the actual idele-class group.
Its `infiniteComponent` is the published restriction through the local class
inclusion. The right side evaluates the actual character in
`ComplexCharacterData` on the same local unit, mapped to `ℂˣ` by the selected
completion embedding. This is the embedding used by the Library's place actions
and `InfinityType.coordinate`; the latter first evaluates a full archimedean
idele at the chosen place. No alternative complex isomorphism is chosen.

For `μ : Fin n → HeckeCharacter F`,
`FamilyHasComplexPlaceParameter μ v ds` means

```lean
∃ d : Fin n → ComplexCharacterData,
  (∀ i, (μ i).HasComplexPlaceParameter v (d i)) ∧
    ds.Perm (List.ofFn d)
```

Every family member occurs, including repetitions. The proved lemmas are:

- `FamilyHasComplexPlaceParameter.length_eq`: `ds.length = n`.
- `FamilyHasComplexPlaceParameter.of_perm`: permutation of `ds` preserves
  attachment.
- `familyHasComplexPlaceParameter_zero`: a family indexed by `Fin 0` has
  precisely the empty list.
- `familyHasComplexPlaceParameter_one`: a family indexed by `Fin 1` satisfies
  attachment if and only if
  `∃ d, (μ 0).HasComplexPlaceParameter v d ∧ ds = [d]`.

These proofs use preservation of length by permutation, `List.length_ofFn`,
empty functions, and the fact that a permutation of a singleton list is that
singleton. They do not use character classification.

## Motivation and scope

These definitions and elementary list proofs are internal bookkeeping, not
translations of a theorem in the following sources. The registered operator
note `operator-external-inputs-plan-2026-11-16`, *Formalizing the large external
inputs of the local Langlands correspondence for GL_n* (16 November 2026),
Section 2.2 B6–B7 (LaTeX lines 197–199), Section 4.6 and Section 4.8,
especially the infinity-type paragraph (lines 910–911), motivates the later
transport and endpoint statements.

Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the
Trace Formula* (1989), registered source
`arthur-clozel-1989-base-change`, Chapter III, Definition 4.1 and Theorem 4.2(c),
printed p.202 / PDF p.216, discuss representations induced from unitary cuspidal
data and their weak lifts. Theorem III.5.1, printed p.212 / PDF p.226, upgrades
weak lifting to strong lifting for those representations. These passages were
read as motivation; their compatibility theorems are not proved here.

This unit proves no parameter existence or uniqueness, classification of
continuous characters, weak base-change compatibility, regular-algebraicity
comparison, or finite-to-infinite Hecke endpoint comparison. In particular,
equality of finite Euler products is not an assumption in these definitions
that supplies an archimedean conclusion. A separate later statement formulates
the endpoint comparison as a theorem with C2 as a named premise. B7 transport,
the regular-algebraicity bridge and representation realization remain separate.
