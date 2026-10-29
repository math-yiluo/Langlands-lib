# Proof of the canonical subobject-complement comparison

This module proves the published statement
`Langlands.Renard.SubobjectComplementComparisonStatement C` of
`Langlands.CategoryTheory.Renard.SubobjectComplementComparisonStatements` for
every `C : Type u` with `[Category.{v} C]` and `[Abelian C]`. The object
universe `u` and the Hom universe `v` are independent. The statement, its
conventions and its provenance are explained in the statement's own Markdown.
This module imports the statement by Lean name and does not change it, nor the
imported `Langlands.CategoryTheory.RenardSemisimplicity` pair that defines
`EverySubobjectHasComplement`.

No hypothesis is added. There is no smallness, `WellPowered`, arbitrary
coproduct, complete-lattice, Grothendieck, AB6, local-finite-type, Noetherian,
module or finite-dimensionality assumption, and `ComplementedLattice` is never
assumed. Zero objects and zero subobjects are included. The axioms used are
only `propext`, `Classical.choice` and `Quot.sound`.

## Source and provenance

The motivating source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.VI.2(9), printed page 263 / PDF page 269, ends with: if `A ∩ B = 0` and
`A + B = C`, then `C ≃ A ⊕ B`. A.VII condition (iii), printed page 265 / PDF
page 271, asks that every subobject `E′` of `E` have a subobject `E″` with
`E = E′ ⊕ E″`. Both pages were read for this proof.

The source proves neither the full equivalence nor its comparison with
lattice complements. Both are derived internal comparisons, as the statement's
Markdown records. The source gives the direction from zero intersection and
full sum to a direct sum. The converse and the global packaging are proved here
from the definitions, not from a printed argument. The three-way
semisimplicity lemma of A.VII, which uses the Grothendieck and local-finite-type
hypotheses of A.VI.3, is neither used nor proved.

## Declarations

All declarations are in namespace `Langlands.Renard`.

| Declaration | Type |
| --- | --- |
| `subobjectComplementComparison` | `∀ (C : Type u) [Category.{v} C] [Abelian C], SubobjectComplementComparisonStatement C` |
| `canonicalSubobjectComplement` | `∀ (C : Type u) [Category.{v} C] [Abelian C], CanonicalSubobjectComplementStatement C` |
| `everySubobjectComplementedLattice` | `∀ (C : Type u) [Category.{v} C] [Abelian C], EverySubobjectComplementedLatticeStatement C` |

`subobjectComplementComparison` is the proof of the aggregate, the pair
`⟨canonicalSubobjectComplement C, everySubobjectComplementedLattice C⟩` in the
target's order. The two clause theorems are separately reusable.

## Proof route

### Pointwise comparison: `canonicalSubobjectComplement`

Fix `X : C` and actual subobjects `P Q : Subobject X`. Write
`f = coprod.desc P.arrow Q.arrow : (P : C) ⨿ (Q : C) ⟶ X`, the map induced by
the two chosen inclusions.

*Invertible map gives zero intersection.* Assume `IsIso f`. Define

```text
p := inv f ≫ coprod.desc (𝟙 (P : C)) 0 : X ⟶ (P : C)
```

Cancelling the isomorphism `f` gives `P.arrow ≫ inv f = coprod.inl` and
`Q.arrow ≫ inv f = coprod.inr`. Hence `P.arrow ≫ p = 𝟙` and
`Q.arrow ≫ p = 0`: the map `p` is the projection onto `P` along `Q`. Let
`i = Subobject.ofLE (P ⊓ Q) P inf_le_left` and
`j = Subobject.ofLE (P ⊓ Q) Q inf_le_right`. Both `i ≫ P.arrow` and
`j ≫ Q.arrow` equal `(P ⊓ Q).arrow`. Therefore

```text
i = i ≫ P.arrow ≫ p = j ≫ Q.arrow ≫ p = 0.
```

So `(P ⊓ Q).arrow = i ≫ P.arrow = 0` (`Subobject.ofLE_arrow`). Since
`P ⊓ Q = Subobject.mk (P ⊓ Q).arrow` (`Subobject.mk_arrow`),
`Subobject.mk_eq_bot_iff_zero` gives `P ⊓ Q = ⊥`.

*Invertible map gives full sum.* Let

```text
g := coprod.desc (Subobject.ofLE P (P ⊔ Q) le_sup_left)
                 (Subobject.ofLE Q (P ⊔ Q) le_sup_right)
```

By the coproduct extensionality lemma, `g ≫ (P ⊔ Q).arrow = f`. The map `f` is
invertible, hence an epimorphism, so `(P ⊔ Q).arrow` is an epimorphism by
`epi_of_epi`. It is also a monomorphism. An abelian category is balanced, so
`(P ⊔ Q).arrow` is an isomorphism (`isIso_of_mono_of_epi`), and
`Subobject.eq_top_of_isIso_arrow` gives `P ⊔ Q = ⊤`.

*Lattice equalities give the invertible map.* Given `P ⊓ Q = ⊥` and
`P ⊔ Q = ⊤`, the proof applies the published theorem
`Langlands.Renard.complementarySubobjectsSum C X P Q` from
`Langlands.CategoryTheory.RenardNoetherIsomorphisms`. Its conclusion is exactly
`IsIso (coprod.desc P.arrow Q.arrow)`. That theorem and its target are reused
unchanged.

### Global comparison: `everySubobjectComplementedLattice`

Fix `X : C`. Mathlib's `complementedLattice_iff` rewrites
`ComplementedLattice (Subobject X)` as `∀ P, ∃ Q, IsCompl P Q`, for the existing
lattice and bounded order on `Subobject X`. The left side is unfolded by
`change` to the published definition
`∀ P : Subobject X, ∃ Q : Subobject X, IsIso (coprod.desc P.arrow Q.arrow)`.
Then `isCompl_iff`, `disjoint_iff` and `codisjoint_iff` turn `IsCompl P Q` into
`P ⊓ Q = ⊥ ∧ P ⊔ Q = ⊤`. Applying `canonicalSubobjectComplement C X P Q` under
the quantifiers (`forall_congr'`, `exists_congr`) proves the equivalence. The
complement `Q` is the same on both sides.

## Reuse

From the Library: `Langlands.Renard.complementarySubobjectsSum`, for the
direction from lattice equalities to the canonical map. No other Library
declaration is used besides the target statements and the imported
`EverySubobjectHasComplement`.

From Mathlib at commit `5ed2965256430c3649e86755f9576b54eca72435`:

- the subobject API: `Subobject.ofLE`, `Subobject.ofLE_arrow`,
  `Subobject.mk_arrow`, `Subobject.mk_eq_bot_iff_zero` and
  `Subobject.eq_top_of_isIso_arrow`;
- the binary coproduct API: `coprod.desc`, `coprod.inl_desc`,
  `coprod.inr_desc` and coproduct extensionality;
- `epi_of_epi`, `cancel_mono` and `isIso_of_mono_of_epi`;
- the order API: `complementedLattice_iff`, `isCompl_iff`, `disjoint_iff` and
  `codisjoint_iff`.

## Scope

The module proves exactly the binary internal comparison and its global
packaging. It proves neither the three-way semisimplicity lemma of A.VII nor
its subobject corollary. It also gives no arbitrary-sum, AB5 or AB6 argument,
supported-category decomposition or module and representation adapter. Those
remain separate obligations.
