# Renard A.VII: the three semisimplicity conditions

Lean module: `Langlands.CategoryTheory.RenardSemisimplicity`
(`Langlands/CategoryTheory/RenardSemisimplicity.lean`), namespace `Langlands.Renard`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026 (source ID `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The section heading A.VII « Semi-simplicité » is at the foot of printed page 264 /
PDF page 270. The lemma and its corollary are on printed page 265 / PDF page 271:

> **Lemme.** Soit 𝒜 une catégorie abélienne vérifiant les hypothèses de la section
> précédente, et soit 𝐸 un objet de 𝒜. Les conditions suivantes sont équivalentes :
> (i) 𝐸 est isomorphe à une somme directe d'objets simples (ie. 𝐸 est complètement
> réductible).
> (ii) 𝐸 est la somme de ses sous-objets simples.
> (iii) Pour tout sous-objet 𝐸′ de 𝐸, il existe un sous-objet 𝐸″ de 𝐸 tel que
> 𝐸 = 𝐸′ ⊕ 𝐸″.
>
> **Corollaire.** Un sous-objet d'un objet semi-simple est semi-simple.

The conventions used here come from the same appendix:

* A.I.2 (printed page 248 / PDF page 254): a subobject is an equivalence class of
  monomorphisms, ordered by factorization; the union of any family of subobjects
  is a least upper bound in this order, when it exists.
* A.VI.1 (printed page 261 / PDF page 267): in abelian categories « somme directe »
  and `⊕` denote the coproduct.
* A.VI.2(3) (printed page 262 / PDF page 268): in abelian categories unions of
  subobjects are called sums, written `+` or `∑`.
* A.VI.3 (printed page 263 / PDF page 269): a simple object is a nonzero object
  whose only subobjects are `0` and itself.

"The hypotheses of the previous section" are those of A.VI.3 (PDF page 269):
𝒜 is a Grothendieck category in Renard's sense (cocomplete and AB5) satisfying
Renard's AB6, which the footnote there identifies with local finite type, not
Grothendieck's Tohoku AB6. These hypotheses are used only in the proof of the
lemma. The definitions here do not assume them.

## Declarations

Throughout, `C : Type u` with `[Category.{v} C]` and `[Abelian C]`, and `X : C`.
Mathlib's `Simple` is used for simple objects. It is the class with field
`mono_isIso_iff_nonzero`: a monomorphism into `X` is an isomorphism exactly when
it is nonzero. It implies `¬ IsZero X` (`Simple.not_isZero`). The published
`Langlands.Renard.isSimpleObject_iff_simple` (module
`Langlands.CategoryTheory.Renard.CompositionChains`) shows that it agrees with
Renard's A.VI.3 definition.

| Lean declaration | Kind | Content |
| --- | --- | --- |
| `IsCompletelyReducible.{w} X` | `def … : Prop` | source condition (i) at index universe `w` |
| `IsSumOfSimpleSubobjects X` | `def … : Prop` | source condition (ii) |
| `EverySubobjectHasComplement X` | `def … : Prop` | source condition (iii) |
| `IsSemisimpleObject X` | `def … : Prop` | alias: (i) at index universe `max u v` |
| `isSemisimpleObject_iff` | theorem | the alias unfolds to `IsCompletelyReducible.{max u v} X` |
| `IsCompletelyReducible.of_iso`, `.iff_of_iso` | theorems | (i) is invariant under isomorphism |
| `IsCompletelyReducible.iff_exists_iso_sigma` | theorem | (i) in the source's wording, with a chosen coproduct `∐ S` |
| `IsCompletelyReducible.of_isZero` | theorem | a zero object satisfies (i), via the empty family |
| `IsCompletelyReducible.of_simple` | theorem | a simple object satisfies (i), via a one-member family |
| `IsSemisimpleObject.of_isZero`, `.of_iso` | theorems | the same two laws for the alias |
| `IsSumOfSimpleSubobjects.of_isZero` | theorem | a zero object satisfies (ii) |
| `EverySubobjectHasComplement.of_isZero` | theorem | a zero object satisfies (iii) |

All four definitions were inspected with `statement_returns_prop: true`.
`IsCompletelyReducible` has universe parameters `w, v, u` in this order, so
`IsCompletelyReducible.{w} X` fixes the index universe and leaves `v`, `u` to
unification. The other definitions have universe parameters `v, u`.

### (i) `IsCompletelyReducible.{w} X`

```lean
∃ (I : Type w) (S : I → C) (ι : ∀ i, S i ⟶ X),
  (∀ i, Simple (S i)) ∧ Nonempty (IsColimit (Cofan.mk X ι))
```

`X`, with the maps `ι i`, is the vertex of an actual coproduct cofan of the
family `S` of simple objects. This is the universal property of the direct sum:
for every object `Y` and maps `f i : S i ⟶ Y` there is exactly one
`X ⟶ Y` whose composite with each `ι i` is `f i`. The predicate does not assume
that `C` has coproducts of any size. It asks only for this one colimit.

The source says "isomorphic to a direct sum". The theorem
`IsCompletelyReducible.iff_exists_iso_sigma` checks that the cofan formulation
is equivalent to the existence of a `w`-indexed family `S` of simple objects with
a coproduct (`HasCoproduct S`) and an isomorphism `X ≅ ∐ S` to Mathlib's chosen
coproduct. Isomorphism invariance (`of_iso`) is proved directly by composing the
injections with the isomorphism.

**Index universe.** The index type lies in a universe `w` independent of the object
universe `u` and the Hom universe `v`. The source quantifies over arbitrary
index sets.

**Empty family.** `I` may be empty. The empty cofan is a colimit exactly when its
vertex is initial, so every zero object satisfies (i). `of_isZero` proves this
with `I = PEmpty`. This matches the source's proof, where for `E = 0` the
maximal direct sum `E₀` of simple subobjects can only be the empty sum.

### (ii) `IsSumOfSimpleSubobjects X`

```lean
IsLUB {P : Subobject X | Simple (P : C)} ⊤
```

`Subobject X` is Mathlib's type of subobjects, which are isomorphism classes of
monomorphisms into `X` ordered by factorization, as in A.I.2. `(P : C)` is the
chosen underlying object of `P`. The set is the set of *all* simple subobjects of
`X`. The source's sum of a family of subobjects is its union, which A.I.2 defines
as a least upper bound in the subobject order. So "𝐸 is the sum of its simple
subobjects" says exactly that `⊤` (the subobject `𝟙 X`) is the least upper bound
of that set. When the coproduct of the simple subobjects exists (as under the
source's AB4*), this sum is also the image of the canonical map from that
coproduct to `X`. That identification is not used or proved here.

`IsLUB` asserts both that `⊤` is an upper bound and that every upper bound is
`⊤`. It needs no complete-lattice instance on `Subobject X`, and it is not an
implication that becomes vacuous when a supremum fails to exist.

A zero object satisfies (ii) (`IsSumOfSimpleSubobjects.of_isZero`). It has no
simple subobject, and its top subobject is below every subobject.

### (iii) `EverySubobjectHasComplement X`

```lean
∀ P : Subobject X, ∃ Q : Subobject X, IsIso (coprod.desc P.arrow Q.arrow)
```

The source's "𝐸 = 𝐸′ ⊕ 𝐸″" for subobjects 𝐸′, 𝐸″ of 𝐸 means that 𝐸 is the direct sum
of the two subobjects through their inclusions. In Lean, `P.arrow : (P : C) ⟶ X`
and `Q.arrow` are the actual inclusions. `coprod.desc P.arrow Q.arrow :
(P : C) ⨿ (Q : C) ⟶ X` is the canonical map from Mathlib's chosen binary
coproduct, which exists because abelian categories have finite coproducts. The
condition asks this canonical comparison to be an isomorphism. An abstract
isomorphism between `X` and some sum would not be enough. Since any two binary
coproducts are related by a unique isomorphism compatible with the injections,
the condition does not depend on the chosen coproduct. The published statement
`Langlands.Renard.ComplementarySubobjectsSumStatement` (Renard A.VI.2(9), module
`Langlands.CategoryTheory.RenardNoetherIsomorphismStatements`) uses the same
comparison map.

A zero object satisfies (iii) (`EverySubobjectHasComplement.of_isZero`, with
`Q = ⊥`): all objects involved are zero.

## The alias `IsSemisimpleObject`

The source uses "semi-simple" in the corollary without a separate definition,
for an object satisfying the equivalent conditions of the lemma. The alias
`IsSemisimpleObject X` is chosen to be condition (i) at the index universe
`max u v`, the universe of `Subobject X`. This is internal packaging, not a
separate source definition. `max u v` is the natural choice because the source's
proof of (iii) ⇒ (i) builds `E` as a direct sum of simple subobjects of `E`,
indexed by a set of subobjects. The module does not claim that
`IsCompletelyReducible.{w}` is independent of `w`, that `IsSemisimpleObject`
agrees with `IsCompletelyReducible.{w}` for any other `w`, or that the three-way
equivalence holds with an arbitrarily small `w`. A small `w` can restrict the
admissible index types.

`IsSemisimpleObject.of_isZero` records that the zero object is semisimple, and
`IsSemisimpleObject.of_iso` records isomorphism invariance.

## Reading observation on the source proof

This is an internal proof-reading observation. It is not an author-issued
erratum, and it is not a counterexample to the lemma. In the proof of
(iii) ⇒ (i), the step "𝐸 admet alors un sous-objet simple" picks a finite-type
subobject 𝐸′ and a maximal proper subobject of it. This step needs 𝐸 ≠ 0 (and
𝐸′ ≠ 0). The proof applies it only to the complement 𝐹 of a maximal direct sum
𝐸₀ ≠ 𝐸, which is nonzero. When 𝐸 = 0, condition (i) holds through the empty
direct sum. So the zero object is not excluded, and all three definitions here
hold for it. In the same paragraph, "l'ensemble des sous-objets propres de 𝐹"
appears to mean the proper subobjects of 𝐸′, because 𝐹 is introduced only in the
next sentence.

Errata: the 2010-edition correction list (`renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`)
belongs to a different edition. A text search for semisimplicity terms found no
correction to this lemma there, only uses of « lemme A.VII » as a tool. No
current-edition errata note exists in the Library at this module's base. This is
a limited observation.

## Scope and pending obligations

This module contains the three definitions, the alias and the short intrinsic
laws listed above. It does **not** prove or assume:

* the equivalence (i) ⇔ (ii) ⇔ (iii) of the lemma, which the source proves under
  its Grothendieck and AB6 (local finite type) hypotheses using Zorn's lemma;
* the comparison of (iii) with lattice complements in `Subobject X`
  (`P ⊓ Q = ⊥` and `P ⊔ Q = ⊤`);
* the corollary that subobjects of semisimple objects are semisimple;
* any reasoning with the source's AB5 or AB6, or adapters to modules or
  representations.

These remain obligations of parent task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`.
They cannot be inferred from the publication of these definitions.
