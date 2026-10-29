# Renard A.IX: the sum `E_S` of all supported subobjects

Construction author: Worker 985. The construction was specified by Worker 6
in task `c8426fba-3302-4900-b3c2-a48444229ba6`, a child of the Renard whole-book
task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`. Worker 985 wrote and checked the
original pair without reusing a shared draft. The source-universe explanation
was corrected by Worker 6 (prepared draft and analysis) and Worker 199
(source checks, revision and submission) under task
`341795fa-b07c-40cf-9f40-275ad3329d50`. This correction preserves every byte
of the Lean construction and laws and of the published
`SimpleSupportSumStatements` Lean/Markdown pair.

This construction unit defines the subobject `E_S` of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, A.IX, printed page 268 / PDF page 274: the sum of all subobjects
of `E` that lie in the supported full subcategory `M_S`. The module is
`Langlands.CategoryTheory.Renard.SimpleSupportSum`, namespace
`Langlands.Renard`. It imports the public modules
`Langlands.CategoryTheory.Renard.SimpleSupport` and
`Langlands.CategoryTheory.Renard.IndexedSubobjectSums` unchanged, by Lean name.

The unit constructs the sum and proves only its defining and order-theoretic
laws. It does not prove that `E_S` is supported on `S`.

## Source and reading record

The governing original is registered as
`renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 985's original reading record reports recomputing the hash, reading
PDF273–275 (printed 267–269) in full, rendering and visually checking PDF274,
and reading PDF269–270 (A.VI.2 axioms and A.VI.3) for the meaning of *somme*
and the `JH` lemma cited below. For this correction, Worker 199 independently
recomputed both source hashes, read original PDF269–270 and PDF273–275 in
full, visually checked PDF274, and read supplementary errata PDF18–19.

The passage on PDF274 reads: "Pour tout objet `E` de `M`, on note `E_S` la somme
de tous les sous-objets de `E` qui sont dans `M_S`. Alors il est clair que
`E_S ∈ M_S`." In translation: for every object `E` of `M`, `E_S` denotes the sum
of all subobjects of `E` that lie in `M_S`; it is then clear that `E_S ∈ M_S`.
The first sentence is the definition formalized here. The second is a separate
assertion and is not formalized here (see the last section).

The setting of A.IX is a Grothendieck category `M` (AB4\* and AB5) that also
satisfies AB6, and `S` is a subset of `Irr(M)`. `M_S` is the full subcategory of
objects all of whose irreducible subquotients lie in `S`. The word *somme* is the
sum of subobjects of A.VI.2, realized by the public `subobjectSum`. PDF269
remarks that such sums exist thanks to AB4\* ("les sommes existent grâce à
AB4\*").

Errata. No project errata note
`notes/errata/renard-2026-representations-groupes-reductifs-padiques.md` exists in
the published Library notes or the project notes. The public note
`notes/renard/appendix-a-corrections.md` treats A.III.1, A.IV.1–A.IV.2 and
A.VI.1 only, and none of its findings concerns A.IX. The supplementary
2010-edition correction list `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`, was read on
PDF pages 18–19. Its entry "p. 310, l. 10 et 11 : remplacer M par E et MS par ES"
changes the old-edition letters `M, M_S` in this sentence to `E, E_S`. The 2026
text already reads `E` and `E_S`. This observation is limited to those two
pages of the 2010-edition errata.

## Binders, universes and the existence instance

All declarations have the common binders
`{C : Type u} [Category.{v} C] [Abelian C]`. The object universe `u` and Hom
universe `v` are independent; the level parameters of `simpleSupportSum` are
`u, v`. `S : Set (ObjectClass C)` and `X : C` are explicit.

`simpleSupportSubobjects S X : Set (Subobject X)` is the public set of actual
subobjects `P` of `X` with `HasSimpleSupport S (P : C)`. Since
`Subobject X : Type (max u v)`, its subtype
`↥(simpleSupportSubobjects S X)` lies in `Type (max u v)`. The construction
uses this full subtype as the index type. No smaller replacement, chosen
representative family or reindexing is used.

The only existence assumption beyond `[Abelian C]` is the coproduct of this one
family of underlying objects:

```lean
[HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]
```

It is an explicit instance argument of the definition and of every law. The
image of the coproduct map, needed by the public `subobjectSum`, is found from
`[Abelian C]`. No `WellPowered`, `LocallySmall`, concreteness, generator,
finite-length, Grothendieck, AB5, AB6 or universe-identification assumption is
made.

The full index subtype lies in `Type (max u v)`. The formal assumption
`[HasCoproducts.{max u v} C]`, equivalently
`IsSourceCocomplete.{max u v} C`, supplies the displayed instance by instance
search. This implication is correct, but the all-family hypothesis at that
size is degenerate and does not describe the intended general source setting;
the reason is explained below. It is not a premise of this construction.

Coproducts at an independent family size `w` alone need not supply a coproduct
of this syntactically larger index type. They do supply it if the precise
supported family is `w`-small. With `[HasCoproducts.{w} C]` and
`[Small.{w} (simpleSupportSubobjects S X)]`, Mathlib's
`hasCoproductsOfShape_of_small.{w} C (simpleSupportSubobjects S X)` gives
`HasCoproductsOfShape (simpleSupportSubobjects S X) C`, and hence the
one-family instance. The adapter is in
`Mathlib.CategoryTheory.Limits.EssentiallySmall`; it transports a coproduct
indexed by `Shrink.{w}` along the index equivalence. The public sum still
uses the full subtype and its actual inclusion arrows. No redefinition or
extra premise is added to `simpleSupportSum` or its laws.

## The construction

```lean
def simpleSupportSum (S : Set (ObjectClass C)) (X : C)
    [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)] :
    Subobject X :=
  subobjectSum (fun P : simpleSupportSubobjects S X => (P : Subobject X))
```

The family sends each supported subobject `P` to itself. The public
`subobjectSum` of a family `F` is
`Subobject.mk (image.ι (Sigma.desc fun i => (F i).arrow))`. Therefore
`simpleSupportSum S X` is the subobject represented by the image inclusion of
the map from the coproduct of the underlying objects of all supported
subobjects of `X` into `X`, whose restriction to the summand of `P` is
`P.arrow`. It is an actual image subobject, not a witness chosen from a proof
that a least upper bound exists, and it carries no support or maximality
property as a field.

Source correspondence: `X` is the source's `E`, `S` its `S`,
`simpleSupportSubobjects S X` the set of subobjects of `E` that lie in `M_S`,
and `subobjectSum` the A.VI.2 sum. The source assumes `S ⊆ Irr(M)`. The public
support predicate allows arbitrary sets of object classes, so the definition
also makes sense for every `S : Set (ObjectClass C)` and every abelian category
with the displayed coproduct. For `S ⊆ simpleClasses C` (the public `Irr(C)`),
whenever the displayed coproduct is supplied, it is exactly the source's
`E_S`. No later source theorem is inferred for this wider setting.

Renard's set-indexed AB4\* is expressed in the public source-axiom interface
at an independent family size `w`. For `hG : IsSourceGrothendieck.{w} C`,
the first conjunct `hG.1` supplies `HasCoproducts.{w} C`. Together with
`[Small.{w} (simpleSupportSubobjects S X)]`, the preceding adapter supplies
the needed coproduct. The smallness binder records the source's implicit
presupposition that the family of supported subobjects being summed is a
set at the chosen family size. It is not derived from `hG` or canonical AB6
by this construction. The source specialization remains conditional on that
binder, or on a proof of this family's smallness in a concrete application.
The current public `SimpleSupportSumStatements` pair implements exactly
this route, with independent `w`, `u`, `v`, leaving this construction unchanged.

The former explanation identified the source setting with all coproducts of
size `max u v`. The obstruction is internal and set-theoretic. Put
`md := Σ Z W : C, (Z ⟶ W)`, which lies in `Type (max u v)`. If there were
two distinct arrows `r, s : A ⟶ B`, each subset of `md` would define an
arrow from the coproduct of `md` copies of `A` to `B`, with component `r`
on the subset and `s` elsewhere. Distinct subsets give distinct arrows by
the coproduct leg equations. Those arrows inject into `md` by recording
their source and target, contradicting Cantor's theorem. Thus
`HasCoproducts.{max u v} C` forces every Hom to be a subsingleton. In an
abelian category `𝟙 X = 0` then makes every object zero. The same applies
when the all-family size is at least `max u v`.

This diagnosis explains a defect in the former universe interpretation,
not a defect in the one-family construction or a source theorem of Renard.
Mathlib's `CategoryTheory/Limits/SmallComplete.lean` implements the dual
product argument for `SmallCategory`, where object and Hom universes agree;
its existing instance is not being asserted to directly cover the independent
universes here. No new Lean theorem proving this diagnosis is included in
this unit. The unchanged public statement companion also records it and
retains the independent-family formulation. The original probe deriving
`IsLUB` from `isLUB_subobjectSum_set` under the oversized hypothesis is a
valid formal specialization, with the same degeneracy; the implemented
`isLUB_simpleSupportSum` already needs only the one-family instance.

## Intrinsic laws

In this table, `S X` and the coproduct instance above are arguments of every
declaration, and `P G U : Subobject X`.

| Declaration | Statement |
| --- | --- |
| `simpleSupportSum_def S X` | `simpleSupportSum S X = subobjectSum (fun P : simpleSupportSubobjects S X => (P : Subobject X))` |
| `simpleSupportSum_eq_mk S X` | `simpleSupportSum S X = Subobject.mk (image.ι (Sigma.desc fun P : simpleSupportSubobjects S X => (P : Subobject X).arrow))` |
| `le_simpleSupportSum S X hP` | `P ∈ simpleSupportSubobjects S X → P ≤ simpleSupportSum S X`, with `{P}` implicit |
| `simpleSupportSum_le S X h` | `(∀ P ∈ simpleSupportSubobjects S X, P ≤ G) → simpleSupportSum S X ≤ G`, with `{G}` implicit |
| `simpleSupportSum_le_iff S X` | `simpleSupportSum S X ≤ G ↔ ∀ P ∈ simpleSupportSubobjects S X, P ≤ G`, with `{G}` implicit |
| `isLUB_simpleSupportSum S X` | `IsLUB (simpleSupportSubobjects S X) (simpleSupportSum S X)` |
| `simpleSupportSum_eq_of_isLUB S X hU` | `IsLUB (simpleSupportSubobjects S X) U → simpleSupportSum S X = U`, with `{U}` implicit |

Monotonicity has its own binders:

```lean
theorem simpleSupportSum_mono {S T : Set (ObjectClass C)} (hST : S ⊆ T) (X : C)
    [HasCoproduct fun P : simpleSupportSubobjects S X => ((P : Subobject X) : C)]
    [HasCoproduct fun P : simpleSupportSubobjects T X => ((P : Subobject X) : C)] :
    simpleSupportSum S X ≤ simpleSupportSum T X
```

It takes the coproduct instances of both families.

Derivations from the public laws, as implemented:

- `simpleSupportSum_def` is `rfl`. `simpleSupportSum_eq_mk` is also `rfl`: it
  unfolds the public `subobjectSum` (compare the public `subobjectSum_def`).
- `le_simpleSupportSum` is the public `le_subobjectSum` at the index
  `⟨P, hP⟩` of the subtype, whose family value is `P`.
- `simpleSupportSum_le` is the public `subobjectSum_le`. Its hypothesis
  `∀ i, F i ≤ G` is supplied by `fun P => h P P.2`, where `P.2` is the
  membership proof of an element of the subtype.
- `simpleSupportSum_le_iff`: the forward direction composes
  `le_simpleSupportSum` with the given inequality by transitivity; the reverse
  direction is `simpleSupportSum_le`.
- `isLUB_simpleSupportSum` pairs the two previous laws. The upper-bound part is
  `le_simpleSupportSum`. For leastness, an upper bound `G` of the set gives the
  hypothesis of `simpleSupportSum_le`. It is proved directly for the set, not
  through `Set.range`, and so uses only the minimal instance. The public
  `isLUB_subobjectSum_set` would instead require `[HasCoproducts.{max u v} C]`.
- `simpleSupportSum_eq_of_isLUB` is uniqueness of least upper bounds in a
  partial order, `IsLUB.unique`, applied to `isLUB_simpleSupportSum`.
- `simpleSupportSum_mono` applies `simpleSupportSum_le` for `S`. Each subobject
  supported on `S` is supported on `T` by the public
  `simpleSupportSubobjects_mono hST X`, and so lies below the sum for `T` by
  `le_simpleSupportSum`.

`IsLUB` here says only that `E_S` is the least common upper bound of the set of
supported subobjects in Mathlib's order on `Subobject X`. It does not say that
`E_S` belongs to that set, that is, that `E_S` is supported on `S`. Therefore it
does not make `E_S` a maximum element of the set.

## Scope and remaining obligations

The source's next assertion, `E_S ∈ M_S`, is neither assumed nor proved, and it
is not a field or premise of any declaration here. The source calls it clear.
It would follow from A.VI.3 Lemma (iii) on PDF270,
`JH(∑_{i∈I} M_i) = ⋃_{i∈I} JH(M_i)`, which the source proves in its
Grothendieck setting using AB5. The following remain
separate successor obligations of the whole-book program: support of `E_S`, and
hence its maximality among supported subobjects; closure properties and
abelianness of `M_S`; the `JH` identities and zero detection; vanishing of Homs
and intersections across disjoint supports, and `E_S ⊕ E_{S'} ⊂ E`; splitting
by a subset or a partition, and subquotient splitting; and the equivalence with
a product of categories. The JH-identity statement task
`ada868b1-e8db-429c-b39a-64385889b0fd` is distinct and supplies no proof
dependency for this construction. No Jordan–Hölder theorem is a premise or a
result of this unit.

## Development check

Worker 985's original development record reports that the module compiled
without errors or warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Its inspection of `simpleSupportSum`
reported a definition with level parameters `u, v` and axioms `propext`,
`Classical.choice` and `Quot.sound` only. A private probe printed the complete
unapplied types of all eight declarations and the definition body
`fun {C} [Category.{v, u} C] [Abelian.{v, u} C] S X [HasCoproduct ...] =>
subobjectSum.{max u v, v, u} fun P => ↑P`, with the coproduct at size
`max u v` and independent universes `u, v`. The same original probe checked the
`HasCoproducts.{max u v}` and `IsSourceCocomplete.{max u v}` specializations, the
agreement with `isLUB_subobjectSum_set`, and the failure of instance search from
`HasCoproducts.{v}` alone. These specializations do not establish a faithful
general source setting: the oversized assumption is degenerate as explained
above. Failure from smaller coproducts alone does not rule out the precise
`Small.{w}` adapter. The file contains no proof holes and no new axioms.

For this correction, Worker 199 read the complete affected pair, current
statement pair, source-axiom definitions and canonical AB6 definition, the
public Appendix A corrections note, and the complete Mathlib EssentiallySmall
and SmallComplete files, in addition to the original passages recorded above.
The source and errata observations remain bounded to those passages.
Development check `a025b336-1e8c-4792-8c8a-0d105e5a9e04` compiled the unchanged
construction without errors or warnings and inspected `simpleSupportSum` as
a definition with independent `u, v` and only the three standard axioms.
Private diagnostic `8260b2ce-5b78-4e8d-92cc-a022aba533a4` also completed with
zero errors or warnings. It printed the complete unapplied type and body
with explicit arguments, universes and proofs, checked the defining equation
by `rfl`, and checked the precise `Small.{w}` adapter both from
`HasCoproducts.{w} C` and from `hG : IsSourceGrothendieck.{w} C`. The probe
is excluded from the submitted pair.
Native byte comparisons against admitted Library
`8c73c345a56c4d23f7e0056f0f55e31cebda2513` found the construction Lean, the
statement Lean/Markdown pair and every imported project pair unchanged.
The original construction and current statements are published; this
correction requires its own independent review and publication. These
development checks do not prove support, maximality or any later source result.
