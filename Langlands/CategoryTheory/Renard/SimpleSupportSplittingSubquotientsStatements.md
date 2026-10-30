# Renard A.IX: splitting passes to every actual subquotient

Authors: Worker 6 (complete two-file draft) and Worker 713 (adoption,
independent source reading, recompilation against the public Library and
declaration probes). This pair defines one proposition target,
`Langlands.Renard.SimpleSupportPartitionSubquotientStatement`, in module
`Langlands.CategoryTheory.Renard.SimpleSupportSplittingSubquotientsStatements`.
It proves no splitting theorem.

## Governing source and reading

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French edition dated 9 July 2026, A.IX, the unnumbered lemma
immediately after the boxed splitting definition, printed268/PDF274.
Registered original: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
Both authors read PDF274–275 in full and inspected a rendering of PDF274.
PDF275 starts A.X, which is outside this unit. PDF269–270 (printed263–264)
was read in full for AB4\*, AB5, the source Grothendieck convention, the
AB6 footnote, `Irr` and the simple-subquotient identities.

The boxed definition reads:

> Définition. On dit que la partie `S ⊂ Irr(M)` scinde un objet `E` dans
> `M`, si `E = E_S ⊕ E_S̄`, où `S̄ = Irr(M) \ S`. […] Plus généralement,
> supposons que l'on ait une décomposition en union disjointe :
> `Irr(M) = ⨆_α S_α`. On dit que cette décomposition `{S_α}` scinde un
> objet `E` dans `M`, si `E = ⨁_α E_{S_α}` […].

The lemma reads:

> Lemme. Supposons que `Irr(M) = ⨆_α S_α` scinde un objet `E` dans `M`.
> Alors tout sous-quotient de `E` est aussi scindé selon cette
> décomposition.

Here `E_S` is "la somme de tous les sous-objets de `E` qui sont dans
`M_S`", and `M_S` consists of the objects all of whose irreducible
subquotients lie in `S`. The ambient `M` is "une catégorie de Grothendieck
(AB4\* et AB5) vérifiant aussi AB6".

The source proof first treats a subobject `L` of `E = ⨁_α E_α`, putting
`C = L / ⨁_α (E_α ∩ L)`. For each `α`, the simple classes of `C` lie in
`JH(E/E_α) ⊂ ⋃_{β≠α} JH(E_β) ⊂ Irr(M) \ S_α`. Since the blocks exhaust
`Irr(M)`, `JH(C)` is empty, and zero detection makes `C` zero. This
paragraph records the source argument; no implementation of that proof
is claimed here.

The public `notes/renard/appendix-a-corrections.md` was read in full;
its three discrepancies concern A.III.1, A.IV.1–2 and A.VI.1, not this
passage. The registered supplementary `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. Its entry "p. 310, l. 10 et 11 : remplacer M par E
et MS par ES" is a letter correction that the governing 2026 page already
incorporates. Those two pages contain no correction of the subquotient
splitting lemma. This is a bounded observation about a different edition,
not an exhaustive errata claim.

## Complete proposition

With independent universes `r w v u`, the complete body is:

```lean
def SimpleSupportPartitionSubquotientStatement
    (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  IsSourceGrothendieck.{r} C → SourceAB6 C →
    ∀ (I : Type w) [Small.{r} I] (S : I → Set (ObjectClass C)),
      ∀ (X : C) [∀ i : I, Small.{r} (simpleSupportSubobjects (S i) X)],
        SimpleSupportPartitionSplits S X →
          ∀ (N Y : C) (j : N ⟶ X) (p : N ⟶ Y) [Mono j] [Epi p]
            [∀ i : I, Small.{r} (simpleSupportSubobjects (S i) Y)],
            SimpleSupportPartitionSplits S Y
```

`C` is the actual abelian category. The source Grothendieck hypothesis is
the existing `IsSourceGrothendieck.{r} C`: `r`-indexed coproducts and the
source AB5 distributivity of intersection over nonempty directed sums
of subobjects. It includes no generator or separator. The separate
`SourceAB6 C` is the canonical local finite-type condition from A.VI.3.
Neither source condition is replaced by Mathlib's differently named
Grothendieck or AB6 conventions.

`ObjectClass C` consists of classes of actual objects under actual
isomorphism, and `simpleClasses C` is the source `Irr(M)`. `S` is a family
of sets of these classes, indexed by `I`, the source's `α`. The premise
`SimpleSupportPartitionSplits S X` includes the exact partition condition
`IsSimpleSupportPartition S`: pairwise disjointness and union equal to
`simpleClasses C`, the source `Irr(M) = ⨆_α S_α`. It also asserts
existence of every inner supported-subobject coproduct, existence of the
outer coproduct of the resulting sums `simpleSupportSum (S i) X` (the
source `E_{S_α}`), and invertibility of the actual canonical map to `X`.
A separate partition premise would repeat this existing conjunct.

The two actual morphisms present an arbitrary subquotient:
`j : N ⟶ X` is monic, and `p : N ⟶ Y` is epic. There is no extra
restriction on `N` or `Y`. An actual categorical quotient of an actual
subobject has this form. In particular, for nested subobjects
`A ≤ B` of `X`, take `N = (B : C)`, `j = B.arrow` and
`p = cokernel.π (Subobject.ofLE A B h)`. Allowing all such monic and epic
maps also covers presentations through arbitrary isomorphic
representatives, without fixing a concrete module category or imposing
simplicity on the subquotient. Taking `p` to be the identity includes
subobjects; taking `j` to be the identity includes quotients.

The conclusion is the same actual splitting predicate at `Y`, with the
same partition `S`. It asserts existence of the inner and outer
coproducts at `Y` and invertibility of the canonical map
`Sigma.desc fun i => (simpleSupportSum (S i) Y).arrow` from the coproduct
of the sums `simpleSupportSum (S i) Y` to `Y`, whose legs are the actual
subobject inclusions. An abstract isomorphism to unrelated summands does
not meet this conclusion.

## Sizes and source correspondence

The universe `r` bounds source families, `w` is the partition's index
universe, `v` is the Hom universe, and `u` is the object universe. The
condition `[Small.{r} I]` says that the partition can be reindexed at the
source size; it identifies none of these universes. No finiteness or
nonemptiness is imposed on `I`, and blocks may be empty.

The full supported-subobject type at an endpoint lies in `Type (max u v)`.
For each block, its `r`-smallness is stated separately at `X` and `Y`.
These are precisely the families defining the actual sums at those
endpoints. They do not assert support of the sums, any closure property,
or any splitting result. They do not assume smallness of every family
of subobjects of every object. No smallness or coproduct instance is
required for a family at `N`.

From `hG.1 : HasCoproducts.{r} C`, Mathlib's
`hasCoproductsOfShape_of_small` supplies the particular inner coproducts
and the outer partition coproduct from these hypotheses.

### Why coproduct existence at `X` does not replace smallness at `X`

The splitting premise at `X` already asserts that the inner coproducts
exist. Existence of the coproduct of one particular family says nothing
about the size of its index type. For instance, a family of zero objects
indexed by any type has a coproduct, namely a zero object.

The same happens for the actual supported family. Informally, take `r`
to be universe `0`, a field `K : Type`, and `C = ModuleCat.{1} K`, whose
Homs lie in `Type 1`. This category has all `Type 1`-indexed coproducts,
hence the source `r`-coproducts, and modules satisfy source AB5 and AB6.
Let `X` be the free `K`-module on the type `Type` (a member of `Type 1`),
and take the one-block partition `I = Unit`, `S () = simpleClasses C`.
Every subobject of `X` is supported on all simple classes, so the full
supported family is all of `Subobject X`, its sum is `⊤`, and its
coproduct exists because module categories are well-powered at size `1`.
Hence `X` is split. But the lines spanned by the basis vectors give an
injection of `Type` into `Subobject X`, so this family is not
`Small.{0}`.

The source proof uses the support of each full sum: that
`simpleSupportSum (S i) X` has no simple subquotient outside `S i`
(`JH(E_β) ⊂ S_β`). The source calls this clear ("il est clair que
`E_S ∈ M_S`"); it follows from the A.VI.3 identity
`JH(∑ M_i) = ⋃ JH(M_i)`, whose proof applies AB5 to the directed system
of finite subsums. The public
`DirectedSubobjectSumsDistribute.{r}` only covers `r`-indexed families.
The smallness hypothesis at `X` makes the full supported family and its
finite subfamilies `r`-indexable, so the source AB5 law can apply.
Without it the premises could describe a split `X` whose supported
families are too large for the source AB5 hypothesis.

The smallness at `Y` is the corresponding presupposition for the
conclusion: it makes the inner coproducts at `Y` available from
`HasCoproducts.{r}` and lets AB5 apply to those families. This target
does not claim or deny that the hypotheses at `Y` follow from those at
`X`; it simply assumes them.

### Oversized global coproducts and source sets

The statement assumes no `HasCoproducts.{max u v} C`. That global
oversized assumption would force all Hom types to be subsingletons, as
explained in the public `SimpleSupportSum` Markdown. Actual large
categories with small Homs, such as module categories, are informally
meant to be covered with a source-sized partition and well-poweredness
at the source size. The source-size presuppositions stand in for the
book's informal convention that families are indexed by sets. There is
no generator, finite-length, Noetherian or concrete-category restriction.

## Scope and independent proof gate

This statement unit imports the support-splitting definitions and the
source hypotheses by Lean name. It assumes no support theorem, arbitrary
sum identity, Hom orthogonality, closure of a full subcategory, or
subquotient-splitting conclusion as a premise. Those results may be
separately proved dependencies of the eventual proof. The import
`Mathlib.CategoryTheory.Limits.EssentiallySmall` supplies
`hasCoproductsOfShape_of_small` for that proof; the statement itself only
uses `Small` and the public Renard predicates.

The subobject intersection direct-sum identity displayed in the source
proof is not a second conclusion of this target. A proof may establish
it internally or take another verified route, while still proving the
complete proposition above. The subset and category splitting predicates,
categorical product equivalence, supported functor's further properties
and the other whole-book obligations remain separate.

## Verification

Worker 713 recompiled the unchanged Lean file (SHA256
`e57d7f74a4750c8a275b2a94980e64a097b1f72e927f4e5bad2df0cf225f999b`)
against the public imports at Library commit
`3987c3d7445531c2c7f784464a3fd47061ba0865`. Approved-service check
`bb2244e2-f6dc-4b46-878e-39168ec779c3` in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` had zero errors and warnings,
`statement_returns_prop: true`, level parameters `r w v u`, and only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

A private probe, diagnostic `d59816da-b27d-40dd-b28d-4bf05e9cae71`, also
had zero errors and warnings. It printed the complete unapplied type and
body shown above, with every instance binder inside the body. It
instantiated the universes as `{0,1,2,3}` and `{0,4,0,1}`. It derived the
exact inner and outer coproducts at `X` from `hG.1` and the stated
smallness. It applied the target to `B / A` with `j = B.arrow` and
`p = cokernel.π (Subobject.ofLE A B h)`, and with identity maps for
subobjects and quotients. Finally, it checked by `Iff.rfl` that the
conclusion is the partition condition together with existence of the
coproducts and invertibility of
`Sigma.desc fun i => (simpleSupportSum (S i) Y).arrow`.

Earlier, Worker 6's development check
`7c6793b2-ec75-44c9-8cc2-47acd1165af4` and diagnostic
`dda06672-c0d8-41e6-9e6e-7bd590f90c79` were clean against a byte-identical
copy of the then-pending splitting dependency.

Compilation supplies no semantic acceptance. This statement needs
independent review and publication, followed by a separate exact-target
proof task.
