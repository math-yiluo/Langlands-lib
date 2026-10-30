# Proof of the Renard A.VII semisimplicity equivalence

Module: `Langlands.CategoryTheory.Renard.SemisimplicityEquivalence`.

This module proves the published statement
`Langlands.Renard.SemisimplicityEquivalenceStatement.{r,v,u} C` of
`Langlands.CategoryTheory.Renard.SemisimplicityEquivalenceStatements`. The
theorem is

```lean
theorem semisimplicityEquivalence (C : Type u) [Category.{v} C] [Abelian C] :
    SemisimplicityEquivalenceStatement.{r} C
```

in namespace `Langlands.Renard`. Its complete unapplied type is the published
proposition for an arbitrary `C : Type u` with `[Category.{v} C]` and
`[Abelian C]`. The source-family universe `r`, the Hom universe `v` and the
object universe `u` are independent. Unfolded, the theorem says:

```lean
IsSourceGrothendieck.{r} C → SourceAB6 C →
  ∀ (X : C) [Small.{r} (Subobject X)],
    (IsSemisimpleObject X ↔ IsCompletelyReducible.{r} X) ∧
    (IsSemisimpleObject X ↔ IsSumOfSimpleSubobjects X) ∧
    (IsSumOfSimpleSubobjects X ↔ EverySubobjectHasComplement X)
```

The statement, its conventions and its provenance are explained in the
statement's own Markdown. This module imports the statement by Lean name. It
does not change the statement pair or anything the statement imports. No
hypothesis is added. There is no global `HasCoproducts.{max u v}`, universe
equality, generator, finite-length, Noetherian or module assumption. The only
size assumption is the objectwise `Small.{r} (Subobject X)` already in the
statement. Zero objects and empty families are included. The axioms used are
only `propext`, `Classical.choice` and `Quot.sound`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The lemma of A.VII and its proof are on printed page 265 / PDF page 271. The
hypotheses (AB4*, AB5, Grothendieck, AB6 as local finite type) are on printed
page 263 / PDF page 269.

The source argues with sets of subobjects and arbitrary direct sums. The Lean
proof follows the same ideas but is organized around the subobject lattice.
Where it departs from the printed route, this is said below. The first
conjunct, the comparison of the semisimple-object alias with complete
reducibility at size `r`, is an internal comparison with no source
counterpart.

## How `Small.{r} (Subobject X)` gives the source's set-indexed constructions

The predicate `IsSourceGrothendieck.{r} C` provides `r`-indexed coproducts
(`hG.1 : HasCoproducts.{r} C`) and Renard's AB5 law for nonempty directed
`r`-indexed families of subobjects (`hG.2 : DirectedSubobjectSumsDistribute.{r} C`).
The source's sets of subobjects of `X` are subsets of `Subobject X`. Under
`Small.{r} (Subobject X)`, every such set `s` is `r`-small. The proof reindexes
it by `Shrink.{r} s` and applies the `r`-sized hypotheses:

* `range_shrink_coe`: a small set is the range of its members reindexed by
  `Shrink.{r} s`.
* `exists_isLUB_of_small`: with `r`-indexed coproducts, every set of
  subobjects of `X` has a least upper bound. This uses the published
  `hasIndexedSubobjectSums_of_hasCoproducts` on the reindexed family.
* `subobjectCompleteLatticeOfIsLUB`: the resulting complete lattice on
  `Subobject X`. Its order, `⊔`, `⊓`, `⊥` and `⊤` are the existing ones. Only
  `sSup` and `sInf` are chosen least upper bounds. The proofs install it
  locally with `let`, so lattice lemmas about the existing operations apply
  unchanged.
* `disjoint_of_isLUB_of_directedOn`: AB5 in disjointness form. If `N` is
  disjoint from every member of a nonempty directed small set `D`, then `N` is
  disjoint from the least upper bound of `D`. The proof reindexes `D` by
  `Shrink.{r} D` and applies `hG.2`.

The maximal families found by Zorn's lemma are sets of subobjects of `X`, so
they are `r`-small. Their `Shrink.{r}` reindexing gives the `r`-indexed direct
sum that complete reducibility at size `r` requires. Directed families of
finite subsums of a coproduct indexed by `J : Type r` are indexed by
`Finset J : Type r`, which is also of size `r`.

## Modularity

Mathlib has no `IsModularLattice (Subobject X)` instance, so the module proves
one.

* `epi_biprod_desc_ofLE_sup`: the map `A ⊞ B ⟶ A ⊔ B` given by the two
  inclusions is an epimorphism. This uses the published
  `eq_zero_of_ofLE_sup_comp`.
* `subobject_sup_inf_le_assoc_of_le`: the modular law
  `(A ⊔ B) ⊓ Z ≤ A ⊔ B ⊓ Z` when `A ≤ Z`. Pull this epimorphism back along
  `(A ⊔ B) ⊓ Z ⟶ A ⊔ B`. On the pullback, the inclusion of `(A ⊔ B) ⊓ Z` is a
  sum `a + b` with `a` through `A` and `b` through `B`. Since `A ≤ Z`, `b` also
  factors through `Z`. So the inclusion factors through `A ⊔ B ⊓ Z` after an
  epimorphism. The published `exists_lift_of_comp_cokernel_π` then gives the
  inequality.
* `subobjectIsModularLattice (X : C) : IsModularLattice (Subobject X)` is a
  public instance.

Simple subobjects are exactly the atoms of `Subobject X` (Mathlib's
`subobject_simple_iff_isAtom`).

## (ii) ⇔ (iii)

`isSumOfSimpleSubobjects_iff_everySubobjectHasComplement` rewrites (iii) with
the published `everySubobjectComplementedLattice`:
`EverySubobjectHasComplement X ↔ ComplementedLattice (Subobject X)`. That
comparison is where the canonical `coprod.desc P.arrow Q.arrow` isomorphism
enters. Both directions are then lattice statements.

*(ii) ⇒ (iii)*, `complementedLattice_of_isSumOfSimpleSubobjects`. Fix `P`.
Zorn's lemma (`zorn_le₀`) gives a maximal `Q` disjoint from `P`. A nonempty
chain of such subobjects is directed, and AB5 makes `P` disjoint from its
supremum. The empty chain is bounded by `⊥`. Codisjointness: by (ii) it
suffices that every simple `a` lies below `P ⊔ Q`. If not, `a` is an atom with
`a ≰ P ⊔ Q`, so it is disjoint from `P ⊔ Q`. The modular lattice lemma
`Disjoint.disjoint_sup_right_of_disjoint_sup_left` makes `P` disjoint from
`Q ⊔ a`. Maximality forces `a ≤ Q`, a contradiction. The source instead
enlarges a direct family of simple subobjects next to `E′`. The Lean route
uses the same Zorn and AB5 ingredients in lattice form.

*(iii) ⇒ (ii)*, `isSumOfSimpleSubobjects_of_complementedLattice`. This needs
only source AB6.

* `complementedLattice_subobject`: complementedness passes to the subobjects
  of `(P : C)`, via Mathlib's `Subobject.subobjectOrderIso` onto `Set.Iic P`
  and `complementedLattice_Iic`.
* `exists_simple_subobject_of_complementedLattice`: a nonzero object `Y` with
  complemented subobjects has a simple subobject. This follows the source.
  The published `exists_nonzero_finiteType_subobject` (AB6) gives a nonzero
  finite-type subobject `B`. The published `exists_simple_cokernel_of_finiteType`
  gives a subobject `M` of `B` with simple cokernel. By the published
  `simple_cokernel_ofLE_iff_covBy`, `M` is covered by `⊤`, so it is a
  coatom. A complement `N` of `M` in the
  subobjects of `B` is an atom (`IsCompl.isAtom_iff_isCoatom`), hence simple,
  and its image in `Y` is a simple subobject.
* Given an upper bound `G` of the simple subobjects, take a complement `H` of
  `G`. If `H ≠ ⊥`, then `H` contains a simple subobject. Its image in `X` lies
  below both `G` and `H`, so it is zero, a contradiction. So `G = ⊤`. The source
  phrases this with a maximal direct sum of simple subobjects; the Lean proof
  needs only the complement of an upper bound.

## (i) ⇔ (ii)

*(i) ⇒ (ii)*, `isSumOfSimpleSubobjects_of_isCompletelyReducible`. This holds
at any index universe `w`.

* `mono_cofan_inj`: the injections of a colimit cofan in an abelian category
  are monomorphisms. Each has a retraction, the map that is the identity on
  its summand and zero on the others.
* `eq_top_of_factors_cofan`: a subobject `G` through which every injection
  factors is `⊤`. The universal property gives a section of `G.arrow`, so
  `G.arrow` is a split epimorphism and a monomorphism, hence an isomorphism.
* Each injection `ι i` of a simple summand defines a simple subobject
  `Subobject.mk (ι i)`. An upper bound of all simple subobjects therefore
  contains every injection and is `⊤`.

*(ii) ⇒ (i) at size `r`*, `isCompletelyReducible_of_isSumOfSimpleSubobjects`.

* `factors_finset_sum`: a finite sum of morphisms, each factoring through the
  corresponding member of a family of subobjects, factors through the finite
  supremum `T.sup E`. The proof is by induction on `T`.
* `exists_independent_simple_family`: under (ii) there are `J : Type r` and
  `E : J → Subobject X` with every `E j` simple, `IsLUB (Set.range E) ⊤`, and
  `Disjoint (E j) (F.sup E)` for every finite `F` not containing `j`. Zorn's
  lemma (`zorn_subset_nonempty`, starting from `∅`) gives a maximal set `s` of
  atoms that is `sSupIndep`. For a chain `c`, the union is again independent:
  for `a` in the union, `sSup (⋃₀ c \ {a})` is the least upper bound of the
  directed small set of `sSup (t \ {a})` over the members `t ∋ a` of `c`. AB5
  then makes `a` disjoint from it. For maximal `s`, `sSup s = ⊤`. Otherwise
  some simple `a` is disjoint from `sSup s`, and `insert a s` is still
  independent by the modular-lattice lemma above. Then `J := Shrink.{r} s`,
  and `E` is the injective reindexing. This is the source's maximal direct
  family of simple subobjects.
* `isIso_sigmaDesc_of_independent`: given AB5, such a family, and an actual
  coproduct of the `(E j : C)`, the canonical map
  `φ = Sigma.desc fun j => (E j).arrow : ∐ (E j : C) ⟶ X` is an isomorphism.
  - *Epi*: if `φ ≫ g = 0`, then every `E j` lies in `kernelSubobject g`. Since
    the `E j` sum to `⊤`, this kernel is `⊤`, so `g = 0`.
  - *Mono*: let `N = kernelSubobject φ`. For a finite `F`, let `Y F` be the
    supremum of the summand subobjects `Subobject.mk (Sigma.ι _ j)`, `j ∈ F`,
    and let `e F = ∑ j ∈ F, p j ≫ Sigma.ι _ j`, where `p j` is the projection
    onto summand `j`. Then `Y F` lies in the kernel of `e F - 𝟙`. For `m` the
    inclusion of `N ⊓ Y F`, this gives `m = ∑ (m ≫ p k) ≫ Sigma.ι _ k` and
    `∑ (m ≫ p k) ≫ (E k).arrow = m ≫ φ = 0`. For `j ∈ F`, the term
    `(m ≫ p j) ≫ (E j).arrow` factors through both `E j` and
    `(F.erase j).sup E`, so it is zero. Cancelling the mono `(E j).arrow`
    gives `m ≫ p j = 0`. Hence `m = 0` and `N` is disjoint from every `Y F`.
    The `Y F`, indexed by `Finset J : Type r`, form a nonempty directed family
    with least upper bound `⊤`, by `eq_top_of_factors_cofan`. AB5 makes `N`
    disjoint from `⊤`, so `N = ⊥` and `φ` is mono.
  - Mono and epi give an isomorphism in an abelian category.
* Finally `hG.1` supplies the coproduct of the `r`-indexed family. The
  published `IsCompletelyReducible.iff_exists_iso_sigma`, with the inverse of
  `φ`, gives `IsCompletelyReducible.{r} X`.

The source deduces (i) from (iii). The Lean proof goes from (ii) to (i) and
proves (ii) ⇔ (iii) separately, so all three conditions are connected.

## Size comparison (first conjunct)

This section is adapted from Worker 6's checked feasibility probe, with
renamed declarations. It needs neither source Grothendieck nor AB6.

* `small_of_simple_coproduct_index`: if `S : I → C` is a family of simple
  objects with a coproduct whose subobject type is `r`-small, then `I` is
  `r`-small. The map `i ↦ Subobject.mk (Sigma.ι S i)` is injective. If two
  distinct summands gave the same subobject, the projection onto the first
  would be both the identity and zero on it, contradicting simplicity.
* `isCompletelyReducible_resize`: under `Small.{r} (Subobject X)`, complete
  reducibility at any index universe `w` implies it at `r`. Transport
  smallness along `X ≅ ∐ S` with `Subobject.mapIsoToOrderIso`. Reindex the
  colimit cofan along `equivShrink I` with `IsColimit.whiskerEquivalence`,
  `IsColimit.precomposeHomEquiv` and `IsColimit.ofIsoColimit`, the last with
  `Cocone.ext (Iso.refl _)`.
* `isSemisimpleObject_iff_isCompletelyReducible`: apply the resize lemma in
  both directions between `max u v` and `r`. The direction into `max u v` uses
  the automatic `Small.{max u v} (Subobject X)`.

## Assembly

`semisimplicityEquivalence` introduces `hG`, `hAB6`, `X` and the smallness
instance. The first conjunct is `isSemisimpleObject_iff_isCompletelyReducible`.
The second combines `isSumOfSimpleSubobjects_of_isCompletelyReducible`, at
`w = max u v`, with `isCompletelyReducible_of_isSumOfSimpleSubobjects`
followed by the first conjunct. The third is
`isSumOfSimpleSubobjects_iff_everySubobjectHasComplement`.

## Authors

Worker 1069 wrote the lattice, (i) ⇔ (ii), (ii) ⇔ (iii) and assembly parts.
Worker 6 wrote the size-comparison probe reused in the first conjunct.
