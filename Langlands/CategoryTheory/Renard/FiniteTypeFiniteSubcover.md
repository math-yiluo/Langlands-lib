# Renard A.I.3: finite type iff finite subcover, proof

This module proves the published proposition `Langlands.Renard.FiniteTypeFiniteSubcoverStatement C` from `Langlands.CategoryTheory.Renard.FiniteTypeFiniteSubcoverStatements`. The theorem is

```lean
theorem Langlands.Renard.finiteTypeFiniteSubcover (C : Type u) [Category.{v} C] :
    FiniteTypeFiniteSubcoverStatement C
```

Thus, for every category `C` with independent object and Hom universes `u` and `v` and every object `X : C`,

```lean
Langlands.Renard.IsFiniteTypeObject X ↔
  Langlands.Renard.HasFiniteSubcoverProperty X
```

The target pair and the predicate pair `Langlands.CategoryTheory.RenardFiniteType` are imported unchanged by their Lean names. The only other imports are Mathlib's `Order.CompleteLattice.Basic` and `Order.Zorn`.

## Source and route

The governing original is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, A.I.3, printed pages 248–249 / PDF254–255. Registered source: `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The source gives no proof. It cites [37], Pareigis, *Categories and Functors* (1970), 4.10 Theorem 1. That book was not read for this unit, and the proof here does not rely on it. The implemented proof is an independent order-theoretic argument. It uses Zorn's lemma for the chain-to-cover direction and a finite upper bound inside a chain for the converse. The source conventions repaired in the statement Markdown are kept: chains are nonempty, properness means `≠ ⊤`, the cover equation reads `IsLUB S ⊤`, and finite subcovers may be empty.

## Local complete lattice

Both predicates contain `HasSubobjectUnions X`, which says that every `S : Set (Subobject X)` has a least upper bound. The private definition `subobjectCompleteLattice X hX` turns this hypothesis into a `CompleteLattice (Subobject X)`. It defines `sSup S` as the least upper bound chosen by `(hX S).choose`. Mathlib's `completeLatticeOfSup` then builds the lattice from the existing `PartialOrder (Subobject X)` and the fact that each choice is a least upper bound. The definition sets the lattice top to Mathlib's existing top subobject `⊤`.

So the order is the actual factorization order on `Subobject X`, and `⊤` is the actual top subobject. Every `IsLUB` and `⊤` in the target means the same thing under this structure. Bottom, binary join `⊔` and `sSup` come from the chosen least upper bounds; bottom is the chosen least upper bound of the empty set. The structure exists only inside the proof, as a local `let` after the union-existence conjunct has been extracted. No instance is registered globally. The theorem's type contains no complete-lattice, category-wide union, abelian, zero-object, well-poweredness, smallness, Grothendieck, module or Noetherian hypothesis. Each direction returns the union-existence conjunct it received.

The three order lemmas below are stated for an arbitrary `CompleteLattice α` and are applied with `α := Subobject X`.

## Finite type implies finite subcover

The private lemma `finiteSubcover_of_proper_chains` assumes the nonempty proper-chain condition and a set `S` with `IsLUB S ⊤`. The set `S` is arbitrary, with no restriction on its cardinality. Suppose no `F : Finset α` with `↑F ⊆ S` has least upper bound `⊤`. Let

`U = {x | ∀ F : Finset α, ↑F ⊆ S → x ⊔ sSup ↑F ≠ ⊤}`.

1. `⊥ ∈ U`. If `⊥ ⊔ sSup F = ⊤`, then `sSup F = ⊤`, so `F` would be a finite subcover. The case `F = ∅` is included.
2. Every chain in `U` has an upper bound in `U`. For the empty chain, `⊥` is one. For a nonempty chain `c`, take `sSup c`. Fix a finite `F ⊆ S`. The set `D = {x ⊔ sSup F | x ∈ c}` is nonempty. It is a chain because `x ↦ x ⊔ sSup F` is monotone. Each of its elements differs from `⊤` because `c ⊆ U`. The least upper bound of `D` is `sSup c ⊔ sSup F`, proved directly. That join is an upper bound of `D`. Conversely, an upper bound `q` of `D` lies above every `b ∈ c`, hence above `sSup c`. It also lies above `sSup F`, using a single element of the nonempty chain `c`. No distributivity is used. If `sSup c ⊔ sSup F = ⊤`, then `D` would be a nonempty chain of proper elements with least upper bound `⊤`, contrary to the hypothesis. Hence `sSup c ∈ U`.
3. Mathlib's `zorn_le₀` then gives an element `m` that is maximal in `U`.
4. Every `a ∈ S` satisfies `a ≤ m`. Indeed, `m ⊔ a ∈ U`: for finite `F ⊆ S`, the set `insert a F` is also a finite subset of `S`, and `(m ⊔ a) ⊔ sSup F = m ⊔ sSup (insert a F) ≠ ⊤`. Maximality of `m` with `m ≤ m ⊔ a` gives `m ⊔ a ≤ m`, so `a ≤ m`.
5. Since `IsLUB S ⊤`, the upper bound `m` satisfies `⊤ ≤ m`, so `m = ⊤`. Taking `F = ∅` in the definition of `U` gives `m ⊔ ⊥ ≠ ⊤`, which is a contradiction.

Hence a finite subcover exists. In step 1, `isLUB_iff_sSup_eq` turns `sSup ↑F = ⊤` into the `IsLUB ↑F ⊤` required by the predicate. The argument works directly with arbitrary covers. It neither assumes that a cover is directed nor replaces it by a cofinal chain. It does not use Mathlib's compact-element or directed-compactness API.

## Finite subcover implies finite type

The private lemma `finite_upperBound_in_chain` shows, by induction on finsets, that every finite subset of a nonempty chain `S` has an upper bound in `S`. For the empty finset, any member of `S` works. For `insert a F`, compare `a` with the bound `b` already found for `F` and keep whichever is larger.

The private lemma `proper_chains_of_finiteSubcover` derives the chain condition. Let `S` be a nonempty chain of elements different from `⊤`, and suppose `IsLUB S ⊤`. The finite-subcover hypothesis gives a finset `F ⊆ S` with `IsLUB ↑F ⊤`. Let `a ∈ S` be an upper bound of `F`. The least-upper-bound property gives `⊤ ≤ a`, so `a = ⊤`. This contradicts properness. If `F` is empty, `a` is any member of the nonempty chain and the same contradiction follows.

## Degenerate cases

The proof needs no case split for objects whose subobject order has one element, such as zero objects. There `⊥ = ⊤`, so the empty finite subset is already a finite subcover. Correspondingly, the forward argument reaches its contradiction already in step 1, with `F = ∅`. In the converse, no nonempty chain of proper subobjects exists.

## Main theorem

`finiteTypeFiniteSubcover C` fixes `X : C`. In each direction, with hypothesis `hX`, it builds `subobjectCompleteLattice X hX.1` by a local `let`. It then returns `⟨hX.1, ...⟩`, obtaining the second conjunct by applying the corresponding order lemma at `α := Subobject X` to `hX.2`.

## Provenance and checks

Worker 6 authored the Lean proof and an earlier Markdown draft as shared draft revision 1 for proof task `2bafa4e4-92e4-47ad-9977-fc5895409d78`. Worker 840 checked the argument and rewrote this Markdown. The Lean file is unchanged from that draft.

Development check `1cca6568-a54d-4906-a209-58867c06290f` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` compiled the module with no errors or warnings. It inspected `Langlands.Renard.finiteTypeFiniteSubcover` as a theorem with level parameters `u, v`. Its only axioms are `propext`, `Classical.choice` and `Quot.sound`. Check `14994ff9-f7e4-4121-8616-6fb6282279bd` printed the complete unapplied type `∀ (C : Type u_1) [inst : Category.{u_2, u_1} C], FiniteTypeFiniteSubcoverStatement.{u_1, u_2} C`. That check also elaborated `@finiteTypeFiniteSubcover.{u, v}` against `∀ (C : Type u) [Category.{v} C], FiniteTypeFiniteSubcoverStatement C`. Development checks do not establish exact-target validation, independent acceptance or publication.

This unit proves the general categorical A.I.3 characterization only. The actual `ModuleCat` comparisons, Noetherian characterizations, compact-element comparisons and later finiteness statements remain separate obligations.
