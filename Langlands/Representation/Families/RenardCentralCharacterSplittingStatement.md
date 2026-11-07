# Renard VI.8.5 Lemma: filtrations with distinct central characters split

This module contains one **statement**, the closed `Prop`-valued definition
`Langlands.Renard.AlgebraicFamily.CentralCharacterSplittingStatement`, with
universe parameters `uk, uG, uV`. It proves nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**:

- VI.8.5, "Irréductibilité générique des induites": the Lemma and its proof
  inside the proof of the Theorem, printed p. 194 / PDF p. 200.
- Central characters: III.1.10, "Caractère central", printed p. 63 / PDF p. 69.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 read PDF pages 69 and 198–201.

The Lemma reads: "Soit `(π, V)` une représentation de `G` admettant une
filtration `{0} = V_0 ⊂ V_1 ⊂ ⋯ ⊂ V_n = V` dont les quotients successifs
`V'_i = V_i / V_{i-1}` ont des caractères centraux distincts. Alors
`V ≃ ⊕_{i=1}^n V'_i`." Its proof: the result is clear for the restrictions to
`Z(G)`, and since `G` and `Z(G)` commute, the action of `G` preserves the
decomposition into distinct characters of `Z(G)`.

III.1.10 defines the terms. For a subgroup `Z` of the centre `Z(G)` of the
group `G`, a smooth representation `(π, V)` "admet le caractère central `χ`" if
`π(z) = χ(z) Id_V` for all `z`. The source writes `z ∈ Z` in this formula and
`χ` a character of `Z(G)`; the Lemma uses the case `Z = Z(G)`.

## Lean model

- Representations are objects `A : Rep.{uV} k G` of Mathlib's category of
  `k`-linear representations of a group `G`, over a field `k`.
- The filtration is a published
  [`Langlands.ObjectRepFiltration A n`](../Filtration/ObjectDefinitions.md): a
  monotone chain of subrepresentations indexed by `Fin (n + 1)`, equal to `⊥`
  at `0` and to `⊤` at `Fin.last n`. Its graded quotient
  `s.gradedRepresentation i`, for `i : Fin n`, is the quotient of step
  `i.succ` by step `i.castSucc`. This is the source's `V'_{i+1}`.
- `Z : Subgroup G` with `Z ≤ Subgroup.center G` is a central subgroup, and
  `χ : Fin n → Z →* kˣ` gives one character for each graded quotient.
- The direct sum is the coproduct `∐ fun i => s.gradedRepresentation i` in
  `Rep k G`. `Rep k G` is abelian in Mathlib, so finite coproducts are direct
  sums. The isomorphism `A ≅ ∐ …` is an isomorphism in `Rep k G`, that is, a
  `G`-equivariant `k`-linear bijection.

## Declaration

`CentralCharacterSplittingStatement.{uk, uG, uV}`: for every field `k : Type uk`,
every group `G : Type uG`, every central subgroup `Z`, every representation
`A : Rep.{uV} k G`, every filtration `s : ObjectRepFiltration A n` and every
injective family `χ : Fin n → Z →* kˣ`: if every `z ∈ Z` acts on
`s.gradedRepresentation i` as the scalar `χ i z`, then `A` is isomorphic to
`∐ fun i => s.gradedRepresentation i`.

## Correspondence notes

1. Group. The source states the Lemma for the group `G` of Chapter VI, the
   rational points of a connected reductive group, and for its representations,
   which in Chapter VI are smooth and complex. Its proof uses only that `Z(G)`
   is central. The statement therefore takes any group `G`, any field `k` and
   any representation, without topology or smoothness. This makes it formally
   more general. The reading is Worker 709's.
2. Centre. The statement takes any subgroup `Z` contained in
   `Subgroup.center G`. With `Z = Subgroup.center G` it is the source's Lemma
   for the centre of the group `G`, as in III.1.10. With `Z` the rational
   points of the centre of a reductive group, it covers that reading of
   `Z(G)` as well, so the statement does not depend on comparing the two
   centres.
3. Central characters as data. "Ont des caractères centraux distincts" is
   read as: each `V'_i` admits a central character `χ_i` and the `χ_i` are
   pairwise distinct. In Lean the `χ i` are given, together with the
   hypothesis that `z` acts on the `i`-th quotient as `χ i z`. Pairwise
   distinctness is `Function.Injective χ`. A zero quotient admits every
   character; the hypothesis then only requires that some distinct choice
   be given.
4. Characters. A character of `Z` is a group homomorphism `Z →* kˣ`. No
   continuity is required, which only enlarges the set of hypotheses. For a
   smooth representation, the central character of a nonzero quotient is
   locally constant.
5. Indexing. The source indexes the quotients by `1, …, n`, and Lean by
   `Fin n`, so `s.gradedRepresentation i` is the source's `V'_{i+1}`.
6. Direct sum. "`V ≃ ⊕ V'_i`" is read as an isomorphism of representations
   onto the external direct sum, the coproduct in `Rep k G`. The source does
   not say whether the isomorphism should be compatible with the filtration,
   and the statement does not ask for it.

## Relation to published work

The VI.8 progress note
[algebraic-families-progress](../../../notes/renard/algebraic-families-progress.md)
lists the Lemma as row (L5). At Library `7e84f6ad` it is not stated in the
source's form. Its reading note 4 compares it with the published
[CentralEigenspaceSplitting](../Filtration/CentralEigenspaceSplitting.md):
`Langlands.CentralEigenspaceSplitting.eigenSubrep`, `eigenEquivGraded` and
`iSup_eigenSubrep` take one central element `z` that acts on graded quotient
`i` by `c i`, with `c` injective. They show that the `c i`-eigen
subrepresentations are isomorphic to the graded quotients and span `A`. When
the quotients admit central characters, that hypothesis is strictly stronger
than the source's. For example, the four characters of `(ℤ/2)^2` with values
`±1` are pairwise distinct, but a single element takes at most two values on
them. A proof of this statement may adapt that module's polynomial and
Lagrange-basis lemmas to finitely many central elements.

This module asserts nothing about them. A proof of the statement is a
separate obligation, which must prove the declaration unchanged.

## Environment

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. The only project import is
`Langlands.Representation.Filtration.ObjectDefinitions`. No construction or
axiom is introduced.
