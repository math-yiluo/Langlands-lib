# Conjugacy classification of inverse/trivial diagonal families

This module constructs an explicit simultaneous conjugator for two diagonal
families with equally many inverse-weight coordinates, and proves that this
cardinality is a complete invariant over any nontrivial complex algebra.
It is an internal finite linear-algebra derivation from Mathlib's equivalences
of finite types and permutation matrices, together with the inverse-weight
submodules and their conjugacy equivalences in `ComplexWeightSpaces` and
`ComplexWeightConjugacy`. It introduces no additional literature convention.

## The support permutation

Fix a natural number `n`, predicates `p,q : Fin n → Prop` with decidable
membership, and an equality

\[
\#\{j:p(j)\}=\#\{j:q(j)\}.
\]

`weightSupportPermutation p q h` is a permutation `σ` of `Fin n` taking the
`q` support to the `p` support. The implementation first uses
`Fintype.equivOfCardEq` to construct an equivalence between the two support
subtypes, then extends it to the whole finite type with `Equiv.extendSubtype`.
The latter also supplies an equivalence on their complements.
`weightSupportPermutation_spec` proves

\[
p(\sigma(j))\quad\Longleftrightarrow\quad q(j).
\]

Its proof separates membership and nonmembership in `q` and applies the two
membership properties of `extendSubtype`. The construction is noncomputable
because it chooses finite equivalences; it is an actual permutation with
proved inverse identities, not a hypothesis asserting its existence.

## A matrix unit conjugating every member of the family

Let `S` be any commutative ring. For a permutation `σ`,
`weightPermutationUnit S σ` is a unit of `Matrix (Fin n) (Fin n) S` whose value
is `σ.permMatrix S` and whose inverse is `(σ⁻¹).permMatrix S`. Mathlib's
permutation-matrix convention is

\[
P_\sigma v=v\circ\sigma.
\]

The unit identities follow from the permutation-matrix multiplication formula.
`weightPermutationUnit_conj_diagonal` proves

\[
P_\sigma\operatorname{diag}(d)P_\sigma^{-1}
  =\operatorname{diag}(d\circ\sigma).
\]

The implementation rewrites left and right multiplication as row and column
reindexing, then applies the diagonal-submatrix formula for an equivalence.

Write

\[
D_p(u)=\operatorname{diag}
 \bigl(j\longmapsto\text{if }p(j)\text{ then }u^{-1}\text{ else }1\bigr),
 \qquad u\in S^\times.
\]

`diagonalWeightConjugator p q S h` is the matrix unit associated to the support
permutation above. `diagonalWeightConjugator_spec` proves

\[
gD_p(u)g^{-1}=D_q(u)\qquad\text{for every }u\in S^\times.
\]

This is one conjugator for the entire family, independent of `u`.
The proof combines the diagonal conjugation identity with the predicate
matching lemma. All these constructions and identities permit the zero ring
and `n=0`; they use no complex algebra structure.

## Exact classification over a nontrivial complex algebra

`DiagonalWeightConjugate p q S` is a proposition definition asserting that
there is one matrix unit `g` with the preceding identity for all scalar units.
`diagonalWeightConjugate_of_card_eq` supplies this proposition over every
commutative ring from equality of support cardinalities, using the explicit
conjugator.

Assuming additionally `[Algebra ℂ S]` and `[Nontrivial S]`,
`diagonalWeightConjugate_iff_card_eq` proves the equivalence

\[
\bigl(\exists g\in\operatorname{GL}_n(S),\ \forall u\in S^\times,
         \ gD_p(u)g^{-1}=D_q(u)\bigr)
 \quad\Longleftrightarrow\quad
 \#\{j:p(j)\}=\#\{j:q(j)\}.
\]

For necessity, the proof applies `finrank_inverseWeightSpace_conj` to `D_p`,
rewrites the conjugated family using the assumed identity, and computes both
ranks with `finrank_inverseWeightSpace_diagonal`. The complex algebra and
nontriviality assumptions enter exactly through these numerical rank formulas.
Sufficiency is the construction over general commutative rings above.
The invariant counts inverse-weight coordinates even though arbitrary conjugating
matrix units, rather than only permutation matrices, are allowed.

This classifies these specified diagonal families over a fixed coefficient
ring. It does not classify arbitrary families, compare signature charts,
construct a Galois action on scheme cocharacters, or identify their reflex
stabilizer. Applying the construction through the Harris group point
splitting and establishing the scheme and Galois compatibilities are further
steps.
