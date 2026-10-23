# Naturality and multiplication of diagonal Harris point families

This module proves compatibility under coefficient change and test-scheme
pullback for the constructions in `DiagonalPointConjugacy`. It also packages
the diagonal families as group homomorphisms. The provenance is internal:
the proofs use the explicit diagonal and permutation matrices, the group
equivalence `complexGroupPointsEquiv`, and its established naturality.
No additional literature convention is introduced.

## Coefficient change for matrix units

Let `S,R` be commutative rings, `f : S →+* R`, and let `p : Fin n → Prop`
have decidable membership. Write `Dₚ(u)` for `inverseDiagonalUnit S p u`.
`inverseDiagonalUnit_map` proves

\[
\operatorname{GL}_n(f)(D_p(u))=D_p(f^\times(u)).
\]

Here `GLₙ(f)` is `Units.map` of the entrywise matrix ring homomorphism.
The proof applies extensionality to units and matrices, separates diagonal
from off-diagonal entries, and then separates membership in `p`.
Ring homomorphisms preserve the zero and one entries and the inverse scalar
unit entries.

For a permutation `σ`, `weightPermutationUnit_map` proves that applying the
same coefficient map to `weightPermutationUnit S σ` gives
`weightPermutationUnit R σ`. Its entries are zero or one, and the proof
checks whether `σ i = j`. For decidable supports `p,q` and an equality `h`
of their cardinalities, `diagonalWeightConjugator_map` specializes this
identity to `weightSupportPermutation p q h`. The permutation depends on
the supports and their fixed decidability instances, and is independent of
the coefficient ring.

`inverseDiagonalHom S p` constructs the homomorphism

\[
S^\times\longrightarrow\operatorname{GL}_n(S),\qquad u\longmapsto D_p(u).
\]

The identity law is the diagonal-one formula. The multiplication law uses
the product formula for diagonal matrices, coordinate by coordinate,
and commutativity of `S`. These constructions include the zero ring and
the case `n=0`.

## Pullback of actual Harris points

Retain the number fields, algebra towers, unitary data `D`, and Harris
signature charts `C` of `DiagonalPointConjugacy`. Put
`G = D.complexRationalGroupScheme`. For any complex test scheme `T`,
write `S_T = AlgebraInvolution.complexTestAlgebra T`, its actual complex
algebra of global sections.

For a map `a : T' ⟶ T` over `Spec ℂ`, let `a*` be its induced map on
global sections. For arbitrary supports `pτ` the theorem
`diagonalWeightPointFamily_naturality` proves

\[
a^*(a_{p,T}(u))=a_{p,T'}((a^*)^\times(u)).
\]

The left side is composition of actual scheme morphisms. The proof applies
the injective split point equivalence, uses its naturality, and compares
the matrix and multiplier components. The matrix components follow from
`inverseDiagonalUnit_map`; the multiplier identity is preservation of
inversion under the induced unit homomorphism.

For supports `p,q` with equal cardinalities at every real embedding,
`diagonalWeightPointConjugator_naturality` proves

\[
a^*(g_{p,q,T})=g_{p,q,T'}.
\]

Again the proof uses the split point equivalence. The matrix components
are `diagonalWeightConjugator_map`, and the multiplier is one on both
sides. Thus the chosen conjugating points form a natural family on all
test schemes.

Finally, `diagonalWeightPointHom C T p` packages the actual point family
as a homomorphism

\[
S_T^\times\longrightarrow G(T),\qquad u\longmapsto a_{p,T}(u).
\]

Its identity and multiplication laws are proved after applying the split
group equivalence: each matrix component is `inverseDiagonalHom` and
the multiplier is `u⁻¹`. This requires no nontriviality assumption on global
sections and applies to empty test schemes as well.

The module supplies natural point homomorphisms and natural conjugators.
Constructing the resulting group-scheme cocharacters, comparing charts,
and identifying the Galois action and reflex stabilizer remain subsequent
steps.
