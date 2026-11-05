# Proof of the characteristic-zero vector-kernel splitting statement

`Langlands.GroupScheme.characteristicZeroReductiveVectorExtension` proves the
unchanged proposition
`Langlands.GroupScheme.CharacteristicZeroReductiveVectorExtensionStatement.{u}`
for every universe `u`. Let `k : Type u` be a field of characteristic zero,
`E` an affine group scheme over `Spec k`, `H` a connected reductive group
scheme, and `q : E ⟶ H` a flat surjective homomorphism whose actual
scheme-theoretic kernel is a vector group of a specified finite dimension.
Then there is a group-scheme homomorphism `s : H ⟶ E` over `k` with
`s ≫ q = 𝟙 H`.

The proof has one step. It applies the conditional theorem
`characteristicZeroReductiveVectorExtension_of_semisimplicity` from
`Langlands.GroupScheme.Reductive.CharZeroInvariantIntegral` to the published
theorem `reductiveCharZeroSemisimplicityStatement` from
`Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof`. That theorem is
complete reducibility of finite coordinate representations of connected
reductive groups over algebraically closed fields of characteristic zero.

The conditional theorem combines two results already in the Library:

1. From complete reducibility, `invariantIntegralOfSemisimplicity` builds a
   normalized invariant integral on the coordinate algebra of `H` that is
   invariant over every coefficient algebra. Dual fixed vectors over the
   algebraic closure of `k` descend to `k`. Finite regular spans give local
   right integrals, the antipode turns them into local left integrals, and
   Fubini makes the local integrals agree, so they glue to one functional.
2. `characteristicZeroReductiveVectorExtension_of_invariantIntegral` averages
   the defect of a scheme section of `q`, which takes values in the vector
   kernel, against this integral. The corrected section is a homomorphism over
   `k`.

No premise remains. The proof does not use
`CharacteristicZeroLeviDecompositionStatement`, its proof family, or the
target proposition itself. The mathematical background is the Reynolds
operator of a linearly reductive group in Milne, *Algebraic Groups*
(2022 corrected reprint, registered `milne-2022-algebraic-groups`), printed
p.249. The Lean route is internal; the Markdown files of the two
imported modules describe it in detail.
