# Reduction of archimedean irreducibility to a multiplicity-one `O(n)`-type

Module `Langlands.Automorphic.CuspidalArchimedeanIrreducibleReductionStatement`, namespace
`Langlands.Automorphic`. It is a statement module and contains no proof.

## The statement

`CuspidalArchimedeanStandardIrreducibleReductionStatement : Prop` (universe parameter `u`) is
the implication

`Archimedean.RealStandardKTypeMultiplicityOneStatement →
  CuspidalArchimedeanStandardIrreducibleStatement.{u}`.

* The hypothesis is the module `RealStandardKTypeMultiplicityOneStatement`: every real standard
  module `realStandardModule n ds` with `realRank ds = n` contains some irreducible continuous
  representation of `O(n)` with multiplicity exactly one.
* The conclusion is the Library statement `CuspidalArchimedeanStandardIrreducibleStatement`
  (module `CuspidalArchimedeanComponentStatement`). Let `F` be a number field whose adele
  quotient is compact, and let `T` be an actual cuspidal realization of `GL_{r+1}` over `F`.
  Suppose the standard-module parameter of `T` at a real place is `ds : List RealBlock`, or at
  a complex place is `ds : List ComplexCharacterData`
  (`HasRealPlaceParameter`, `HasComplexPlaceParameter`). Then the `(𝔤, K)`-module of the
  standard module of `ds` is irreducible (`Archimedean.IsIrreducibleGKModule`).

## Provenance

The reduction is internal to this project; it is not a theorem from the literature. Its
hypothesis comes from Vogan, *Representations of Real Reductive Lie Groups* (1981),
Theorem 6.5.9(b), applied through Lemma 6.6.12 and Theorems 6.6.14 and 6.6.15 to modules
induced from discrete series (Definition 6.6.11); see
`RealStandardKTypeMultiplicityOneStatement.md`. At
complex places no extra hypothesis is needed, because the Library already proves a
multiplicity-one statement for the lowest `U(n)`-type (`complexLowestKTypeMultOne`).

The intended argument is as follows. Fix an infinite place `w`. The realization is irreducible,
so it is spanned by the images of one irreducible place component under the operators commuting
with the place actions at `w`. Hence it is a sum of copies of that component. A
`(𝔤, K)`-module embedding into such a sum is semisimple and isotypic. It is irreducible as soon
as some nonzero vector is mapped to a multiple of itself by every `(𝔤, K)`-endomorphism. At a
complex place such a vector is a lowest `U(n)`-type vector. At a real place it is a vector of
the multiplicity-one `O(n)`-type. The module `CuspidalArchimedeanIrreducibleReductionProof`
implements this argument.
