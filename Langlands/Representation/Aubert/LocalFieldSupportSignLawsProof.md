# Proof of the support-sign laws

`Langlands.Aubert.LocalFieldGraded.localFieldSupportSignLaws` proves
`LocalFieldSupportSignLawsStatement.{uF,uV}` for every nonarchimedean
local field package `K`, every topological realization `T`, and every
witness `h` that the binary normalized induction product is exact and
preserves finite length. The field universe `uF` and the representation
universe `uV` stay independent. The proof works in the full direct sum
of the exact finite-length Grothendieck groups of
\(\mathrm{GL}_n(F)\), rank zero included.

The sign `sign n` is `adjustOperator T n LinearMap.id`. On the class of an
irreducible representation \(A\) of rank \(n\), it multiplies by
\((-1)^{n-k}\), where \(k\) is the size of the supercuspidal support of
\(A\) (`adjustOperator_irreducible`). This is Aubert's adjustment
(Aubert 1995, Notation 1.6 and Definition 2.1, `aubert-1995-duality`).

## Reduction to irreducible classes

`ext_irreducible` shows that two `ℤ`-linear maps out of a homogeneous
exact Grothendieck group agree if they agree on every actual irreducible
class. Maps out of the free group on irreducible isomorphism classes are
determined by the generators (`integral_hom_ext`), and each generator
realizes to an actual irreducible class
(`realizeIrreducibles_generator_irreducibleIsoClass`). Hence the two maps
agree after composition with the Jordan–Hölder realization
`realizeIrreducibles`. The Jordan–Hölder realization is a left inverse of
`factorMap` (`realize_comp_factorMap`), so each exact class `x` is
`realizeIrreducibles (factorMap x)`. The two maps therefore agree at `x`.

Both homogeneous clauses follow from `ext_irreducible` and
`adjustOperator_irreducible`. For `adjust_comp`, both sides send an
irreducible class \([A]\) to \(\epsilon(A)\,D[A]\), where \(\epsilon(A)\)
is the support sign. For `sign_square`, \(\epsilon(A)^2 = 1\) because
\(\epsilon(A)\) is a power of \(-1\).

## Products in positive ranks

Let \(A\) and \(B\) be irreducible of positive ranks \(a\) and \(b\).
`AllFieldBZ.glSupercuspidalEmbedding` embeds each of them in a
normalized product of supercuspidals, which gives supports \(s\) of
\(A\) and \(t\) of \(B\). Every supercuspidal block has positive rank
(`cuspidalShape`, `length_le`), so \(|s| \le a\) and \(|t| \le b\).
`binaryNormalizedProductPositiveIso` identifies the binary normalized
product with the normalized product on `BlockShape.binary a b`. Applied to
that block shape,
`AllFieldBZ.CuspidalSupport.productConstituentSupport` shows that every
irreducible subquotient \(P\) of \(A \times B\) has support \(s + t\).
`supportSign_of_support` then gives
\(\epsilon(P) = (-1)^{a+b-|s|-|t|} = \epsilon(A)\,\epsilon(B)\).

`sign_of_constituents` turns this into an identity of classes. Suppose
every irreducible subquotient of a finite-length representation \(M\) has
sign \(\sigma\). Then `sign` sends \([M]\) to \(\sigma\,[M]\). The proof
writes \([M]\) as the realization of its Jordan–Hölder vector
`compositionFactors`. An irreducible class lies in the support of that
vector exactly when it is an actual subquotient of \(M\)
(`mem_support_compositionFactors_iff_isSubquotient`). Therefore
\(\operatorname{sign}[A \times B] = \epsilon(A)\epsilon(B)[A \times B]\),
since `binaryProduct_objects` identifies the product of classes with the
class of the product. The product of classes is bilinear. Two applications
of `ext_irreducible` then extend the identity to all homogeneous classes
of positive ranks.

## Rank zero

Each irreducible representation of the trivial group
\(\mathrm{GL}_0(F)\) is a simple module. Hence it is equivalent to the
actual trivial line `unitObject T` (the private lemma
`rankZero_equiv_unit`). By the Jordan–Hölder theorem
`irreducibleGrothendieckStatement`, every rank-zero class is an integer
multiple of `unit T`. The rank-zero sign is \(1\) (`supportSign_rankZero`),
so the graded sign fixes `unit T`, which is the fourth clause.

The private lemmas `unit_mul` and `mul_unit` prove that `unit T` is a
two-sided unit of `multiplication T h`. On homogeneous objects they use
`binaryLeftZeroTensorEquiv` and `binaryRightZeroTensorEquiv` together with
`BinaryTensor.secondFactorUnitEquiv` and
`BinaryTensor.firstFactorUnitEquiv`, after reindexing ranks along
\(0 + b = b\) and \(a + 0 = a\). `hom_ext_object` and
`DirectSum.linearMap_ext` extend these identities to the whole direct sum.
The file proves these rank-zero facts itself.

## The graded product

`gradedSign_multiplication` proves the third clause. Both sides are
bilinear, so `DirectSum.linearMap_ext` reduces it to homogeneous classes
of ranks \(a\) and \(b\). If \(a = 0\) or \(b = 0\), that factor is an
integer multiple of `unit T`, and the unit laws give the identity. If
\(a, b > 0\), it is the positive-rank product identity, after
`multiplication_homogeneous`.

## Classification dependencies

All classification input enters through the following Library theorems.

- `Langlands.AllFieldBZ.glSupercuspidalEmbedding` embeds an irreducible
  representation of positive rank in a normalized product of
  supercuspidals. The proof calls it directly to choose supports, and the
  definition of `supportSign` also uses it.
- `Langlands.AllFieldBZ.glSupercuspidalSupportUniqueness` states that the
  supercuspidal support is unique. The proof does not call it directly. It
  enters through `supportSign_of_support` and `productConstituentSupport`.
- `productConstituentSupport` additionally uses
  `Langlands.AllFieldBZ.Classification.normalizedProduct_embedding_of_factor_embeddings`,
  which turns blockwise embeddings into an embedding of normalized
  products. Through it, `productConstituentSupport` also uses
  `Langlands.FiniteTensor.externalMap_injective`. These two are the only
  classification declarations that the proof reaches beyond those the
  statement already uses.

These facts come from a transitive traversal of the constants used by the
proof, expanding every `Langlands` constant together with the constructors
and recursors of its inductive types. A declaration counts as
classification input when its module lies under
`Langlands.AllFieldBZ.Representation.Classification` or
`Langlands.Representation.Classification`. These declarations lie in
thirteen modules. The seven modules under
`Langlands.AllFieldBZ.Representation.Classification` are `Segments`,
`SupercuspidalEmbeddingProof`, `SupercuspidalEmbeddingTransport`,
`SupercuspidalSupport`, `SupercuspidalSupportStatement`,
`SupercuspidalSupportUniquenessProof` and `IrreducibleProductEmbedding`.
The six modules under `Langlands.Representation.Classification` are
`ConstituentRelations`, `IrreducibleProductEmbedding`, `Supercuspidal`,
`SupercuspidalContragredientAux`, `SupercuspidalSupport` and
`SupercuspidalTwist`. The statement alone reaches eleven of these modules.
The two others are the two `IrreducibleProductEmbedding` modules, reached
only through `productConstituentSupport`.

The product and the support relation follow Zelevinsky, *Induced
representations of reductive p-adic groups II* (1980), §§1.7 and 1.10
(`zelevinsky-1980-induced-ii`).
