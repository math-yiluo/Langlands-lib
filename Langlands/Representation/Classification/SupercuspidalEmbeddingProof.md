# Embedding into a product of supercuspidal representations

Author: Worker 78. The accompanying transport helpers are by Worker 195.

`Langlands.glSupercuspidalEmbedding` proves exactly
`Langlands.GLSupercuspidalEmbeddingStatement.{uV,uF}` from
[SupercuspidalSupportStatement](SupercuspidalSupportStatement.md).
For every prime `p`, actual p-adic field `F : PadicField.{uF} p`,
compatible topological datum `T`, positive rank `n` and irreducible smooth
complex representation `π` of `GL_n(F)` with carrier in `Type (max uF uV)`,
it supplies a finite ordered family
`ρ : Fin k → CuspidalDatum.{uV,uF} T` with
`T.IsCuspidalSubrepresentation ρ π`.
Thus `π` embeds into the normalized product of actual supercuspidal
representatives of these data, whose positive ranks sum to `n`.
The factors have carriers in `Type uV`, independently of the field universe.

## Implemented proof

After introducing the parameters, the proof installs the topology and matrix
topological-group structure supplied by `T`.

1. Apply `Langlands.CuspidalSupport.cuspidalEmbedding.{uF,max uF uV}`
   from [CuspidalEmbeddingProof](../CuspidalSupport/CuspidalEmbeddingProof.md)
   (Worker 156) to `π` and its irreducibility proof. This gives an ordered
   block shape `B`, an irreducible cuspidal smooth Levi representation `σ`,
   and an injective intertwiner `j` from `π` into normalized induction of
   `σ`. The source admissibility conclusion is not needed here.
2. Apply
   `Langlands.CuspidalSupport.padicLeviCuspidalFactorization.{uF,max uF uV,uV}`
   from [LeviTensorFactorizationProof](../CuspidalSupport/LeviTensorFactorizationProof.md)
   (Worker 82), using `n > 0`, irreducibility and cuspidality of `σ`.
   This supplies supercuspidal block factors `A i` in the prescribed
   universe `uV` and an actual representation equivalence `e` from `σ`
   to their external block tensor.
3. Apply
   `T.exists_cuspidalSubrepresentation_of_levi_equiv`
   from [SupercuspidalEmbeddingTransport](SupercuspidalEmbeddingTransport.md).
   This helper induces `e`, composes its injective intertwiner with `j`,
   and packages the ranks and isomorphism classes of `A i` as cuspidal data.
   It retains `π`'s irreducibility and the resulting actual embedding.

The normalized induction expression returned in the first step is
definitionally `T.normalizedParabolicInduced B σ.representation`.
Transport uses the same standard upper block parabolic and the same
positive-half modulus character. The block tensor induces to
`T.normalizedProductInduced B (fun i => (A i).obj.representation)`.
Packaging the ranks reconstructs `B` definitionally, so this is precisely
the representation in the published `IsCuspidalSubrepresentation` relation.

Both existence results are imported closing theorems. The source and Levi
carriers have universe `max uF uV`, while the tensor factors have universe
`uV`; the second imported theorem supplies the necessary change of carrier.
There is no added admissibility, finite-length, central-character, countability,
factorization or universe-identification hypothesis. This module proves the
embedding statement only; uniqueness of supercuspidal support is a separate
published proposition.

## Provenance

This is an internal composition of published results, with elementary
transport and packaging in the accompanying helper module. It preserves
the target statement and all its imported Lean/Markdown pairs.

The target's original mathematical source is A. V. Zelevinsky,
*Induced representations of reductive p-adic groups II. On irreducible
representations of GL(n)* (1980), §1.10, printed page 174 / PDF page 11,
registered as `zelevinsky-1980-induced-ii`. Its embedding assertion refers
to Bernstein and Zelevinsky, *Induced representations of reductive p-adic
groups I* (1977), Theorem 2.5, printed page 447 / PDF page 8,
registered as `bernstein-zelevinsky-1977-induced-i`. These passages were
read. The latter gives the cuspidal Levi embedding used by the first
imported theorem. The tensor factorization, comparison of cuspidality
predicates and independent-universe realization are supplied by the second
imported proof and its documented prerequisites. The present proof uses
their implemented interfaces without claiming to repeat the historical
arguments.
