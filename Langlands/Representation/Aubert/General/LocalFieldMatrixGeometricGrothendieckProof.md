# Proof of the matrix geometric class formula

`Langlands.Aubert.General.RationalPointFamily.GL.localFieldMatrixGeometricGrothendieck`
has type `LocalFieldMatrixGeometricGrothendieckStatement.{u, v}`. For every
nonarchimedean local field `F` with its data `T : LocalFieldData F`, every
positive rank `n` and every pair of block shapes `B`, `C`, it gives the
standard-intersection refinements, the enumeration of the minimal Weyl
double-coset representatives and, for each finite-length smooth
representation of the Levi subgroup of `B` at carrier universe
`max (u + 1) v`, the class formula in exact finite-length K0.
[Statement](LocalFieldMatrixGeometricGrothendieckStatement.md)

The proof proceeds in three steps.

1. `Langlands.AllField.Geometric.padicGeometricLemma`, at the universes
   `u` and `max (u + 1) v`, gives the refinements `S` and `R`, their
   standard-intersection properties `hS` and `hR`, a number `m`, an
   enumeration `e : Fin m ≃ MinimalRepresentatives B C`, and a natural
   gluing of `Langlands.AllField.Geometric.jacquetInductionFunctor` from the
   geometric graded functors. The proof returns these same data as the
   witnesses of the statement. The composite
   `jacquetInductionFunctor T B C` is by definition normalized parabolic
   induction along `B`, then normalized Jacquet restriction along `C`, then
   the forgetful functor `SmoothRep.toRep`. The lemma
   `Langlands.AllField.CuspidalSupport.geometricPieceSmoothFunctor_toRep`
   identifies each geometric graded functor with
   `geometricPieceSmoothFunctor` followed by `SmoothRep.toRep`. Rewriting by
   these two facts and by associativity of functor composition turns the
   gluing into `IsGluedFrom (J ⋙ SmoothRep.toRep) (fun i => P i ⋙ SmoothRep.toRep)`.
   Here `J` is the smooth composite of the statement and `P i` is its `i`-th
   smooth geometric piece.

2. Let `A` be a finite-length smooth representation of the Levi subgroup of
   `B`. `Langlands.Aubert.General.RationalPointFamily.GL.localFieldMatrixParabolicPreservation`
   proves that normalized induction along `B` and normalized Jacquet
   restriction along `C` preserve finite length. Applied to `A`, then to the
   induced representation, it shows that `J.obj A` has finite length.

3. `Langlands.SmoothRep.filtrationGrothendieckStatement` applies to the
   gluing of step 1 and the finite-length object `J.obj A` of step 2. It
   gives finite length of every `(P i).obj A` and the equality of the class
   of `J.obj A` with the sum over `i : Fin m` of the classes of the pieces.
   These are the three remaining components of the statement.

The geometric filtration is that of Bernstein–Zelevinsky, *Induced
representations of reductive p-adic groups I* (1977), §2.12, printed
p. 448 (`bernstein-zelevinsky-1977-induced-i`). The class formula follows
from the short exact sequences of its successive steps.

## Dependencies

The proof uses only the Lean axioms `propext`, `Classical.choice` and
`Quot.sound`. Its four direct inputs are the all-field geometric lemma, the
identification of the smooth geometric pieces, the finite-length
preservation theorem and the exact finite-filtration class formula. The
finite-length input relies on the all-field finite-length results for
normalized induction and Jacquet restriction. The page of
`localFieldMatrixParabolicPreservation` lists the classification-module
declarations that its proof reaches.
