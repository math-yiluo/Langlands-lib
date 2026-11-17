import Langlands.GroupScheme.Reductive.AbsoluteCartanClassificationStatement
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Finite indecomposable Cartan matrices on actual absolute vertices -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TitsIndexData

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The actual vertex type is nonempty and its full integral Cartan matrix is
finite and indecomposable. The finite enumeration here is only an instance. -/
def HasFiniteIndecomposableCartan : Prop :=
  letI : Fintype d.Vertex := Fintype.ofFinite _
  letI : DecidableEq d.Vertex := Classical.decEq _
  Nonempty d.Vertex ∧
    (Matrix.of d.cartan).IsFiniteCartan ∧ (Matrix.of d.cartan).IsIndecomposable

end TitsIndexData

/-- Absolute almost-simplicity gives the matrix hypotheses needed for finite
Cartan exhaustion, on every supplied actual Tits index over every field. -/
def AbsolutelyAlmostSimpleFiniteCartanStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsAbsolutelyAlmostSimple G → d.HasFiniteIndecomposableCartan

end Langlands.GroupScheme
