import Langlands.GroupScheme.Torus.SplitDescent
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingStatement
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Reflection of split tori along base maps admitting sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Finite Galois splitting, when supplied, makes tori split over an algebraically closed base. -/
theorem IsTorus.isSplitTorus_of_finiteGaloisSplitting
    (hsplit : TorusFiniteGaloisSplittingStatement.{u}) {k : Type u} [Field k] [IsAlgClosed k]
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) : IsSplitTorus T := by
  obtain ⟨K, hK, hAlg, hfinite, _, hsplitK⟩ := hsplit k T hT
  let : Field K := hK
  let : Algebra k K := hAlg
  let : FiniteDimensional k K := hfinite
  exact IsSplitTorus.of_baseChange_of_isAlgebraic hsplitK

end Langlands.GroupScheme
