import Langlands.Representation.Geometric.ParabolicSupportJacquetStatement
import Langlands.AllField.Representation.Geometric.ParabolicOrbitJacquet
/-! Exactness comparison for the fixed support-image filtration. -/

namespace Langlands.AllField.Geometric
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicSupportJacquetComparison geometricPieceFunctor jacquetInductionFunctor parabolicInductionSupportFiltration parabolicJacquetImageSubfunctor parabolicJacquetSupportFiltration parabolicOrbitJacquetFunctor
open Langlands.AllField.Geometric

open _root_.CategoryTheory
open Langlands.GeneralLinear

universe uF uV

/-- The successive quotients of the fixed normalized Jacquet image filtration
are naturally the normalized radical coinvariants of the support quotients. -/
def PadicParabolicSupportJacquetComparison : Prop :=
  ∀ (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) (B C : BlockShape n),
    letI := T.topology
    ∀ (m : ℕ)
      (s : OrderedDoubleCosets (B.parabolic F) (C.parabolic F) m)
      (i : Fin m),
      Nonempty ((parabolicJacquetSupportFiltration.{uF, uV} T B C s).graded i ≅
        (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i ⋙
          Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C))

end Langlands.AllField.Geometric
