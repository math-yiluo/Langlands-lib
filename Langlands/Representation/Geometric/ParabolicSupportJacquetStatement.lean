import Langlands.Representation.Geometric.ParabolicOrbitJacquet

/-! Exactness comparison for the fixed support-image filtration. -/

namespace Langlands.Geometric

open GeneralLinear CategoryTheory

universe uF uV

/-- The successive quotients of the fixed normalized Jacquet image filtration
are naturally the normalized radical coinvariants of the support quotients. -/
def PadicParabolicSupportJacquetComparison : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) (B C : BlockShape n),
    letI := T.topology
    ∀ (m : ℕ)
      (s : OrderedDoubleCosets (B.parabolic F.Carrier) (C.parabolic F.Carrier) m)
      (i : Fin m),
      Nonempty ((parabolicJacquetSupportFiltration.{uF, uV} T B C s).graded i ≅
        (parabolicInductionSupportFiltration.{uF, uV} T B C s).graded i ⋙
          Parabolic.normalizedCoinvariantsFunctor C (T.leviModulus C))

end Langlands.Geometric
