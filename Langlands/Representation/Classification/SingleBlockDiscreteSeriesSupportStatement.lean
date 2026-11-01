import Langlands.Representation.Classification.DiscreteSeriesPositiveRootSupportStatement
import Langlands.Group.GL.SingleBlock

/-!
# Unitary cuspidal support for square-integrable GL representations

Transport the product-Levi support assertion through the actual single-block
Levi equivalence, keeping the given GL representation as the quotient target.
-/

namespace Langlands

open GeneralLinear Geometric

universe uF uV

/-- Analytic discrete series of `GL_n` are actual quotients of single-block
refined upper induction from unitary cuspidal data with a strict root parameter.
The source action is transported through the constructed single-block map. -/
def GLSingleBlockDiscreteSeriesSupportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (C : BlockShape n) (hC : C.length = 1)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      Representation.IsIrreducible ρ → T.IsSquareIntegrable ρ →
      ∃ (R : BlockRefinement C)
        (ω : Rep.{max uF uV} ℂ ((C.flatten R).Levi F.Carrier))
        (t : Fin (C.flatten R).length → ℝ),
        Representation.IsIrreducible ω.ρ ∧
        CuspidalSupport.IsLeviCuspidal (C.flatten R) ω.ρ ∧
        IsUnitarizable ω.ρ ∧
        RelativeRegularComparison.IsPositiveRootParameter C R t ∧
        ∃ q : Representation.IntertwiningMap
          ((RelativeJacquetMultiplicity.innerInduced T C R
          (RelativeJacquetMultiplicity.fineTwist T C R ω t 0)).ρ.comp
            (C.singleBlockLeviEquiv hC F.Carrier).symm.toMonoidHom) ρ,
          Function.Surjective q

end Langlands
