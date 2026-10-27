import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Langlands.Representation.Parabolic.OppositeRefinementFunctors

/-! Finite intertwiner spaces from an actual fine twist into the actual
normalized refined and composed opposite Jacquet modules. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric

universe uF uV uW uZ

/-- The actual fine twist of an irreducible cuspidal representation has
finite-dimensional intertwiner spaces into the normalized refined opposite
Jacquet module of every admissible coarse-Levi representation, and into the
normalized composed opposite Jacquet module of every admissible
representation of `GL_n`. -/
def FineOppositeJacquetHomFinitenessStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
      ∀ (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
        let τ := RelativeJacquetMultiplicity.fineTwist T B S ω v₀ t
        (∀ π : Rep.{uW} ℂ (B.Levi F.Carrier), IsAdmissible π.ρ →
          FiniteDimensional ℂ (τ.ρ.IntertwiningMap
            (T.normalizedRefinedOppositeJacquet B S π.ρ))) ∧
        (∀ J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier), IsAdmissible J.ρ →
          FiniteDimensional ℂ (τ.ρ.IntertwiningMap
            (T.normalizedComposedOppositeJacquet B S J.ρ)))

end Langlands
