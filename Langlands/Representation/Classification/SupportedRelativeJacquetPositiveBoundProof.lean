import Langlands.Representation.Classification.SupportedRelativeJacquetPositiveBoundStatement
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Classification.RelativeJacquetEmbeddingProof
import Langlands.Representation.Parabolic.RefinedLeviRealTwistProof
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof

/-! Positive inner counts from supported quotients at arbitrary real parameters. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- The specified support quotient gives a nonzero adjoint map, so every
actual ambient count bounds an actual positive inner count. -/
theorem glSupportedRelativeJacquetPositiveBound :
    GLSupportedRelativeJacquetPositiveBoundStatement.{uF,uV,uW} := by
  intro p _ F T
  let := T.topology
  intro n hn B S ω hωi hωc v₀ π hπi hπa hsupport t τ πt M hM
  let := T.leviTopologicalGroup B
  obtain ⟨q₀, hq₀⟩ := hsupport
  obtain ⟨_E, _hE, _hEinv, hquot⟩ :=
    (refinedLeviRealTwist.{uF,uV,uW} p F T n B S ω v₀ t).2
  obtain ⟨qₜ, hqₜ, _⟩ := hquot π q₀ hq₀
  have hπti : Representation.IsIrreducible πt.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff B t π.ρ).mpr hπi
  have hπta : IsAdmissible πt.ρ :=
    (T.isAdmissible_leviRealPowerTwist_iff B t π.ρ).mpr hπa
  obtain ⟨hτi, hτa, _⟩ :=
    fineTwistIrreducibleAdmissible.{uF,uV} p F T n B S ω hωi hωc v₀ t
  have hqₜ0 : qₜ ≠ 0 := by
    let : Representation.IsIrreducible πt.ρ := hπti
    let : Nontrivial πt :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (B.Levi F.Carrier)) πt.ρ.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : πt)
    obtain ⟨x, hx⟩ := hqₜ v
    intro hzero
    apply hv
    rw [← hx, hzero]
    rfl
  obtain ⟨E, _hnat₁, _hnat₂⟩ :=
    Parabolic.normalizedSecondAdjointness.{uF,uV,uW}.2 p F T n hn B S
  have hnonzero : E τ πt hτa hπta qₜ ≠ 0 := by
    intro hz
    exact hqₜ0 ((E τ πt hτa hπta).injective
      (hz.trans (map_zero _).symm))
  obtain ⟨m, hm, hle⟩ :=
    (glRelativeJacquetEmbedding.{uF,uV,uW} p F T n hn B S πt hπti hπta).2
      τ M hM
  refine ⟨m, ?_, hm, hle⟩
  exact SimpleMapMultiplicityDetectionProof.positive_of_simple_map hτi m hm
    (Or.inl ⟨E τ πt hτa hπta qₜ, hnonzero⟩)

end Langlands
