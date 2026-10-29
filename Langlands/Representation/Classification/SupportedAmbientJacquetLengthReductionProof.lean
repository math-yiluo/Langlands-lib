import Langlands.Representation.Classification.SupportedAmbientJacquetLengthReductionStatement
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.Parabolic.FineAmbientQuotientTransportProof
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetFiniteLengthProof
import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonProof
import Langlands.Representation.Filtration.MultiplicityAdditivityProof

/-! Conditional construction of actual supported ambient Jacquet series. -/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- A specified support quotient and standard cuspidal induction length produce
finite length of the outer induction and its actual ambient Jacquet module. -/
theorem glSupportedAmbientJacquetLengthReduction :
    GLSupportedAmbientJacquetLengthReductionStatement.{uF,uV,uW} := by
  intro p _ F T
  let := T.topology
  intro n _hn hlen B S ω hωi hωc v₀ π hπa hsupport t τ πt
  let := T.leviTopologicalGroup B
  let := T.generalLinearTopologicalGroup n
  let α := T.leviRealPowerTwist (B.flatten S)
    (fun k => -v₀ k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ
  have hαi : Representation.IsIrreducible α :=
    (T.isIrreducible_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hωi
  have hαc : CuspidalSupport.IsLeviCuspidal (B.flatten S) α :=
    (T.isLeviCuspidal_leviRealPowerTwist_iff (B.flatten S) _ ω.ρ).mpr hωc
  have hfine : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (RelativeRecovery.fineAmbientInduced T B S ω v₀ t).ρ.asModule :=
    (hlen (B.flatten S) (SmoothRep.of α hαc.1.1) hαi hαc).1
  let I := CuspidalJacquetMultiplicity.induced T B πt
  obtain ⟨q₀, hq₀⟩ := hsupport
  obtain ⟨qf, hqf⟩ :=
    fineAmbientQuotientTransport.{uF,uV,uW,max uF uW} p F T n B S ω hωc.1.1
      v₀ t π q₀ hq₀ I (Representation.IntertwiningMap.id I.ρ) Function.surjective_id
  have hI : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      I.ρ.asModule :=
    FiniteLengthAssembly.finiteLength_of_surjective qf hqf hfine
  have hπta : IsAdmissible πt.ρ :=
    (T.isAdmissible_leviRealPowerTwist_iff B t π.ρ).mpr hπa
  have hIa : IsAdmissible I.ρ :=
    Parabolic.normalizedInductionAdmissibility F T B _ πt.ρ hπta
  have hIfg : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      I.ρ.asModule := by
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hI).1
    infer_instance
  have hJo := Parabolic.oppositeJacquetFiniteLength T (B.flatten S) I.ρ hIa hIfg
  obtain ⟨E, _hE⟩ :=
    Parabolic.flattenedOppositeJacquetComparison.{uF,uF,max uF uW}.2 p F T n B S I
  have hJpull : IsFiniteLength (MonoidAlgebra ℂ ((B.flatten S).Levi F.Carrier))
      (Representation.asModule ((ambientJacquet T B S πt).ρ.comp
        (flattenedLeviEquiv F.Carrier B S).toMonoidHom)) :=
    FiniteLengthAssembly.finiteLength_of_injective E.toIntertwiningMap E.injective hJo
  have hJ : IsFiniteLength (MonoidAlgebra ℂ (refinedLevi F.Carrier B S))
      (ambientJacquet T B S πt).ρ.asModule :=
    (FiniteLengthAssembly.finiteLength_comp_surjective_iff
      (ambientJacquet T B S πt).ρ
      (flattenedLeviEquiv F.Carrier B S).toMonoidHom
      (flattenedLeviEquiv F.Carrier B S).surjective).mpr hJpull
  obtain ⟨r, s, hs⟩ := MultiplicityAdditivityProof.exists_series hJ
  exact ⟨hI, hJ, s.factorMultiplicity τ, r, s, hs, rfl⟩

end Langlands
