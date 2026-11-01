import Langlands.Representation.Classification.RelativeCosocleMultiplicityStatement
import Langlands.Representation.Classification.RelativeCosocleHomComparisonProof
import Langlands.Representation.Classification.RelativeCosocleAdmissibilityProof
import Langlands.Representation.Classification.HeadHomMultiplicityProof
import Langlands.Representation.Classification.FineTwistRegularityProof
import Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionLengthProof
import Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonProof

/-! Relative cosocle multiplicities from actual opposite-Jacquet Hom comparison. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands

open GeneralLinear Geometric
open RelativeJacquetMultiplicity RelativeRegularComparison

universe uG uH uA uB uC uF uV uM uW uZ

namespace RelativeCosocleMultiplicityProof

section Hom

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  {A : Type uA} {B : Type uB} {C : Type uC}
  [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
  [AddCommGroup C] [Module ℂ C]

private def homPostcompEquiv (ρ : Representation ℂ G A)
    {σ : Representation ℂ G B} {τ : Representation ℂ G C} (e : σ.Equiv τ) :
    (ρ.IntertwiningMap σ) ≃ₗ[ℂ] (ρ.IntertwiningMap τ) where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  left_inv f := by ext x; exact e.symm_apply_apply (f x)
  right_inv f := by ext x; exact e.apply_symm_apply (f x)

private def homChangeGroup (e : G ≃* H) (ρ : Representation ℂ G A)
    (σ : Representation ℂ H B) :
    (ρ.IntertwiningMap (σ.comp e.toMonoidHom)) ≃ₗ[ℂ]
      Representation.IntertwiningMap (ρ.comp e.symm.toMonoidHom) σ where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' h := by
        simpa using f.isIntertwining' (e.symm h) }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' g := by
        simpa using f.isIntertwining' (e g) }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

end Hom

private theorem transportFineData {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} {C D : BlockShape n} (h : C = D)
    (ω : Rep.{uV} ℂ (C.Levi F.Carrier)) :
    letI := T.topology
    Representation.IsIrreducible ω.ρ → CuspidalSupport.IsLeviCuspidal C ω.ρ →
      Representation.IsIrreducible (h ▸ ω : Rep ℂ (D.Levi F.Carrier)).ρ ∧
        CuspidalSupport.IsLeviCuspidal D (h ▸ ω : Rep ℂ (D.Levi F.Carrier)).ρ := by
  cases h
  exact fun hi hc => ⟨hi, hc⟩

private theorem ambientLengthAdapter {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (hlength : CuspidalSupport.CuspidalInductionLengthTheorem.{uF, uV} F T n)
    (hirr : Representation.IsIrreducible σ.ρ)
    (hcusp : letI := T.topology; CuspidalSupport.IsLeviCuspidal B σ.ρ) :
    letI := T.topology
    IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (CuspidalJacquetMultiplicity.induced T B σ).ρ.asModule := by
  let := T.topology
  have hraw := (hlength B (SmoothRep.of σ.ρ hcusp.1.1) hirr hcusp).1
  dsimp only [CuspidalJacquetMultiplicity.induced, Rep.of,
    SmoothRep.of, SmoothRep.representation,
    PadicField.TopologicalData.normalizedParabolicInduced,
    BlockShape.normalizedInducedOf, Induction.normalizedSmoothInduced,
    BlockShape.inflateCharacter, PadicField.TopologicalData.leviHalfCharacter,
    PadicField.TopologicalData.parabolicHalfModulus] at hraw ⊢
  exact hraw

set_option maxHeartbeats 800000 in
private theorem fineAmbientHomRank {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (S : BlockRefinement B) (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
    (v : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)
    (J : Rep.{uZ} ℂ (GeneralLinear n F.Carrier))
    (hstandard : Parabolic.StandardSecondAdjointnessClause.{uF, uV, uZ})
    (hω : letI := T.topology; IsAdmissible (T.leviRealPowerTwist (B.flatten S)
      (fun k => -v k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ))
    (hJ : letI := T.topology; IsAdmissible J.ρ) :
    Module.finrank ℂ ((RelativeRecovery.fineAmbientInduced T B S ω v t).ρ.IntertwiningMap J.ρ) =
      Module.finrank ℂ ((fineTwist T B S ω v t).ρ.IntertwiningMap
        (T.normalizedComposedOppositeJacquet B S J.ρ)) := by
  let := T.topology
  obtain ⟨Eout, -⟩ := hstandard p F T n hn (B.flatten S)
  obtain ⟨φ, -⟩ :=
    Parabolic.flattenedOppositeJacquetComparison.{uF, uF, uZ}.2 p F T n B S J
  let α := Rep.of (T.leviRealPowerTwist (B.flatten S)
    (fun k => -v k + t ((B.flattenBlockEquiv S).symm k).1) ω.ρ)
  let e := flattenedLeviEquiv F.Carrier B S
  let Etransport := (homPostcompEquiv α.ρ φ.symm).trans
    (homChangeGroup e α.ρ (T.normalizedComposedOppositeJacquet B S J.ρ))
  exact (Eout α J hω hJ).finrank_eq.trans Etransport.finrank_eq

private theorem innerHomRank {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData) {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (S : BlockRefinement B) (τ : Rep.{uV} ℂ (refinedLevi F.Carrier B S))
    (π : Rep.{uW} ℂ (B.Levi F.Carrier))
    (hrefined : Parabolic.RefinedSecondAdjointnessClause.{uF, uV, uW})
    (hτ : letI := T.topology; IsAdmissible τ.ρ)
    (hπ : letI := T.topology; IsAdmissible π.ρ) :
    Module.finrank ℂ ((innerInduced T B S τ).ρ.IntertwiningMap π.ρ) =
      Module.finrank ℂ (τ.ρ.IntertwiningMap
        (T.normalizedRefinedOppositeJacquet B S π.ρ)) := by
  let := T.topology
  obtain ⟨E, -⟩ := hrefined p F T n hn B S
  exact (E τ π hτ hπ).finrank_eq

private theorem commonHeadMultiplicity {G : Type uG} {H : Type uH}
    [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    (A : Rep.{uA} ℂ G) (B : Rep.{uB} ℂ H)
    (J : Rep.{uC} ℂ G) (π : Rep.{uW} ℂ H)
    (hA : IsFiniteLength (MonoidAlgebra ℂ G) A.ρ.asModule)
    (hB : IsFiniteLength (MonoidAlgebra ℂ H) B.ρ.asModule)
    (hJ : IsAdmissible J.ρ) (hπ : IsAdmissible π.ρ)
    (hJi : Representation.IsIrreducible J.ρ)
    (hπi : Representation.IsIrreducible π.ρ)
    (hdim : Module.finrank ℂ (A.ρ.IntertwiningMap J.ρ) =
      Module.finrank ℂ (B.ρ.IntertwiningMap π.ρ)) :
    ∃ m : ℕ, HasJordanHolderMultiplicity (Rep.of (Classification.head A.ρ)) J m ∧
      HasJordanHolderMultiplicity (Rep.of (Classification.head B.ρ)) π m := by
  obtain ⟨-, hout⟩ := Classification.finiteLengthHeadHomMultiplicity.1 G A J hA hJ hJi
  obtain ⟨-, hin⟩ := Classification.finiteLengthHeadHomMultiplicity.1 H B π hB hπ hπi
  exact ⟨_, hout, hdim.symm ▸ hin⟩

end RelativeCosocleMultiplicityProof

open RelativeCosocleMultiplicityProof

set_option maxHeartbeats 800000 in
/-- The canonical heads of the fine ambient and fine inner inductions have
one common Jordan–Hölder multiplicity for every actual outer quotient and
arbitrary irreducible tempered coarse input. The multiplicity may be zero. -/
theorem relativeCosocleMultiplicity :
    GLRelativeCosocleMultiplicityStatement.{uF, uV, uM, uW, uZ} := by
  have hcomparison := relativeCosocleHomComparison.{uF, uV, uM, uW, uZ}
  have hstandard := Parabolic.normalizedSecondAdjointness.{uF, uV, uZ}.1
  have hrefined := Parabolic.normalizedSecondAdjointness.{uF, uV, uW}.2
  have hadm := relativeCosocleAdmissibility.{uF, uW, uZ}
  dsimp only [GLRelativeCosocleMultiplicityStatement]
  intro p _ F T
  let := T.topology
  intro n hn B Q R S h ω hωirr hωcusp hωunit v₀ hv₀ σ hσirr hσdisc hσquot
    π hπirr hπtemp t ht J hJirr hJquot
  let D := B.flatten Q
  let ωB : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier) := h ▸ ω
  let vB : Fin (B.flatten S).length → ℝ := h ▸ v₀
  obtain ⟨hωBirr, hωBcusp⟩ := transportFineData T h ω hωirr hωcusp
  let s₀ : Fin (B.flatten S).length → ℝ :=
    fun k => -vB k + (0 : Fin B.length → ℝ) ((B.flattenBlockEquiv S).symm k).1
  let st : Fin (B.flatten S).length → ℝ :=
    fun k => -vB k + t ((B.flattenBlockEquiv S).symm k).1
  let α₀ := Rep.of (T.leviRealPowerTwist (B.flatten S) s₀ ωB.ρ)
  let αt := Rep.of (T.leviRealPowerTwist (B.flatten S) st ωB.ρ)
  let τ₀ := fineTwist T B S ωB vB 0
  let τt := fineTwist T B S ωB vB t
  let Aout := RelativeRecovery.fineAmbientInduced T B S ωB vB t
  let Ain := innerInduced T B S τ₀
  change ∃ m : ℕ,
    HasJordanHolderMultiplicity (Rep.of (Classification.head Aout.ρ)) J m ∧
      HasJordanHolderMultiplicity (Rep.of (Classification.head Ain.ρ)) π m
  have hreg₀ := fineTwistIrreducibleAdmissible p F T n B S ωB hωBirr hωBcusp vB 0
  have hregt := fineTwistIrreducibleAdmissible p F T n B S ωB hωBirr hωBcusp vB t
  have hα₀irr : Representation.IsIrreducible α₀.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff _ _ _).mpr hωBirr
  have hαtirr : Representation.IsIrreducible αt.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff _ _ _).mpr hωBirr
  have hα₀cusp : CuspidalSupport.IsLeviCuspidal (B.flatten S) α₀.ρ := hreg₀.2.2
  have hαtcusp : CuspidalSupport.IsLeviCuspidal (B.flatten S) αt.ρ := hregt.2.2
  have hπadm : IsAdmissible π.ρ := (hadm p F T n B π).1 hπtemp
  obtain ⟨q, hq⟩ := hJquot
  have hJadm : IsAdmissible J.ρ :=
    ((hadm p F T n B π).2.2 hπadm t).2.2 J q hq
  have hLout : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      Aout.ρ.asModule := by
    change IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (CuspidalJacquetMultiplicity.induced T (B.flatten S) αt).ρ.asModule
    exact ambientLengthAdapter T (B.flatten S) αt
      (CuspidalSupport.cuspidalInductionLength.{uF, uV} F T n) hαtirr hαtcusp
  have hLin : IsFiniteLength (MonoidAlgebra ℂ (B.Levi F.Carrier))
      Ain.ρ.asModule :=
    (CuspidalSupport.refinedCuspidalInductionFiniteLength.{uF, uV}
      p F T n B S α₀ hα₀irr hα₀cusp).2.1
  have hαtadm : IsAdmissible αt.ρ := hαtcusp.1
  have houtdim := fineAmbientHomRank T hn B S ωB vB t J hstandard hαtadm hJadm
  have hτ₀adm : IsAdmissible τ₀.ρ := hreg₀.2.1
  have hindim := innerHomRank T hn B S τ₀ π hrefined hτ₀adm hπadm
  have hcmp := hcomparison p F T n hn B Q R S h ω hωirr hωcusp hωunit
    v₀ hv₀ σ hσirr hσdisc hσquot π hπirr hπtemp t ht J hJirr ⟨q, hq⟩
  have hdim : Module.finrank ℂ (Aout.ρ.IntertwiningMap J.ρ) =
      Module.finrank ℂ (Ain.ρ.IntertwiningMap π.ρ) :=
    houtdim.trans (hcmp.2.2.trans hindim.symm)
  exact commonHeadMultiplicity Aout Ain J π hLout hLin hJadm hπadm hJirr hπirr hdim

end Langlands
