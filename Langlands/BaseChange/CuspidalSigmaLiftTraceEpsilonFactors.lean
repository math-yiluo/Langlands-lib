import Langlands.AllField.HarmonicAnalysis.PadicSelfDualMeasureExistsProof
import Langlands.BaseChange.CuspidalSigmaLiftPadicEpsilonFactors
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.LocalFactor.Abelian.Scaling
import Langlands.LocalField.CharZeroPadicRealization
import Langlands.LocalField.SuppliedPadicExtension
import Langlands.LocalField.SuppliedPadicNormalization

/-! # Local epsilon data on characteristic-zero fields and their trace characters -/

noncomputable section

namespace Langlands.BaseChange

open CharZeroLocalField LocalField
open HarmonicAnalysis (UnitaryAdditiveCharacter)
open LocalFactor.PadicAbelian (uniformizerUnit uniformizerUnit_ord)

universe u v uV uW

/-- Local factor and conductor certificates on the original characteristic-zero
local fields, for arbitrary additive characters and supplied self-dual measures. -/
def CuspidalSigmaLiftCharZeroEpsilonFactorsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E] [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (k s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (k + 1) F) V),
    π.IsIrreducible → GeneralLinear.IsSupercuspidal π →
    ∀ {W₁ : Type uW} [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
    P₁.IsIrreducible → GeneralLinear.IsSupercuspidal P₁ →
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear (k + 1) E) W),
    Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
      (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    ∀ (X : Finset (Fˣ →* ℂˣ)), (∀ κ ∈ X, IsNormTrivial E κ) →
    ∀ (ψF : UnitaryAdditiveCharacter F) (ψE : UnitaryAdditiveCharacter E)
      (νF : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances F) ψF)
      (νE : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances E) ψE),
    ∃ (aF : (Fˣ →* ℂˣ) → ℕ) (aOrbit : Fin s → ℕ)
      (eF : (Fˣ →* ℂˣ) → ℂˣ × ℤ) (eOrbit : Fin s → ℂˣ × ℤ) (eP : ℂˣ × ℤ),
      (∀ κ ∈ X, IsStandardEpsilonConductor ψF νF.val
        (twist (κ.comp GeneralLinear.determinant) π) (aF κ) (eF κ)) ∧
      (∀ i : Fin s, IsStandardEpsilonConductor ψE νE.val
        (P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom) (aOrbit i) (eOrbit i)) ∧
      OrbitProductEpsilonMultiplicativity ψE νE.val P eOrbit eP

set_option maxHeartbeats 500000 in
theorem cuspidalSigmaLiftCharZeroEpsilonFactors :
    CuspidalSigmaLiftCharZeroEpsilonFactorsStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ _ σ k s k₁ hr V _ _ π hi hs W₁ _ _ P₁ hi₁ hs₁
    W _ _ P horbit X hX ψF ψE νF νE
  let p := residueChar F
  let : Fact p.Prime := ⟨residueChar_prime F⟩
  let : Algebra (Padic p) F := padicAlgebra F
  let : FiniteDimensional (Padic p) F := finiteDimensional F
  let K := padicField F
  let T := topologicalData F
  let : Algebra (Padic p) E := Algebra.compHom E (algebraMap (Padic p) F)
  let : IsScalarTower (Padic p) F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional (Padic p) E := FiniteDimensional.trans (Padic p) F E
  let L := PadicField.ofField (p := p) E
  let : TopologicalSpace K.Carrier := T.topology
  let : Algebra K.Carrier E := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier E := (inferInstance : IsScalarTower (Padic p) F E)
  let : FiniteDimensional K.Carrier E := (inferInstance : FiniteDimensional F E)
  let S : L.TopologicalData := suppliedPadicExtension T E
    (IsModuleTopology.continuous_of_linearMap (Algebra.linearMap F E))
  let : TopologicalSpace L.Carrier := S.topology
  let : Algebra K.Carrier L.Carrier := (inferInstance : Algebra F E)
  let : IsScalarTower (Padic p) K.Carrier L.Carrier := (inferInstance : IsScalarTower (Padic p) F E)
  let : IsModuleTopology K.Carrier L.Carrier := (inferInstance : IsModuleTopology F E)
  let μF : LocalFactor.PadicAbelian.SelfDualHaar T ψF := ⟨νF.val, νF.property⟩
  let μE : LocalFactor.PadicAbelian.SelfDualHaar S ψE := ⟨νE.val, νE.property⟩
  exact cuspidalSigmaLiftPadicEpsilonFactors p K L T S σ k s k₁ hr π hi hs P₁ hi₁ hs₁
    P horbit X hX ψF ψE μF μE

private theorem exists_conductorZero_character (F : Type u) [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] :
    ∃ ψ : UnitaryAdditiveCharacter F, (LocalFieldData.ofInstances F).additiveConductor ψ = 0 := by
  let K := padicField F
  let T := topologicalData F
  let : TopologicalSpace K.Carrier := T.topology
  let : ValuativeRel K.Carrier := T.valuativeRel
  let : IsNonarchimedeanLocalField K.Carrier := T.localField
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists K T
  let π₀ := uniformizerUnit T
  let b := π₀ ^ (-T.additiveConductor ψ)
  refine ⟨ψ.scale b, ?_⟩
  change T.toLocalFieldData.additiveConductor (ψ.scale b) = 0
  rw [T.toLocalFieldData_additiveConductor, T.additiveConductor_scale]
  simp only [b, π₀, Units.val_zpow_eq_zpow_val, T.ord_zpow, uniformizerUnit_ord]
  ring

private theorem nonempty_selfDualHaar (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (ψ : UnitaryAdditiveCharacter K) :
    Nonempty (AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances K) ψ) := by
  obtain ⟨_, h⟩ := AllField.HarmonicAnalysis.padicSelfDualMeasureExists K (LocalFieldData.ofInstances K)
  obtain ⟨μ, hμ⟩ := h ψ
  exact ⟨⟨μ, hμ⟩⟩

/-- Supply the trace character of the conductor reduction, the self-dual Haar
measures and every same-field factor certificate. The cross-field comparison
is not asserted. -/
def CuspidalSigmaLiftTraceEpsilonFactorsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F]
    (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E] [FiniteDimensional F E]
    (σ : E ≃ₐ[F] E) (k s k₁ : ℕ) (h : s * (k₁ + 1) = k + 1)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (k + 1) F) V),
    π.IsIrreducible → GeneralLinear.IsSupercuspidal π →
    ∀ {W₁ : Type uW} [AddCommGroup W₁] [Module ℂ W₁]
      (P₁ : Representation ℂ (GeneralLinear (k₁ + 1) E) W₁),
    P₁.IsIrreducible → GeneralLinear.IsSupercuspidal P₁ →
    ∀ {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (P : Representation ℂ (GeneralLinear (k + 1) E) W),
    Nonempty (P.Equiv ((sigmaOrbitProduct σ s (Nat.succ_pos k₁) P₁).comp
      (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom)) →
    ∀ (X : Finset (Fˣ →* ℂˣ)), (∀ κ ∈ X, IsNormTrivial E κ) →
    ∃ (ψF : UnitaryAdditiveCharacter F)
      (νF : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances F) ψF)
      (νE : AllField.LocalFactor.PadicAbelian.SelfDualHaar (LocalFieldData.ofInstances E)
        (ψF.tracePullback (E := E)))
      (aF : (Fˣ →* ℂˣ) → ℕ) (aOrbit : Fin s → ℕ)
      (eF : (Fˣ →* ℂˣ) → ℂˣ × ℤ) (eOrbit : Fin s → ℂˣ × ℤ) (eP : ℂˣ × ℤ),
      let ψE : UnitaryAdditiveCharacter E := ψF.tracePullback
      (LocalFieldData.ofInstances F).additiveConductor ψF = 0 ∧
      (∀ κ ∈ X, IsStandardEpsilonConductor ψF νF.val
        (twist (κ.comp GeneralLinear.determinant) π) (aF κ) (eF κ)) ∧
      (∀ i : Fin s, IsStandardEpsilonConductor ψE νE.val
        (P₁.comp (entrywiseAut (σ ^ (i : ℕ)) (k₁ + 1)).toMonoidHom) (aOrbit i) (eOrbit i)) ∧
      OrbitProductEpsilonMultiplicativity ψE νE.val P eOrbit eP

set_option maxHeartbeats 400000 in
theorem cuspidalSigmaLiftTraceEpsilonFactors :
    CuspidalSigmaLiftTraceEpsilonFactorsStatement.{u, v, uV, uW} := by
  intro F _ _ _ _ _ E _ _ _ _ _ _ _ σ k s k₁ hr V _ _ π hi hs W₁ _ _ P₁ hi₁ hs₁
    W _ _ P horbit X hX
  obtain ⟨ψF, hψF⟩ := exists_conductorZero_character F
  let ψE : UnitaryAdditiveCharacter E := ψF.tracePullback
  obtain ⟨νF⟩ := nonempty_selfDualHaar F ψF
  obtain ⟨νE⟩ := nonempty_selfDualHaar E ψE
  obtain ⟨aF, aOrbit, eF, eOrbit, eP, hF, hOrbit, hprod⟩ :=
    cuspidalSigmaLiftCharZeroEpsilonFactors F E σ k s k₁ hr π hi hs P₁ hi₁ hs₁
      P horbit X hX ψF ψE νF νE
  exact ⟨ψF, νF, νE, aF, aOrbit, eF, eOrbit, eP, hψF, hF, hOrbit, hprod⟩

end Langlands.BaseChange
