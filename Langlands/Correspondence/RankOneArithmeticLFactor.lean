import Langlands.Correspondence.RankOneArithmeticEuler
import Langlands.Correspondence.AssemblyDeterminant
import Langlands.Correspondence.RankOneReciprocityBijection
import Langlands.Correspondence.ArithmeticFactors
import Langlands.LocalFactor.Abelian.Padic

/-! # Actual rank-one arithmetic pair L-factors -/

noncomputable section

universe uF uP uK uG uV uW uX uY

open Polynomial

namespace Langlands.WeilDeligneRepresentation

/-- Tensor equivalences allow independent source and target carrier universes. -/
def tensorCongr {K : Type uK} [Field K] {G : Type uG} [Group G] {ν : G →* Kˣ}
    {A : WeilDeligneRepresentation.{uK, uG, uV} K G ν}
    {B : WeilDeligneRepresentation.{uK, uG, uW} K G ν}
    {C : WeilDeligneRepresentation.{uK, uG, uX} K G ν}
    {D : WeilDeligneRepresentation.{uK, uG, uY} K G ν}
    (e : Equiv A C) (f : Equiv B D) :
    Equiv (tensor A B) (tensor C D) where
  representationEquiv := {
    toLinearEquiv := TensorProduct.congr e.representationEquiv.toLinearEquiv
      f.representationEquiv.toLinearEquiv
    isIntertwining' := (tensorMap e.toHom f.toHom).intertwiner.isIntertwining' }
  comm_monodromy := (tensorMap e.toHom f.toHom).comm_monodromy

end Langlands.WeilDeligneRepresentation

namespace Langlands.Correspondence

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rankOneArithmeticFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The conductor and normalized-absolute-value definitions of unramifiedness agree. -/
theorem isUnramifiedQuasicharacter_iff_isUnramifiedCharacter (χ : QuasiCharacter F) :
    F.canonicalTopologicalData.IsUnramifiedQuasicharacter χ ↔
      F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom := by
  rw [PadicField.TopologicalData.IsUnramifiedCharacter,
    ← F.canonicalTopologicalData.ker_ordUnits]
  constructor
  · intro h a ha
    change F.canonicalTopologicalData.ord (a : F.Carrier) = 0 at ha
    exact h a ((F.canonicalTopologicalData.normalizedAbs_eq_one_iff_discreteValuation _).mp
      ((F.canonicalTopologicalData.ord_eq_zero_iff_normalizedAbs a).mp ha))
  · intro h a ha
    apply h
    change F.canonicalTopologicalData.ord (a : F.Carrier) = 0
    exact (F.canonicalTopologicalData.ord_eq_zero_iff_normalizedAbs a).mpr
      ((F.canonicalTopologicalData.normalizedAbs_eq_one_iff_discreteValuation _).mpr ha)

/-- Under supplied geometric reciprocity, inertia triviality detects unramified field characters. -/
theorem weilCharacter_trivial_on_inertia_iff {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (χ : QuasiCharacter F) :
    (∀ w ∈ Weil.Local.localInertia F, weilCharacter F e χ w = 1) ↔
      F.canonicalTopologicalData.IsUnramifiedCharacter χ.toMonoidHom := by
  constructor
  · intro h
    rw [PadicField.TopologicalData.IsUnramifiedCharacter,
      ← F.canonicalTopologicalData.ker_ordUnits]
    intro a ha
    obtain ⟨w, rfl⟩ := AssemblyDeterminant.reciprocityHom_surjective F e a
    have hw : w ∈ Weil.Local.localInertia F := by
      change Weil.Local.localDegreeInt F w = 0
      rw [← ord_reciprocityHom F he]
      exact ha
    exact h w hw
  · intro h w hw
    exact weilCharacter_eq_one_of_mem_localInertia F he h hw

/-- The actual scalar Weil Euler polynomial equals the field-character Euler denominator. -/
theorem eulerPolynomial_scalarWeilCharacter {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (χ : QuasiCharacter F) :
    LocalFactor.WeilDeligne.eulerPolynomial
      (WeilDeligneRepresentation.zeroMonodromy (Weil.Local.localNormCharacter F).toMonoidHom
        (FiniteRepresentation.of (Langlands.characterRepresentation (weilCharacter F e χ))))
      (Weil.Local.localInertia F) (Weil.Local.localGeometricFrobenius F) =
      LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ := by
  classical
  by_cases hc : F.canonicalTopologicalData.multiplicativeConductor χ = 0
  · have hχ := (isUnramifiedQuasicharacter_iff_isUnramifiedCharacter F χ).mp
      ((F.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff χ).mp hc)
    rw [LocalFactor.WeilDeligne.eulerPolynomial_scalarCharacter_of_unramified _ _ _
      ((weilCharacter_trivial_on_inertia_iff F he χ).mpr hχ),
      weilCharacter_localGeometricFrobenius he hχ,
      LocalFactor.PadicAbelian.lPolynomial, ite_eq_left hc]
  · have hram : ∃ w ∈ Weil.Local.localInertia F, weilCharacter F e χ w ≠ 1 := by
      by_contra! h
      apply hc
      apply (F.canonicalTopologicalData.multiplicativeConductor_eq_zero_iff χ).mpr
      exact (isUnramifiedQuasicharacter_iff_isUnramifiedCharacter F χ).mpr
        ((weilCharacter_trivial_on_inertia_iff F he χ).mp h)
    rw [LocalFactor.WeilDeligne.eulerPolynomial_scalarCharacter_of_ramified _ _ _ hram,
      LocalFactor.PadicAbelian.lPolynomial, ite_eq_right hc]

/-- The actual scalar Weil L-factor equals the field-character rational L-factor. -/
theorem rationalLFactor_scalarWeilCharacter {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (χ : QuasiCharacter F) :
    LocalFactor.WeilDeligne.rationalLFactor
      (WeilDeligneRepresentation.zeroMonodromy (Weil.Local.localNormCharacter F).toMonoidHom
        (FiniteRepresentation.of (Langlands.characterRepresentation (weilCharacter F e χ))))
      (Weil.Local.localInertia F) (Weil.Local.localGeometricFrobenius F) =
      LocalFactor.PadicAbelian.rationalLFactor F.canonicalTopologicalData χ := by
  change (algebraMap ℂ[X] (RatFunc ℂ) (LocalFactor.WeilDeligne.eulerPolynomial _ _ _))⁻¹ =
    (algebraMap ℂ[X] (RatFunc ℂ)
      (LocalFactor.PadicAbelian.lPolynomial F.canonicalTopologicalData χ))⁻¹
  rw [eulerPolynomial_scalarWeilCharacter F he χ]

/-- The arithmetic pair L-factor of actual rank-one character classes is the
field-character L-factor of their product, including ramified products. -/
theorem arithmeticPairLFactor_rankOneWeilCharacterClass {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) (χ η : QuasiCharacter F) :
    arithmeticPairLFactor F
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e χ))
      (weilPairClass F (rankOneWeilCharacterClass.{uF, uP} F e η)) =
      LocalFactor.PadicAbelian.rationalLFactor F.canonicalTopologicalData (χ * η) := by
  let ν := (Weil.Local.localNormCharacter F).toMonoidHom
  let ψ := weilCharacter F e χ
  let φ := weilCharacter F e η
  change LocalFactor.WeilDeligne.rationalLFactor
    (WeilDeligneRepresentation.tensor
      (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.characterLine.{uF, uP} ψ))
      (WeilDeligneRepresentation.zeroMonodromy ν (FiniteRepresentation.characterLine.{uF, uP} φ)))
    (Weil.Local.localInertia F) (Weil.Local.localGeometricFrobenius F) = _
  let f := (WeilDeligneRepresentation.tensorCongr
    (WeilDeligneRepresentation.zeroMonodromyCongr ν
      (FiniteRepresentation.characterLineEquiv.{uF, uP} ψ))
    (WeilDeligneRepresentation.zeroMonodromyCongr ν
      (FiniteRepresentation.characterLineEquiv.{uF, uP} φ))).trans
      (WeilDeligneRepresentation.scalarCharacterTensorEquiv ν ψ φ)
  rw [LocalFactor.WeilDeligne.rationalLFactor_eq_of_equiv
    (Weil.Local.localInertia F) f (Weil.Local.localGeometricFrobenius F)]
  have hmul : ψ * φ = weilCharacter F e (χ * η) := by
    ext w
    rfl
  rw [hmul]
  exact rationalLFactor_scalarWeilCharacter F he (χ * η)

/-- The pair formula depends only on the realized characters, not on their
chosen actual rank-one representatives. -/
theorem arithmeticPairLFactor_of_isRankOneWeilCharacter {e : ReciprocityCandidate F}
    (he : IsGeometricReciprocity F e) {χ η : QuasiCharacter F}
    {σ τ : IrreducibleWeilClass.{uF, uP} F 1}
    (hσ : IsRankOneWeilCharacter F (weilCharacter F e χ) σ)
    (hτ : IsRankOneWeilCharacter F (weilCharacter F e η) τ) :
    arithmeticPairLFactor F (weilPairClass F σ) (weilPairClass F τ) =
      LocalFactor.PadicAbelian.rationalLFactor F.canonicalTopologicalData (χ * η) := by
  rw [IsRankOneWeilCharacter.class_unique F hσ (rankOneWeilCharacterClass_spec F e χ),
    IsRankOneWeilCharacter.class_unique F hτ (rankOneWeilCharacterClass_spec F e η)]
  exact arithmeticPairLFactor_rankOneWeilCharacterClass F he χ η

end Langlands.Correspondence
