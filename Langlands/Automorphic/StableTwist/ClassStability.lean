import Langlands.Representation.RankinSelberg.StableTwist.JPSSStability
import Langlands.Correspondence.AutomorphicActualGamma
import Langlands.Correspondence.AutomorphicGammaTransfer
import Langlands.Global.Factors.CuspidalPairFiniteLayer
import Langlands.Representation.RankinSelberg.GenericLanglandsPairEpsilonFactorComparisonProof
import Langlands.LocalFactor.Harmonic.DualityProof
import Langlands.Representation.Whittaker.Transport

/-!
# Highly ramified stability of class pair gamma factors
-/

noncomputable section

namespace Langlands.Automorphic.StableTwist

open Langlands.Correspondence

universe u

variable {p : ℕ} [Fact p.Prime]

local instance classStabilityTopology (K : PadicField.{u} p) : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance classStabilityGLTopology (K : PadicField.{u} p) (n : ℕ) :
    TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n

local instance classStabilityGLTopologicalGroup (K : PadicField.{u} p) (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopologicalGroup n

/-- A self-dual Haar measure for `ψ` is unique. -/
theorem selfDualHaar_val_eq (K : PadicField.{u} p) (ψ : NontrivialAdditiveCharacter K)
    (ν ν' : LocalFactor.PadicAbelian.SelfDualHaar K.canonicalTopologicalData ψ) :
    ν.val = ν'.val := by
  obtain ⟨_, hd⟩ := LocalFactors.padicFourierDuality p K K.canonicalTopologicalData
  exact (hd ψ.toAddChar ψ.continuous_toFun ψ.nontrivial).2.2.1 ν.val ν'.val ν.property
    ν'.property

/-- Every pair of classes has a class pair gamma factor for every self-dual measure. -/
theorem exists_isAutomorphicPairGammaFactor (K : PadicField.{u} p)
    (ψ : NontrivialAdditiveCharacter K) {ν : LocalAdditiveHaarMeasure K}
    (hν : IsSelfDualMeasure K ψ ν) {r t : ℕ}
    (π : AutomorphicClass.{u, u} K r.succPNat) (π' : AutomorphicClass.{u, u} K t.succPNat) :
    ∃ G : RatFunc ℂ, IsAutomorphicPairGammaFactor K ψ ν π π' G := by
  have hd := (isSmoothDual_iff_eq_contragredient K π _).mpr rfl
  have hd' := (isSmoothDual_iff_eq_contragredient K π' _).mpr rfl
  obtain ⟨P, hP⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairLPolynomial
    K ψ hν π π'
  obtain ⟨Pd, hPd⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairLPolynomial
    K ψ hν (SmoothDualClass.contragredient
      (GeneralLinear.compactOpen_cofinal K K.canonicalTopologicalData r.succPNat) π)
    (SmoothDualClass.contragredient
      (GeneralLinear.compactOpen_cofinal K K.canonicalTopologicalData t.succPNat) π')
  obtain ⟨e, he⟩ := Global.CuspidalPairFunctionalEquation.exists_isAutomorphicPairEpsilonFactor
    K ψ hν π π'
  exact ⟨_, (automorphicPairGammaFactor hd hd' hP hPd he).property⟩

/-- **Class-level two-factor stability.** Let `A₁, A₂` (rank `r + 1`) and `B₁, B₂`
(rank `t + 1`) be generic objects, with equal central characters in each rank. For
every quasi-character `χ` of large conductor, any gamma factor of
`((A₂ ⊗ χ), B₂)` is one of `((A₁ ⊗ χ), B₁)`, for every self-dual measure. -/
theorem classPairGammaStability
    (hR1 : RankinSelberg.PairGammaTwistExchangeStatement.{u, u, u})
    (K : PadicField.{u} p) (ψ : NontrivialAdditiveCharacter K) {r t : ℕ}
    (A₁ A₂ : AutomorphicObject.{u, u} K r.succPNat)
    (B₁ B₂ : AutomorphicObject.{u, u} K t.succPNat)
    (hA₁ : letI := K.canonicalTopologicalData.topology
      letI := K.canonicalGeneralLinearTopology (r + 1)
      Whittaker.IsGeneric ψ r A₁.obj.representation)
    (hA₂ : letI := K.canonicalTopologicalData.topology
      letI := K.canonicalGeneralLinearTopology (r + 1)
      Whittaker.IsGeneric ψ r A₂.obj.representation)
    (hB₁ : letI := K.canonicalTopologicalData.topology
      letI := K.canonicalGeneralLinearTopology (t + 1)
      Whittaker.IsGeneric ψ t B₁.obj.representation)
    (hB₂ : letI := K.canonicalTopologicalData.topology
      letI := K.canonicalGeneralLinearTopology (t + 1)
      Whittaker.IsGeneric ψ t B₂.obj.representation)
    (hA : RankinSelberg.SameGLCentralCharacter K A₁.obj.representation A₂.obj.representation)
    (hB : RankinSelberg.SameGLCentralCharacter K B₁.obj.representation B₂.obj.representation) :
    ∃ N : ℕ, ∀ χ : QuasiCharacter K, N ≤ K.canonicalTopologicalData.multiplicativeConductor χ →
      ∀ π₁χ π₂χ : AutomorphicClass.{u, u} K r.succPNat,
        IsCharacterTwist K χ (automorphicClassOf K A₁) π₁χ →
        IsCharacterTwist K χ (automorphicClassOf K A₂) π₂χ →
        ∀ ν : LocalAdditiveHaarMeasure K, IsSelfDualMeasure K ψ ν → ∀ G : RatFunc ℂ,
          IsAutomorphicPairGammaFactor K ψ ν π₂χ (automorphicClassOf K B₂) G →
          IsAutomorphicPairGammaFactor K ψ ν π₁χ (automorphicClassOf K B₁) G := by
  let T := K.canonicalTopologicalData
  obtain ⟨ν₀⟩ := RankinSelberg.HighlyRamified.nonempty_selfDualHaar K ψ
  obtain ⟨N, hN⟩ := RankinSelberg.StableTwist.pairGammaStability hR1 K ψ ν₀
    A₁.obj.representation A₂.obj.representation B₁.obj.representation B₂.obj.representation
    hA₁ hA₂ hB₁ hB₂ hA hB
  refine ⟨N, fun χ hχ π₁χ π₂χ h₁ h₂ ν hν G hG => ?_⟩
  have hνeq : ν = ν₀.val := selfDualHaar_val_eq K ψ ⟨ν, hν⟩ ν₀
  subst hνeq
  obtain ⟨A₁', C₁, hA₁', rfl, ⟨e₁⟩⟩ := h₁
  obtain ⟨A₂', C₂, hA₂', rfl, ⟨e₂⟩⟩ := h₂
  obtain ⟨f₁⟩ := (automorphicClassOf_eq_iff K A₁' A₁).mp hA₁'
  obtain ⟨f₂⟩ := (automorphicClassOf_eq_iff K A₂' A₂).mp hA₂'
  let g₁ := (Langlands.twistEquiv _ f₁.symm).trans e₁
  let g₂ := (Langlands.twistEquiv _ f₂.symm).trans e₂
  have hC₁ : Whittaker.IsGeneric ψ r C₁.obj.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r g₁).mp
      ((RankinSelberg.isGeneric_quasicharacter_twist_iff T ψ χ _).mpr hA₁)
  have hC₂ : Whittaker.IsGeneric ψ r C₂.obj.representation :=
    (Whittaker.isGeneric_iff_of_equiv ψ r g₂).mp
      ((RankinSelberg.isGeneric_quasicharacter_twist_iff T ψ χ _).mpr hA₂)
  have h₂' := hG.isPadicSymmetricGammaFactor_of_generic (ν := ν₀)
    RankinSelberg.genericLanglandsPairEpsilonFactorComparison C₂ B₂ hC₂ hB₂
  have h₂'' := (RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv g₂
    (Representation.Equiv.refl _)).mpr h₂'
  obtain ⟨G₁, hG₁⟩ := exists_isAutomorphicPairGammaFactor K ψ hν (automorphicClassOf K C₁)
    (automorphicClassOf K B₁)
  have h₁' := hG₁.isPadicSymmetricGammaFactor_of_generic (ν := ν₀)
    RankinSelberg.genericLanglandsPairEpsilonFactorComparison C₁ B₁ hC₁ hB₁
  have h₁'' := (RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv g₁
    (Representation.Equiv.refl _)).mpr h₁'
  rw [← hN χ hχ G₁ G h₁'' h₂'']
  exact hG₁

end Langlands.Automorphic.StableTwist
