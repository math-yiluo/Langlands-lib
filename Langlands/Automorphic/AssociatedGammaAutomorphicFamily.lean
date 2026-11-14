import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Automorphic.AssociatedGammaTwistedPairData
import Langlands.Automorphic.AssociatedGammaEulerFamily
import Langlands.Automorphic.AssociatedGammaCuspidalEquation
import Langlands.Global.Factors.CuspidalPairFunctionalEquationStatement
import Langlands.Automorphic.CuspidalContragredientLocalCompatibilityProof

/-!
# The automorphic Hecke Euler family of a cuspidal pair

For actual cuspidal realizations `T`, `T'` with contragredients `Td`, `Td'`, presentations
with irreducible admissible components, chosen finite additive components and self-dual
measures, and archimedean data, the local factors at a Hecke character `χ` are: the
archimedean factors of the pair, lumped at one infinite place and independent of `χ`; and at
a finite place `z` the twisted pair data of `(π_z ⊗ χ_z, π'_z)`. Given the completed global
Rankin–Selberg equation, these factors satisfy the analytic engine inputs for every
character trivial at infinity, through the global twist `T ⊗ χ`.
-/

noncomputable section

set_option autoImplicit false

open scoped Classical

universe u uQ

namespace Langlands.Global.CuspidalPairFunctionalEquation

open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
open Langlands.Global.CompletionPadic Langlands.Global.HeckeFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.ClassField.Global.RelativeWeilGroup

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Local classes of a contragredient pair of presentations are smooth duals. -/
theorem isSmoothDual_localClass {r : ℕ} {T Td : Automorphic.CuspidalOperatorRealization F r}
    (hTd : Td.realization.IsContragredientOf T.realization)
    (P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T)
    (Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td)
    (h : HasIrreducibleAdmissibleComponents P) (hd : HasIrreducibleAdmissibleComponents Pd)
    (v : FinitePlace F) :
    Correspondence.IsSmoothDual (padicField v) (localClass P h v) (localClass Pd hd v) := by
  obtain ⟨e⟩ := Automorphic.cuspidalContragredientLocalCompatibility.{u, uQ, uQ} F r T Td hTd
    P Pd v (h v).1 (h v).2 (hd v).1 (hd v).2
  exact ⟨_, _, rfl, rfl, ⟨e.symm⟩⟩

omit [CompactSpace (AdeleQuotient F)] in
/-- The inverse of a character trivial at infinity is trivial at infinity. -/
theorem _root_.Langlands.Global.HeckeCharacter.hasPrescribedInfinityComponent_one_inv
    {χ : HeckeCharacter F} (hχ : χ.HasPrescribedInfinityComponent 1) :
    χ⁻¹.HasPrescribedInfinityComponent 1 := by
  refine DFunLike.ext _ _ fun x => ?_
  have hx : χ.atInfinity x = 1 := by rw [hχ]; rfl
  change (χ.atInfinity x)⁻¹ = 1
  rw [hx, inv_one]

/-- Data of a cuspidal pair used to build its automorphic Hecke Euler family. -/
structure AutomorphicTwistSetup (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (r t : ℕ) where
  T : Automorphic.CuspidalOperatorRealization F r
  T' : Automorphic.CuspidalOperatorRealization F t
  Td : Automorphic.CuspidalOperatorRealization F r
  Td' : Automorphic.CuspidalOperatorRealization F t
  hTd : Td.realization.IsContragredientOf T.realization
  hTd' : Td'.realization.IsContragredientOf T'.realization
  P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T
  P' : Automorphic.CuspidalSpectralPresentation.{u, uQ} T'
  Pd : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td
  Pd' : Automorphic.CuspidalSpectralPresentation.{u, uQ} Td'
  h : HasIrreducibleAdmissibleComponents P
  h' : HasIrreducibleAdmissibleComponents P'
  hd : HasIrreducibleAdmissibleComponents Pd
  hd' : HasIrreducibleAdmissibleComponents Pd'
  additive : ∀ v : FinitePlace F, Correspondence.NontrivialAdditiveCharacter (padicField v)
  additive_spec : ∀ v, IsCanonicalFiniteAdditiveComponent ψ v (additive v)
  measure : ∀ v : FinitePlace F, Correspondence.LocalAdditiveHaarMeasure (padicField v)
  measure_spec : ∀ v, Correspondence.IsSelfDualMeasure (padicField v) (additive v) (measure v)
  aR : {v : NumberField.InfinitePlace F // v.IsReal} → ℝˣ
  aR_spec : ∀ v, IsRealAdditiveComponent ψ v.1 v.2 (aR v)
  aC : {v : NumberField.InfinitePlace F // v.IsComplex} → ℂˣ
  aC_spec : ∀ v, IsComplexAdditiveComponent ψ v.1 v.2 (aC v)
  dR : {v : NumberField.InfinitePlace F // v.IsReal} → List RealBlock
  dR' : {v : NumberField.InfinitePlace F // v.IsReal} → List RealBlock
  dRd : {v : NumberField.InfinitePlace F // v.IsReal} → List RealBlock
  dRd' : {v : NumberField.InfinitePlace F // v.IsReal} → List RealBlock
  dR_spec : ∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter T.realization v (dR v)
  dR'_spec : ∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter T'.realization v (dR' v)
  dRd_spec : ∀ v, Automorphic.OperatorRealization.HasRealPlaceParameter Td.realization v (dRd v)
  dRd'_spec : ∀ v,
    Automorphic.OperatorRealization.HasRealPlaceParameter Td'.realization v (dRd' v)
  dC : {v : NumberField.InfinitePlace F // v.IsComplex} → List ComplexCharacterData
  dC' : {v : NumberField.InfinitePlace F // v.IsComplex} → List ComplexCharacterData
  dCd : {v : NumberField.InfinitePlace F // v.IsComplex} → List ComplexCharacterData
  dCd' : {v : NumberField.InfinitePlace F // v.IsComplex} → List ComplexCharacterData
  dC_spec : ∀ v,
    Automorphic.OperatorRealization.HasComplexPlaceParameter T.realization v (dC v)
  dC'_spec : ∀ v,
    Automorphic.OperatorRealization.HasComplexPlaceParameter T'.realization v (dC' v)
  dCd_spec : ∀ v,
    Automorphic.OperatorRealization.HasComplexPlaceParameter Td.realization v (dCd v)
  dCd'_spec : ∀ v,
    Automorphic.OperatorRealization.HasComplexPlaceParameter Td'.realization v (dCd' v)
  w₀ : NumberField.InfinitePlace F

namespace AutomorphicTwistSetup

variable {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
  (D : AutomorphicTwistSetup.{u, uQ} ψ r t)

/-- The archimedean L-factor of the pair. -/
def infiniteL (s : ℂ) : ℂ :=
  (∏ v, ((realPairLFactor (D.dR v) (D.dR' v)).denominator s)⁻¹) *
    ∏ v, ((complexPairLFactor (D.dC v) (D.dC' v)).denominator s)⁻¹

/-- The archimedean L-factor of the contragredient pair. -/
def dualInfiniteL (s : ℂ) : ℂ :=
  (∏ v, ((realPairLFactor (D.dRd v) (D.dRd' v)).denominator s)⁻¹) *
    ∏ v, ((complexPairLFactor (D.dCd v) (D.dCd' v)).denominator s)⁻¹

/-- The archimedean epsilon factor of the pair. -/
def infiniteEpsilon (s : ℂ) : ℂ :=
  (∏ v, (realPairEpsilon (D.dR v) (D.dR' v) (D.aR v) (NNReal.sqrt ‖((D.aR v : ℝ))‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr (D.aR v).ne_zero)) s : ℂ)) *
    ∏ v, (complexPairEpsilon (D.dC v) (D.dC' v) (D.aC v) ‖((D.aC v : ℂ))‖₊
      (nnnorm_pos.mpr (D.aC v).ne_zero) s : ℂ)

/-- The twisted pair data at a finite place, depending on `χ` only through `χ_z`. -/
def finiteData (χ : HeckeCharacter F) (z : FinitePlace F) :
    Polynomial ℂ × Polynomial ℂ × (ℂˣ × ℤ) :=
  Correspondence.twistedPairData (D.additive z) (D.measure z) (localClass D.P D.h z)
    (localClass D.P' D.h' z) (quasicharacterBase z (χ.finiteComponent z))

/-- The local factors of the automorphic Hecke Euler family. -/
def localFactors (χ : HeckeCharacter F) : AllPlaces F → LocalFactors :=
  Sum.elim (lumpedArch D.w₀ D.infiniteL D.dualInfiniteL D.infiniteEpsilon)
    fun z => pairDataFactors (residueCardinality z) (D.finiteData χ z)

/-- The archimedean factors do not depend on the character. -/
theorem localFactors_inl (χ : HeckeCharacter F) (w : NumberField.InfinitePlace F) :
    D.localFactors χ (.inl w) = D.localFactors 1 (.inl w) := rfl

/-- At a finite place the factor depends only on the local component. -/
theorem localFactors_inr_of_finiteComponent_eq {χ χ' : HeckeCharacter F} {z : FinitePlace F}
    (h : χ.finiteComponent z = χ'.finiteComponent z) :
    D.localFactors χ (.inr z) = D.localFactors χ' (.inr z) := by
  simp only [localFactors, Sum.elim_inr, finiteData, h]

/-- The twisted finite data are the factors of the twisted presentation. -/
theorem finiteData_specs (χ : HeckeCharacter F) (z : FinitePlace F) :
    let h₁ := D.P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ D.h
    let hd₁ := D.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ⁻¹ D.hd
    Correspondence.IsAutomorphicPairLPolynomial (padicField z) (D.additive z) (D.measure z)
        (localClass (D.P.heckeDeterminantTwist χ) h₁ z) (localClass D.P' D.h' z)
        (D.finiteData χ z).1 ∧
      Correspondence.IsAutomorphicPairLPolynomial (padicField z) (D.additive z) (D.measure z)
        (localClass (D.Pd.heckeDeterminantTwist χ⁻¹) hd₁ z) (localClass D.Pd' D.hd' z)
        (D.finiteData χ z).2.1 ∧
      Correspondence.IsAutomorphicPairEpsilonFactor (padicField z) (D.additive z) (D.measure z)
        (localClass (D.P.heckeDeterminantTwist χ) h₁ z) (localClass D.P' D.h' z)
        (D.finiteData χ z).2.2 := by
  intro h₁ hd₁
  have hc : (D.Td.heckeDeterminantTwist χ⁻¹).realization.IsContragredientOf
      (D.T.heckeDeterminantTwist χ).realization :=
    Automorphic.OperatorRealization.IsContragredientOf.heckeDeterminantTwist_inv D.hTd χ
  have htw := D.P.isCharacterTwist_heckeDeterminantTwist_padicClass χ z (D.h z).1 (D.h z).2
    (h₁ z).1 (h₁ z).2
  exact (Correspondence.twistedPairData_spec (D.additive z) (D.measure_spec z) _ _ _).specs htw
    (isSmoothDual_localClass hc _ _ h₁ hd₁ z) (isSmoothDual_localClass D.hTd' _ _ D.h' D.hd' z)

/-- The finite factor choice of the twisted pair built from the twisted finite data. -/
def twistedChoice (χ : HeckeCharacter F) :
    FinitePairFactorChoice ψ (D.P.heckeDeterminantTwist χ) D.P'
      (D.Pd.heckeDeterminantTwist χ⁻¹) D.Pd'
      (D.P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ D.h) D.h'
      (D.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ⁻¹ D.hd) D.hd' where
  additive := D.additive
  additive_spec := D.additive_spec
  measure := D.measure
  measure_spec := D.measure_spec
  lPolynomial z := (D.finiteData χ z).1
  lPolynomial_spec z := (D.finiteData_specs χ z).1
  dualLPolynomial z := (D.finiteData χ z).2.1
  dualLPolynomial_spec z := (D.finiteData_specs χ z).2.1
  epsilon z := (D.finiteData χ z).2.2
  epsilon_spec z := (D.finiteData_specs χ z).2.2

/-- **Engine inputs.** Given the completed global Rankin–Selberg equation, for every Hecke
character trivial at infinity there is a finite set `S` such that the family satisfies the
engine inputs at every `B ⊇ S`, and the twisted factor choice is unramified outside `S`. -/
theorem exists_engineInputs
    (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u, uQ})
    (hψ : ∃ x : Adeles F, ψ x ≠ 1) (hdiag : ∀ x : F, ψ (diagonal F x) = 1)
    (χ : HeckeCharacter F) (hχ : χ.HasPrescribedInfinityComponent 1) :
    ∃ S : Finset (FinitePlace F), (D.twistedChoice χ).IsUnramifiedOutside S ∧
      ∀ B : Finset (FinitePlace F), S ⊆ B →
        HeckeEulerFamily.HasEngineInputs (D.localFactors χ) B := by
  have hχi := HeckeCharacter.hasPrescribedInfinityComponent_one_inv hχ
  have hc : (D.Td.heckeDeterminantTwist χ⁻¹).realization.IsContragredientOf
      (D.T.heckeDeterminantTwist χ).realization :=
    Automorphic.OperatorRealization.IsContragredientOf.heckeDeterminantTwist_inv D.hTd χ
  obtain ⟨-, S, -, -, -, -, -, hall⟩ := hFE F ψ hψ hdiag r t
    (D.T.heckeDeterminantTwist χ) (D.Td.heckeDeterminantTwist χ⁻¹) D.T' D.Td' hc D.hTd'
    (D.P.heckeDeterminantTwist χ) D.P' (D.Pd.heckeDeterminantTwist χ⁻¹) D.Pd'
    (D.P.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ D.h) D.h'
    (D.Pd.heckeDeterminantTwist_hasIrreducibleAdmissibleComponents χ⁻¹ D.hd) D.hd'
  obtain ⟨hunr, hC⟩ := hall (D.twistedChoice χ)
  refine ⟨S, hunr, fun B hSB => ?_⟩
  have hC' := hC D.aR D.aR_spec D.aC D.aC_spec D.dR D.dR' D.dRd D.dRd'
    (fun v => Automorphic.OperatorRealization.HasRealPlaceParameter.heckeDeterminantTwist _ hχ
      (D.dR_spec v)) D.dR'_spec
    (fun v => Automorphic.OperatorRealization.HasRealPlaceParameter.heckeDeterminantTwist _ hχi
      (D.dRd_spec v)) D.dRd'_spec D.dC D.dC' D.dCd D.dCd'
    (fun v => Automorphic.OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist _
      hχ (D.dC_spec v)) D.dC'_spec
    (fun v => Automorphic.OperatorRealization.HasComplexPlaceParameter.heckeDeterminantTwist _
      hχi (D.dCd_spec v)) D.dCd'_spec
  obtain ⟨σ', Lp, Lpd, hA, hE, hF⟩ := (D.twistedChoice χ).exists_engineInputs_cuspidal S B hSB
    hunr D.aR D.aC D.dR D.dR' D.dRd D.dRd' D.dC D.dC' D.dCd D.dCd' hC' D.w₀
  exact ⟨σ', Lp, Lpd, hA, hE, hF⟩

end AutomorphicTwistSetup

end Langlands.Global.CuspidalPairFunctionalEquation
