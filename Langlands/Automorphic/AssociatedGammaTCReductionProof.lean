import Langlands.Automorphic.AssociatedFactorTCReductionStatement
import Langlands.Automorphic.AssociatedGammaFinal
import Langlands.Automorphic.StableTwistGammaMatchProof

/-!
# Henniart's Théorème 2.3 over totally complex fields from the totally complex functional equation

A proof of `AssociatedGammaReductionTCStatement`: the completed global Rankin–Selberg
functional equation of cuspidal pairs over totally complex number fields implies Henniart's
Théorème 2.3 over totally complex number fields.

The proof is that of the published `associatedGamma_of_inputs`. That proof applies the
functional equation only at the base field `F` of the conclusion, through three published
auxiliary results. This module copies the four results with the hypothesis
`CuspidalPairGlobalFunctionalEquationTCStatement` in place of
`CuspidalPairGlobalFunctionalEquationStatement` and the instance
`[NumberField.IsTotallyComplex F]` added; the proofs are otherwise verbatim. The stable local
comparison is the proved Library theorem `stableTwistPairGammaMatchStatement`.
-/

noncomputable section

set_option autoImplicit false

/-! ## The engine inputs of the automorphic family -/

section EngineInputs

open scoped Classical

namespace Langlands.Global.CuspidalPairFunctionalEquation.AutomorphicTwistSetup

open Langlands.Global.FunctionalEquationComparison
open Langlands.Global.FunctionalEquationComparison.RelativeWeilEngine
open Langlands.Global.CompletionPadic Langlands.Global.HeckeFunctionalEquation
open Langlands.LocalFactor.Archimedean
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup

/-- **Engine inputs over a totally complex field.** The totally complex form of
`exists_engineInputs`: given the completed global Rankin–Selberg equation over totally complex
fields, over a totally complex field `F`, for every Hecke character trivial at infinity there
is a finite set `S` such that the family satisfies the engine inputs at every `B ⊇ S`, and the
twisted factor choice is unramified outside `S`. -/
theorem exists_engineInputs_tc.{u, uQ} {F : Type u} [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [CompactSpace (AdeleQuotient F)]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} {r t : ℕ}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t)
    (hFE : CuspidalPairGlobalFunctionalEquationTCStatement.{u, uQ})
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

end Langlands.Global.CuspidalPairFunctionalEquation.AutomorphicTwistSetup

end EngineInputs

/-! ## The common-twist analytic input -/

section CommonInputs

open scoped Classical

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

/-- **Common-twist analytic input over a totally complex field.** The totally complex form of
`commonTwistEulerInputs_families`. -/
theorem commonTwistEulerInputs_families_tc.{u, uQ, uV, uE}
    {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (hFE : CuspidalPairGlobalFunctionalEquationTCStatement.{u, uQ})
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (hψ : ∃ x : Adeles F, ψ x ≠ 1) (hdiag : ∀ x : F, ψ (diagonal F x) = 1)
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (hW : IsWeaklyAssociated S D.P.spectralSystem)
    (hW' : IsWeaklyAssociated S' D.P'.spectralSystem)
    (hWd : IsWeaklyAssociated S.dual D.Pd.spectralSystem)
    (hWd' : IsWeaklyAssociated S'.dual D.Pd'.spectralSystem)
    (T₀ : Finset (FinitePlace F)) (arch : NumberField.InfinitePlace F → LocalFactors)
    (hA : ∀ χ : HeckeCharacter F, χ.HasFiniteOrder → χ.HasPrescribedInfinityComponent 1 →
      ∀ B : Finset (FinitePlace F), T₀ ⊆ B → (∀ z ∉ B, χ.IsUnramifiedAt z) →
        HeckeEulerFamily.HasEngineInputs (A.localFactors arch χ) B)
    (T : Finset (FinitePlace F)) :
    CommonTwistEulerInputs F T (HeckeEulerFamily.ofLocalFactors D.localFactors)
      (HeckeEulerFamily.ofLocalFactors (A.localFactors arch)) := by
  apply HeckeEulerFamily.commonTwistEulerInputs_ofLocalFactors
  intro χ₁ χ₂ hf₁ hf₂ hi₁ hi₂
  obtain ⟨S₁, hU₁, hD₁⟩ := D.exists_engineInputs_tc hFE hψ hdiag χ₁ hi₁
  obtain ⟨S₂, hU₂, hD₂⟩ := D.exists_engineInputs_tc hFE hψ hdiag χ₂ hi₂
  obtain ⟨R₁, hR₁⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt F χ₁
  obtain ⟨R₂, hR₂⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt F χ₂
  obtain ⟨W₁, -, hW₁⟩ := exists_finset_isUnramifiedMatchAt hW
  obtain ⟨W₂, -, hW₂⟩ := exists_finset_isUnramifiedMatchAt hW'
  obtain ⟨W₃, -, hW₃⟩ := exists_finset_isUnramifiedMatchAt hWd
  obtain ⟨W₄, -, hW₄⟩ := exists_finset_isUnramifiedMatchAt hWd'
  let X : Finset (FinitePlace F) := D.P.exceptional ∪ D.P'.exceptional ∪ D.Pd.exceptional ∪
    D.Pd'.exceptional ∪ (D.P.heckeDeterminantTwist χ₁).exceptional ∪
    (D.P.heckeDeterminantTwist χ₂).exceptional ∪ (D.Pd.heckeDeterminantTwist χ₁⁻¹).exceptional ∪
    (D.Pd.heckeDeterminantTwist χ₂⁻¹).exceptional
  let B : Finset (FinitePlace F) := T ∪ T₀ ∪ S₁ ∪ S₂ ∪ R₁ ∪ R₂ ∪ W₁ ∪ W₂ ∪ W₃ ∪ W₄ ∪ X
  have hB : ∀ z ∉ B, z ∉ T ∧ z ∉ T₀ ∧ z ∉ S₁ ∧ z ∉ S₂ ∧ z ∉ R₁ ∧ z ∉ R₂ ∧ z ∉ W₁ ∧ z ∉ W₂ ∧
      z ∉ W₃ ∧ z ∉ W₄ ∧ z ∉ D.P.exceptional ∧ z ∉ D.P'.exceptional ∧
      z ∉ D.Pd.exceptional ∧ z ∉ D.Pd'.exceptional ∧
      z ∉ (D.P.heckeDeterminantTwist χ₁).exceptional ∧
      z ∉ (D.P.heckeDeterminantTwist χ₂).exceptional ∧
      z ∉ (D.Pd.heckeDeterminantTwist χ₁⁻¹).exceptional ∧
      z ∉ (D.Pd.heckeDeterminantTwist χ₂⁻¹).exceptional := by
    intro z hz
    simp only [B, X, Finset.mem_union, not_or] at hz
    tauto
  have hsub : ∀ {Y : Finset (FinitePlace F)}, (∀ z, z ∈ Y → z ∈ B) → Y ⊆ B := fun h z hz => h z hz
  refine ⟨B, hsub fun z hz => by simp [B, hz], fun z hz => ⟨hR₁ z (hB z hz).2.2.2.2.1,
    hR₂ z (hB z hz).2.2.2.2.2.1⟩, hD₁ B (hsub fun z hz => by simp [B, hz]),
    hA χ₁ hf₁ hi₁ B (hsub fun z hz => by simp [B, hz]) fun z hz => hR₁ z (hB z hz).2.2.2.2.1,
    hD₂ B (hsub fun z hz => by simp [B, hz]),
    hA χ₂ hf₂ hi₂ B (hsub fun z hz => by simp [B, hz]) fun z hz => hR₂ z (hB z hz).2.2.2.2.2.1,
    0, fun z hz s _ => ?_⟩
  obtain ⟨-, -, hzS₁, hzS₂, hzR₁, hzR₂, hzW₁, hzW₂, hzW₃, hzW₄, hzP, hzP', hzPd, hzPd',
    hzχ₁, hzχ₂, hzd₁, hzd₂⟩ := hB z hz
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · exact lFactor_eq_of_unramified D A hEps arch χ₁ S₁ hU₁ z hzS₁ hzP hzχ₁ hzP'
      (hR₁ z hzR₁) (hW₁ z hzP hzW₁) (hW₂ z hzP' hzW₂) s
  · exact dualLFactor_eq_of_unramified D A hEps arch χ₁ S₁ hU₁ z hzS₁ hzPd hzd₁ hzPd'
      (hR₁ z hzR₁) (hW₃ z hzPd hzW₃) (hW₄ z hzPd' hzW₄) s
  · exact lFactor_eq_of_unramified D A hEps arch χ₂ S₂ hU₂ z hzS₂ hzP hzχ₂ hzP'
      (hR₂ z hzR₂) (hW₁ z hzP hzW₁) (hW₂ z hzP' hzW₂) s
  · exact dualLFactor_eq_of_unramified D A hEps arch χ₂ S₂ hU₂ z hzS₂ hzPd hzd₂ hzPd'
      (hR₂ z hzR₂) (hW₃ z hzPd hzW₃) (hW₄ z hzPd' hzW₄) s

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup

end CommonInputs

/-! ## The gamma certificate and the assembly -/

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

/-- **Gamma certificate from the two setups over a totally complex field.** The totally
complex form of `hasHeckeGammaCertificate_setups`. -/
theorem hasHeckeGammaCertificate_setups_tc.{u, uQ, uV, uE}
    {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
    [NumberField.IsTotallyComplex F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E]
    (hFE : CuspidalPairGlobalFunctionalEquationTCStatement.{u, uQ})
    (hL1 : StableTwistPairGammaMatchStatement.{u, uV, uE})
    (hPS : PrincipalSeriesPairGammaMatchStatement.{u, uV, uE})
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (hGen : Automorphic.CuspidalLocalGenericityStatement.{u, uQ})
    (hc : IsArithmeticClassFamily c)
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)} [CompactSpace (AdeleQuotient F)]
    (hψ : ∃ x : Adeles F, ψ x ≠ 1) (hdiag : ∀ x : F, ψ (diagonal F x) = 1) {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (hadd : ∀ z, A.additive z = D.additive z)
    (hW : IsWeaklyAssociated S D.P.spectralSystem)
    (hW' : IsWeaklyAssociated S' D.P'.spectralSystem)
    (hWd : IsWeaklyAssociated S.dual D.Pd.spectralSystem)
    (hWd' : IsWeaklyAssociated S'.dual D.Pd'.spectralSystem)
    (ω ω' : HeckeCharacter F) (hω : D.T.realization.HasCentralCharacter ω)
    (hω' : D.T'.realization.HasCentralCharacter ω')
    (hdet : FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω)
    (hdet' : FiniteRepresentation.determinantCharacter S' = reciprocityCharacter c F E ω')
    (v : FinitePlace F) :
    HasHeckeGammaCertificate.{u, uV, uE} v (D.additive v) (D.measure v) (A.family v)
      (A.system v) (A.system_spec v) (localClass D.P D.h v) (localClass D.P' D.h' v)
      (localPairClass S (A.localMap v)) (localPairClass S' (A.localMap v)) := by
  classical
  obtain ⟨T₀, arch, hAin⟩ := A.exists_engineInputs hEps hc hψ hdiag
  obtain ⟨W₁, hW₁e, hW₁⟩ := exists_finset_isUnramifiedMatchAt hW
  obtain ⟨W₂, hW₂e, hW₂⟩ := exists_finset_isUnramifiedMatchAt hW'
  let Tb : Finset (FinitePlace F) := insert v (W₁ ∪ W₂)
  have hT : ∀ z ∉ Tb, ∃ (hz : z ∉ D.P.exceptional) (hz' : z ∉ D.P'.exceptional),
      IsUnramifiedMatchAt S z (D.P.spectralSystem.eulerPolynomial z hz) ∧
        IsUnramifiedMatchAt S' z (D.P'.spectralSystem.eulerPolynomial z hz') := by
    intro z hz
    simp only [Tb, Finset.mem_insert, Finset.mem_union, not_or] at hz
    have h1 : z ∉ D.P.exceptional := fun h => hz.2.1 (hW₁e h)
    have h2 : z ∉ D.P'.exceptional := fun h => hz.2.2 (hW₂e h)
    exact ⟨h1, h2, hW₁ z h1 hz.2.1, hW₂ z h2 hz.2.2⟩
  obtain ⟨depth, hram⟩ := ramifiedGammaStability_families hL1 hGen D A hEps arch hadd ω ω'
    hω hω' hdet hdet' hW.2.1 hW'.2.1 Tb
  -- the automorphic gamma factor at `v`
  have hd := Correspondence.twistedPairData_spec (D.additive v) (D.measure_spec v)
    (localClass D.P D.h v) (localClass D.P' D.h' v)
    (quasicharacterBase v ((1 : HeckeCharacter F).finiteComponent v))
  obtain ⟨πη, htw, hG⟩ := IsTwistedPairData.exists_gamma hd
  have htw1 := htw
  rw [HeckeCharacter.finiteComponent_one, quasicharacterBase_one] at htw1
  obtain rfl := htw1.unique (Correspondence.isCharacterTwist_one _)
  -- the arithmetic gamma factor at `v`
  have hfs := A.finiteFactors_spec hEps 1 v
  rw [localPairClass_dual, localPairClass_dual] at hfs
  obtain ⟨H, hH, hHc⟩ := hfs.exists_gamma
  change Correspondence.IsArithmeticPairGammaFactor _ _ _ _ _
    (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E 1) S) (A.localMap v))
    (localPairClass S' (A.localMap v)) H at hH
  rw [localPairClass_twist_of_trivial S (A.localMap v) _
    (fun g => reciprocityCharacter_one_apply _), hadd] at hH
  exact ⟨Tb, Finset.mem_insert_self v _, depth,
    HeckeEulerFamily.ofLocalFactors D.localFactors,
    HeckeEulerFamily.ofLocalFactors (A.localFactors arch), _, H, hG, hH,
    hasRationalContinuation_pairDataFactors_gamma hd htw hG, hHc,
    commonTwistEulerInputs_families_tc hFE hEps hψ hdiag D A hW hW' hWd hWd' T₀ arch hAin Tb,
    infinityGammaPreservation_families D A arch, finiteGammaPreservation_families D A arch v,
    hram, outsideGammaStability_families hPS hGen D A hEps arch hadd hW.2.1 hW'.2.1 Tb hT⟩

/-- **Henniart (2000), Théorème 2.3, over totally complex fields**, assuming the completed
global Rankin–Selberg functional equation for cuspidal pairs over totally complex fields and
the stable local comparison under highly ramified twists. The totally complex form of
`associatedGamma_of_inputs`. -/
theorem associatedGamma_of_inputs_tc.{u, uV, uP, uQ, uE}
    (hFE : CuspidalPairGlobalFunctionalEquationTCStatement.{u, u})
    (hL1 : StableTwistPairGammaMatchStatement.{u, uV, uE}) :
    AssociatedGammaTCStatement.{u, uV, uP, uQ, uE} := by
  classical
  have hGen := Automorphic.CuspidalPairPartialGamma.localGenericity.{u, u}
  have hPS : PrincipalSeriesPairGammaMatchStatement.{u, uV, uE} :=
    @principalSeriesPairGammaMatchStatement.{u, uV, uE}
  have hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE} :=
    @Correspondence.arithmeticPairEpsilonExistence.{u, uV, uE}
  have hPres : Automorphic.CuspidalAllLocalIrreduciblePresentationExistenceStatement.{u, uQ} :=
    @Automorphic.cuspidalAllLocalIrreduciblePresentationExistence.{u, uQ}
  have hDual : Automorphic.CuspidalDualPresentationExistenceStatement.{u, uQ, uQ} :=
    @Automorphic.cuspidalDualPresentationExistence.{u, uQ, uQ}
  have hContra : PresentedContragredientAssociationStatement.{u, uV, u, u} :=
    @presentedContragredientAssociation.{u, uV, u, u}
  intro c hc F E _ _ _ _ _ _ _ _ ψ hdiag r t S S' T T' hS hS' P P' v hI hA hI' hA' w e ι hι
    ψv hψv eC ε hε
  -- presentations with irreducible admissible local components, and contragredients
  obtain ⟨Q, hQ⟩ := hPres F r T P
  obtain ⟨Q', hQ'⟩ :=
    hPres F t T' P'
  obtain ⟨Td, hTd⟩ := Automorphic.cuspidalContragredientExistence F r T
  obtain ⟨Td', hTd'⟩ := Automorphic.cuspidalContragredientExistence F t T'
  obtain ⟨Pd₀⟩ := hDual F r T Td hTd P
  obtain ⟨Pd₀'⟩ := hDual F t T' Td' hTd' P'
  obtain ⟨Qd, hQd⟩ :=
    hPres F r Td Pd₀
  obtain ⟨Qd', hQd'⟩ :=
    hPres F t Td' Pd₀'
  -- weak association and central characters
  have hW := IsWeaklyAssociatedClass.presentation hS Q
  have hW' := IsWeaklyAssociatedClass.presentation hS' Q'
  have hWd := hContra c F E S T Td Q Qd hTd hW
  have hWd' := hContra c F E S' T' Td' Q' Qd' hTd' hW'
  obtain ⟨ω, hω, hdet, -⟩ := associatedCentralCharacter c hc F E S T hS
  obtain ⟨ω', hω', hdet', -⟩ := associatedCentralCharacter c hc F E S' T' hS'
  -- the global additive character is nontrivial
  have hψ : ∃ x : Adeles F, ψ x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rcases ψv with ⟨χ0, hc0, hn0⟩
    exact hn0 (DFunLike.ext χ0 1 fun x => (hψv x).trans (hcon _))
  -- choices supplied by the global functional equation
  obtain ⟨⟨⟨ch⟩, hreal, hcomplex⟩, -⟩ :=
    hFE F ψ hψ hdiag r t T Td T' Td' hTd hTd' Q Q' Qd Qd' hQ hQ' hQd hQd'
  choose aR haR using fun x => (hreal x).1
  choose dR hdR using fun x => (hreal x).2.1
  choose dR' hdR' using fun x => (hreal x).2.2.1
  choose dRd hdRd using fun x => (hreal x).2.2.2.1
  choose dRd' hdRd' using fun x => (hreal x).2.2.2.2
  choose aC haC using fun x => (hcomplex x).1
  choose dC hdC using fun x => (hcomplex x).2.1
  choose dC' hdC' using fun x => (hcomplex x).2.2.1
  choose dCd hdCd using fun x => (hcomplex x).2.2.2.1
  choose dCd' hdCd' using fun x => (hcomplex x).2.2.2.2
  have hadd_v : ch.additive v = ψv :=
    isCanonicalFiniteAdditiveComponent_unique (ch.additive_spec v) hψv
  have hν₀ : Correspondence.IsSelfDualMeasure (padicField v) ψv (ch.measure v) :=
    hadd_v ▸ ch.measure_spec v
  refine isPairGammaMatch_of_heckeGammaCertificate v ψv eC ε hε _ _ _ _ ⟨_, hν₀⟩
    fun ν hν => ?_
  -- the two setups, with the given local data at `v`
  let meas := Function.update ch.measure v ν
  have hmeas : ∀ z, Correspondence.IsSelfDualMeasure (padicField z) (ch.additive z)
      (meas z) := by
    intro z
    rcases eq_or_ne z v with rfl | hz
    · simp only [meas, Function.update_self]
      rw [hadd_v]
      exact hν
    · simp only [meas, Function.update_of_ne hz]
      exact ch.measure_spec z
  let D : AutomorphicTwistSetup.{u, u} ψ r t :=
    { T := T, T' := T', Td := Td, Td' := Td', hTd := hTd, hTd' := hTd', P := Q, P' := Q',
      Pd := Qd, Pd' := Qd', h := hQ, h' := hQ', hd := hQd, hd' := hQd',
      additive := ch.additive, additive_spec := ch.additive_spec, measure := meas,
      measure_spec := hmeas, aR := aR, aR_spec := haR, aC := aC, aC_spec := haC,
      dR := dR, dR' := dR', dRd := dRd, dRd' := dRd', dR_spec := hdR, dR'_spec := hdR',
      dRd_spec := hdRd, dRd'_spec := hdRd', dC := dC, dC' := dC', dCd := dCd, dCd' := dCd',
      dC_spec := hdC, dC'_spec := hdC', dCd_spec := hdCd, dCd'_spec := hdCd',
      w₀ := Classical.arbitrary _ }
  let ld := Function.update (fun z => Classical.choice (exists_localWeilData (E := E) hc z)) v
    ⟨w, e, ι, hι⟩
  let ls := Function.update
    (fun z => Classical.choice (exists_localSystem.{u, uE} (padicField z))) v ⟨eC, ε, hε⟩
  let A : ArithmeticTwistSetup.{u, uV, uE} ψ S S' :=
    { hS := hW.1, hS' := hW'.1, place := fun z => (ld z).1, candidate := fun z => (ld z).2.1,
      localMap := fun z => (ld z).2.2.1, localMap_spec := fun z => (ld z).2.2.2,
      additive := ch.additive, additive_spec := ch.additive_spec,
      family := fun z => (ls z).1, system := fun z => (ls z).2.1,
      system_spec := fun z => (ls z).2.2 }
  have hcert := hasHeckeGammaCertificate_setups_tc hFE hL1 hPS hEps hGen hc hψ hdiag D A
    (fun _ => rfl) hW hW' hWd hWd' ω ω' hω hω' hdet hdet' v
  have hcl : localClass Q hQ v = (P.localComponent v).padicClass hI hA :=
    Automorphic.CuspidalSpectralPresentation.localComponent_padicClass_eq Q P v _ _ hI hA
  have hcl' : localClass Q' hQ' v = (P'.localComponent v).padicClass hI' hA' :=
    Automorphic.CuspidalSpectralPresentation.localComponent_padicClass_eq Q' P' v _ _ hI' hA'
  change HasHeckeGammaCertificate.{u, uV, uE} v (ch.additive v) (meas v) (ls v).1 (ls v).2.1
    (ls v).2.2 (localClass Q hQ v) (localClass Q' hQ' v) (localPairClass S (ld v).2.2.1)
    (localPairClass S' (ld v).2.2.1) at hcert
  rw [hcl, hcl'] at hcert
  have hmv : meas v = ν := Function.update_self _ _ _
  have hldv : ld v = ⟨w, e, ι, hι⟩ := Function.update_self _ _ _
  have hlsv : ls v = ⟨eC, ε, hε⟩ := Function.update_self _ _ _
  have key : ∀ (a : Correspondence.NontrivialAdditiveCharacter (padicField v))
      (m : Correspondence.LocalAdditiveHaarMeasure (padicField v))
      (s : Σ' (eC' : LocalFactor.CommonClosure.ReciprocityFamily (padicField v))
        (ε' : LocalFactor.NonabelianSystem.Assignment.{u, uE} (padicField v)),
        LocalFactor.NonabelianSystem.IsSystem (padicField v) eC' ε')
      (d : Σ' (w' : FinitePlacesAbove E v)
        (e' : LocalFactor.RankOne.ReciprocityCandidate (towerPadicField v w'.1))
        (ι' : Weil.Local.localWeilGroup (padicField v) →ₜ* RelativeWeilGroup c F E),
        IsLocalRelativeWeilMap v w'.1 e' ι'),
      a = ψv → m = ν → s = ⟨eC, ε, hε⟩ → d = ⟨w, e, ι, hι⟩ →
      HasHeckeGammaCertificate.{u, uV, uE} v a m s.1 s.2.1 s.2.2
        ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
        (localPairClass S d.2.2.1) (localPairClass S' d.2.2.1) →
      HasHeckeGammaCertificate.{u, uV, uE} v ψv ν eC ε hε
        ((P.localComponent v).padicClass hI hA) ((P'.localComponent v).padicClass hI' hA')
        (localPairClass S ι) (localPairClass S' ι) := by
    rintro a m s d rfl rfl rfl rfl h
    exact h
  exact key _ _ _ _ hadd_v hmv hlsv hldv hcert

/-- **Henniart (2000), Théorème 2.3, over totally complex fields, from the totally complex
global functional equation.** The completed global Rankin–Selberg functional equation of
cuspidal pairs over totally complex number fields implies `AssociatedGammaTCStatement`; the
stable local comparison is the proved Library theorem `stableTwistPairGammaMatchStatement`. -/
theorem associatedGammaReductionTC.{u, uV, uP, uQ, uE} :
    AssociatedGammaReductionTCStatement.{u, uV, uP, uQ, uE} := fun hFE =>
  associatedGamma_of_inputs_tc.{u, uV, uP, uQ, uE} hFE
    stableTwistPairGammaMatchStatement.{u, uV, uE}

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup
