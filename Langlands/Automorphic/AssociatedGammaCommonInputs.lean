import Langlands.Automorphic.AssociatedGammaOutsideMatch
import Langlands.Global.Factors.HeckeFiniteRamification

/-!
# The common-twist analytic input for the two Hecke families

Given the completed global Rankin–Selberg equation, the existence of arithmetic epsilon
factors, and weak association of `S`, `S'`, `S^∨`, `S'^∨` with the Satake parameters of the
presentations `P`, `P'`, `Pd`, `Pd'`, the automorphic and arithmetic Hecke Euler families
satisfy `CommonTwistEulerInputs` for every finite set `T`.
-/

noncomputable section

set_option autoImplicit false

open scoped Classical

universe u uQ uV uE

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- Weak association gives one finite set outside which the unramified matching holds. -/
theorem exists_finset_isUnramifiedMatchAt [CompactSpace (AdeleQuotient F)] {n : ℕ}
    {S₀ : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {s : Unramified.SpectralSystem (FinitePlace F) n} (h : IsWeaklyAssociated S₀ s) :
    ∃ W : Finset (FinitePlace F), s.exceptional ⊆ W ∧
      ∀ (z : FinitePlace F) (hz : z ∉ s.exceptional), z ∉ W →
        IsUnramifiedMatchAt S₀ z (s.eulerPolynomial z hz) := by
  obtain ⟨-, -, W, hW, hm⟩ := (isWeaklyAssociated_iff_exists_finset S₀ s).mp h
  exact ⟨W, hW, fun z _ hzW => hm z hzW⟩

/-- **Common-twist analytic input** for the two families. -/
theorem commonTwistEulerInputs_families
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (hFE : CuspidalPairGlobalFunctionalEquationStatement.{u, uQ})
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
  obtain ⟨S₁, hU₁, hD₁⟩ := D.exists_engineInputs hFE hψ hdiag χ₁ hi₁
  obtain ⟨S₂, hU₂, hD₂⟩ := D.exists_engineInputs hFE hψ hdiag χ₂ hi₂
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
