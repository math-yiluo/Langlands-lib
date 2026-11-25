import Langlands.Automorphic.AssociatedGammaRamifiedInputs
import Langlands.Automorphic.CuspidalLocalGenericityStatement

/-!
# Ramified gamma stability for the two Hecke families

From the stable comparison under highly ramified twists (`StableTwistPairGammaMatchStatement`)
and local genericity of cuspidal components, at every finite place there is a depth such
that the gamma factors of the two families agree for every finite-order Hecke character that
is nontrivial on the principal units of that depth.
-/

noncomputable section

set_option autoImplicit false

universe u uQ uV uE

namespace Langlands.ClassFieldTheory.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality
open Langlands.Global.CuspidalPairFunctionalEquation

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E]

/-- Every class has a twist by every quasi-character. -/
theorem exists_isCharacterTwist {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p} {n : ℕ+}
    (η : Correspondence.QuasiCharacter K) (π : Correspondence.AutomorphicClass.{u, u} K n) :
    ∃ πη, Correspondence.IsCharacterTwist K η π πη :=
  ⟨_, (Correspondence.isCharacterTwist_iff_eq_twist K η
    (Correspondence.isOpen_ker_determinantQuasiCharacter K n η) π _).mpr rfl⟩

/-- **Ramified gamma stability** for the two families, from the stable comparison. -/
theorem ramifiedGammaStability_families
    (hL1 : StableTwistPairGammaMatchStatement.{u, uV, uE})
    (hGen : Automorphic.CuspidalLocalGenericityStatement.{u, uQ})
    {ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)}
    [CompactSpace (AdeleQuotient F)] {r t : ℕ}
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    (D : AutomorphicTwistSetup.{u, uQ} ψ r t) (A : ArithmeticTwistSetup.{u, uV, uE} ψ S S')
    (hEps : Correspondence.ArithmeticPairEpsilonExistenceStatement.{u, uV, uE})
    (arch : NumberField.InfinitePlace F → LocalFactors)
    (hadd : ∀ z, A.additive z = D.additive z)
    (ω ω' : HeckeCharacter F) (hω : D.T.realization.HasCentralCharacter ω)
    (hω' : D.T'.realization.HasCentralCharacter ω')
    (hdet : FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω)
    (hdet' : FiniteRepresentation.determinantCharacter S' = reciprocityCharacter c F E ω')
    (hrank : S.rank = r + 1) (hrank' : S'.rank = t + 1) (T : Finset (FinitePlace F)) :
    ∃ depth : FinitePlace F → ℕ, RamifiedGammaStability F T depth
      (HeckeEulerFamily.ofLocalFactors D.localFactors)
      (HeckeEulerFamily.ofLocalFactors (A.localFactors arch)) := by
  have hstable : ∀ z : FinitePlace F, ∃ Az : ℕ,
      ∀ χ' : Correspondence.QuasiCharacter (padicField z),
        Az ≤ (padicField z).canonicalTopologicalData.multiplicativeConductor χ' →
        ∀ πχ : Correspondence.AutomorphicClass.{u, u} (padicField z) r.succPNat,
          Correspondence.IsCharacterTwist (padicField z) χ' (localClass D.P D.h z) πχ →
          IsPairGammaMatch (padicField z) (A.family z) (A.system z) (A.system_spec z)
            (D.additive z) πχ (localClass D.P' D.h' z)
            (WeilDeligneRepresentation.twistClass
              (Correspondence.weilCharacter (padicField z)
                (Correspondence.baseReciprocityCandidate _ (A.family z)) χ')
              (localPairClass S (A.localMap z)))
            (localPairClass S' (A.localMap z)) := by
    intro z
    exact hL1 (padicField z) (A.family z) (A.system z) (A.system_spec z)
      (Correspondence.baseReciprocityCandidate _ (A.family z))
      (Correspondence.baseReciprocityCandidate_spec _ (A.family z)) (D.additive z)
      (localClass D.P D.h z) (localClass D.P' D.h' z)
      (quasicharacterBase z (ω.finiteComponent z)) (quasicharacterBase z (ω'.finiteComponent z))
      (localPairClass S (A.localMap z)) (localPairClass S' (A.localMap z))
      ⟨_, rfl, hGen F r D.T D.P z (D.h z).1 (D.h z).2 (D.additive z)⟩
      ⟨_, rfl, hGen F t D.T' D.P' z (D.h' z).1 (D.h' z).2 (D.additive z)⟩
      (centralActsBy_localClass D.P D.h ω hω z) (centralActsBy_localClass D.P' D.h' ω' hω' z)
      ⟨_, rfl, hrank, localComponent_isContinuous _ A.hS,
        determinantCharacter_localComponent S (A.localMap_spec z) (A.family z)
          (A.system_spec z).1 ω hdet⟩
      ⟨_, rfl, hrank', localComponent_isContinuous _ A.hS',
        determinantCharacter_localComponent S' (A.localMap_spec z) (A.family z)
          (A.system_spec z).1 ω' hdet'⟩
  choose depth hdepth using hstable
  refine ⟨depth, fun z _ χ _ hχ => ?_⟩
  obtain ⟨πη, htw⟩ := exists_isCharacterTwist (quasicharacterBase z (χ.finiteComponent z))
    (localClass D.P D.h z)
  have hcond := (lt_multiplicativeConductor_quasicharacterBase _ _ hχ).le
  have hmatch := hdepth z _ hcond πη htw
  rw [← localPairClass_twist_eq_twistClass S (A.localMap_spec z) (A.family z)
    (A.system_spec z).1 χ] at hmatch
  exact meromorphicEq_gamma_of_isPairGammaMatch D A hEps arch χ z (hadd z) htw hmatch

end Langlands.ClassFieldTheory.Global.RelativeWeilGroup
