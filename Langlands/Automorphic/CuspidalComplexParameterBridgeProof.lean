import Langlands.Automorphic.ComplexPlaceCentralAction
import Langlands.Automorphic.ComplexPlaceDominantWeights
import Langlands.Automorphic.CuspidalComplexParameterBridgeStatement
import Langlands.Global.ComplexEmbeddingHighestWeight
import Langlands.Global.Factors.CuspidalArchimedeanParameterExistenceTCProof

/-! # The totally complex cuspidal infinitesimal-character bridge -/

noncomputable section

universe uF

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Langlands.Automorphic

open NumberField
open Langlands.Global Langlands.Global.ArchimedeanGL
open Langlands.Archimedean.VermaShifted Langlands.LocalFactor.Archimedean
open ComplexPlaceParameter

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}
local notation "Weight" => EmbeddingIndex F → Fin n → ℂ
local notation "Character" => EnvelopingCenter F n →ₐ[ℂ] ℂ

private theorem ofFn_exponent_sub_rho (ds : List ComplexCharacterData) (hlen : ds.length = n)
    (coord : ComplexCharacterData → ℂ) :
    (List.ofFn fun i : Fin n => coord (ds.get (Fin.cast hlen.symm i)) - rho n i + rho n i) =
      ds.map coord := by
  subst n
  rw [← List.ofFn_getElem_eq_map]
  apply congrArg List.ofFn
  funext i
  simp

private theorem exists_matchesGlobalHighestWeight (ds : CP → List ComplexCharacterData)
    (hlen : ∀ v, (ds v).length = n) :
    ∃ μ : Weight, MatchesGlobalHighestWeight F n ds μ := by
  let weight (coord : ComplexCharacterData → ℂ) (v : CP) (i : Fin n) :=
    coord ((ds v).get (Fin.cast (hlen v).symm i)) - rho n i
  let μ : Weight
    | .inl _ => 0
    | .inr (v, false) => weight ComplexCharacterData.zExponent v
    | .inr (v, true) => weight ComplexCharacterData.zBarExponent v
  refine ⟨μ, fun v => ⟨hlen v, ?_, ?_⟩⟩
  · exact List.Perm.of_eq (ofFn_exponent_sub_rho (ds v) (hlen v) _).symm
  · exact List.Perm.of_eq (ofFn_exponent_sub_rho (ds v) (hlen v) _).symm

variable [IsTotallyComplex F]

private theorem character_eq_of_matches (ds : CP → List ComplexCharacterData)
    {μ ν : Weight} {χ ψ : Character}
    (hχ : IsHighestWeightCharacter F n μ χ) (hψ : IsHighestWeightCharacter F n ν ψ)
    (hμ : MatchesGlobalHighestWeight F n ds μ) (hν : MatchesGlobalHighestWeight F n ds ν) :
    χ = ψ := by
  apply complexEmbeddingCenter_hom_ext F n
  intro j z
  rw [isHighestWeightCharacter_block F n μ χ hχ, isHighestWeightCharacter_block F n ν ψ hψ]
  apply AlgHom.congr_fun ((upperCharacter_eq_iff n (μ j) (ν j)).mpr ?_)
  obtain ⟨⟨v, k⟩, rfl⟩ := (complexEmbeddingIndex F).surjective j
  fin_cases k
  · simpa using (hμ v).2.1.symm.trans (hν v).2.1
  · simpa using (hμ v).2.2.symm.trans (hν v).2.2

private theorem existsUnique_matchesInfinitesimalCharacter (ds : CP → List ComplexCharacterData)
    (hlen : ∀ v, (ds v).length = n) :
    ∃! χ : Character, MatchesInfinitesimalCharacter F n ds χ := by
  obtain ⟨μ, hμ⟩ := exists_matchesGlobalHighestWeight ds hlen
  let χ := globalHighestWeightCharacter F n μ
  have hχ := isHighestWeightCharacter_globalHighestWeightCharacter F n μ
  refine ⟨χ, ⟨μ, hχ, hμ⟩, ?_⟩
  rintro ψ ⟨ν, hψ, hν⟩
  exact character_eq_of_matches ds hψ hχ hν hμ

private theorem isRegularAlgebraicCharacter_iff_clozel (ds : CP → List ComplexCharacterData)
    (χ : Character) (hmatch : MatchesInfinitesimalCharacter F n ds χ) :
    IsRegularAlgebraicCharacter F n χ ↔ ∀ v, IsClozelRegularAlgebraic n (ds v) := by
  obtain ⟨μ, hχ, hμ⟩ := hmatch
  constructor
  · rintro ⟨ν, hν, hχν⟩
    have horbit (j : EmbeddingIndex F) :
        (List.ofFn fun i => μ j i + rho n i).Perm
          (List.ofFn fun i => (ν j i : ℂ) + rho n i) := by
      apply (upperCharacter_eq_iff n _ _).mp
      apply AlgHom.ext
      intro z
      exact (isHighestWeightCharacter_block F n μ χ hχ j z).symm.trans
        (isHighestWeightCharacter_block F n _ χ hχν j z)
    intro v
    exact isClozelRegularAlgebraic_of_matchesDominant (hν (.inr (v, false))) (hν (.inr (v, true)))
      ⟨(hμ v).1, (hμ v).2.1.trans (horbit _), (hμ v).2.2.trans (horbit _)⟩
  · intro h
    choose weightZ weightBar hz hbar hweights using
      fun v => exists_matchesDominant_of_isClozelRegularAlgebraic (h v)
    let ν : EmbeddingIndex F → Fin n → ℤ
      | .inl _ => 0
      | .inr (v, false) => weightZ v
      | .inr (v, true) => weightBar v
    have hν : ∀ j, Antitone (ν j) := by
      rintro (w | ⟨v, b⟩)
      · exact antitone_const
      · cases b
        · exact hz v
        · exact hbar v
    let ψ := globalHighestWeightCharacter F n (fun j i => (ν j i : ℂ))
    have hψ := isHighestWeightCharacter_globalHighestWeightCharacter F n (fun j i => (ν j i : ℂ))
    have he : ψ = χ := character_eq_of_matches ds hψ hχ hweights hμ
    exact ⟨ν, hν, he ▸ hψ⟩

/-- The actual complex-place lists determine the character acting on the cuspidal realization. -/
theorem cuspidalComplexParameterInfinitesimalCharacterTC :
    CuspidalComplexParameterInfinitesimalCharacterTCStatement.{uF} := by
  intro F _ _ _ _ r S ds hd
  refine ⟨existsUnique_matchesInfinitesimalCharacter ds (fun v => (hd v).1), ?_⟩
  rintro χ ⟨μ, hχ, hμ⟩
  exact S.realization.hasInfinitesimalCharacter_of_complexPlaceParameters S.irreducible ds hd χ μ hμ
    (isHighestWeightCharacter_block F (r + 1) μ χ hχ)

/-- The numerical Clozel condition is equivalent to regular algebraicity of the matching character. -/
theorem complexParameterRegularAlgebraicTC : ComplexParameterRegularAlgebraicTCStatement.{uF} := by
  intro F _ _ _ n ds χ hχ
  exact isRegularAlgebraicCharacter_iff_clozel ds χ hχ

/-- Parameter existence, computation of the actual center action, and the Clozel comparison. -/
theorem cuspidalComplexParameterBridgeTC : CuspidalComplexParameterBridgeTCStatement.{uF} :=
  ⟨cuspidalArchimedeanParameterExistenceTC, cuspidalComplexParameterInfinitesimalCharacterTC,
    complexParameterRegularAlgebraicTC⟩

end Langlands.Automorphic
