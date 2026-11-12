import Langlands.Correspondence.HenniartExtensionTwist
import Langlands.Correspondence.RankOneOperationCompatibility
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.VirtualRepresentation.Weil.UnitaryExpansion

/-!
# Rank one and the extended stable map

The trivial rank-one Weil class is unitary and factors through the trivial
quotient of the absolute Galois group. The character clause of a candidate
makes its stable image the trivial character of `GL₁`. Twist compatibility of
the extended map and of the published rank-one bijection then identify the
extension in rank one with that bijection.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV uE

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartExtensionRankOneFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

/-- The trivial rank-one Weil class pulled back along `e`, as a basis class. -/
abbrev trivialWeilBasis (e : ReciprocityCandidate K) : LocalWeil.Basis.{uK, uW} K :=
  ⟨1, rankOneWeilCharacterClass K e 1⟩

/-- The trivial rank-one class is unitary. -/
theorem trivialWeilBasis_isUnitary (e : ReciprocityCandidate K) :
    Weil.IsUnitaryClass _ (trivialWeilBasis.{uK, uW} K e) := by
  refine ⟨FiniteRepresentation.characterLine (LocalFactor.RankOne.weilCharacter K e 1).toMonoidHom,
    FiniteRepresentation.isUnitary_of_hasFiniteImage _ ?_, rfl⟩
  apply (Set.finite_singleton (1 : Module.End ℂ (ULift.{uW} ℂ))).subset
  rintro _ ⟨g, rfl⟩
  ext v
  change ((LocalFactor.RankOne.weilCharacter K e 1 g : ℂˣ) : ℂ) • v = v
  change ((1 : ℂˣ) : ℂ) • v = v
  rw [Units.val_one, one_smul]

/-- The trivial rank-one class as a unitary basis class. -/
abbrev trivialWeilUnitary (e : ReciprocityCandidate K) : LocalWeil.UnitaryBasis.{uK, uW} K :=
  ⟨trivialWeilBasis K e, trivialWeilBasis_isUnitary K e⟩

/-- The trivial rank-one class factors through the trivial quotient. -/
theorem trivialWeilUnitary_isFiniteFactoring (e : ReciprocityCandidate K) :
    IsFiniteFactoring K (trivialWeilUnitary.{uK, uW} K e) := by
  refine ⟨PUnit.{uK + 1}, inferInstance, inferInstance, 1, ?_⟩
  refine Finsupp.single_mem_supported ℤ 1 ?_
  refine ⟨FiniteRepresentation.characterLine.{uK, uW} (1 : PUnit.{uK + 1} →* ℂˣ), ?_⟩
  apply Quotient.sound
  refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun g => ?_⟩
  ext v
  change ((1 : ℂˣ) : ℂ) • v = ((LocalFactor.RankOne.weilCharacter K e 1 g : ℂˣ) : ℂ) • v
  rfl

/-- The extension sends the trivial rank-one class to the trivial character of
`GL₁`. -/
theorem extensionMap_trivial (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    extensionMap K hSC 1 (rankOneWeilCharacterClass K e 1) = rankOneSupercuspidalClass K 1 := by
  obtain ⟨y, hy, hinc⟩ := extensionMap_agrees K hSC hUTI (trivialWeilUnitary K e)
    (trivialWeilUnitary_isFiniteFactoring K e)
  obtain ⟨Q, _, _, q, hσ, ⟨W, A, Φ, hΦ⟩, hall⟩ := hy
  obtain ⟨x, hx, hΦx⟩ := (hΦ.2.1.2.2.2 e he 1 (fun _ => by simp)).2
  have hxgen : (x : LocalWeil.UnitaryLattice.{uK, uW} K) = generator (trivialWeilUnitary K e) := by
    apply Weil.includeUnitary_injective (Weil.Local.localWeilGroup K)
    change LocalWeil.includeUnitary K x = LocalWeil.includeUnitary K (generator _)
    rw [hx]
    exact (Weil.includeUnitary_generator (trivialWeilUnitary K e)).symm
  have hy' := hall W A Φ hΦ x hxgen
  rw [hy'] at hΦx
  rw [hΦx] at hinc
  exact (eq_of_heq (Sigma.mk.inj (Finsupp.single_left_injective one_ne_zero hinc)).2).symm

/-- Rank-one compatibility of the extended stable map. -/
theorem extensionMap_rankOne (hCE : CandidateExistenceStatement.{uK, uW, uV, uE, uK})
    (hSC : StableCorrespondenceStatement.{uK, uW, uV, uE})
    (hUTI : UnramifiedTwistIndependenceStatement.{uK, uW, uV, uE})
    {e : ReciprocityCandidate K} (he : IsGeometricReciprocity K e) :
    SupercuspidalRankOneCompatibility K e (extensionMap K hSC) := by
  rw [supercuspidalRankOneCompatibility_iff_eq]
  have htw := (supercuspidalTwistCompatibility_iff K e _).mp (extensionMap_twist K hCE hSC hUTI he)
  funext σ
  obtain ⟨χ, rfl⟩ := rankOneWeilCharacterClass_surjective K e σ
  have hσ : FiniteRepresentation.continuousIrreducibleTwistEquiv
      (LocalFactor.RankOne.weilCharacter K e χ) ((1 : ℕ+) : ℕ)
        (rankOneWeilCharacterClass K e 1) =
        rankOneWeilCharacterClass.{uK, uW} K e χ := by
    have h1 := IsRankOneWeilCharacter.twist K (rankOneWeilCharacterClass_spec K e 1)
      (LocalFactor.RankOne.weilCharacter K e χ)
    have hchar : (LocalFactor.RankOne.weilCharacter K e χ).toMonoidHom * weilCharacter K e 1 =
        weilCharacter K e χ := by
      ext g
      change ((LocalFactor.RankOne.weilCharacter K e χ g *
        (1 : QuasiCharacter K) (reciprocityHom K e g) : ℂˣ) : ℂ) =
          ((LocalFactor.RankOne.weilCharacter K e χ g : ℂˣ) : ℂ)
      change ((LocalFactor.RankOne.weilCharacter K e χ g * 1 : ℂˣ) : ℂ) = _
      rw [mul_one]
    rw [hchar] at h1
    exact IsRankOneWeilCharacter.class_unique K h1 (rankOneWeilCharacterClass_spec K e χ)
  have hσ' : FiniteRepresentation.continuousIrreducibleTwistEquiv
      (LocalFactor.RankOne.weilCharacter K e χ) 1 (rankOneWeilCharacterClass K e 1) =
        rankOneWeilCharacterClass.{uK, uW} K e χ := hσ
  have hR := rankOneReciprocityEquiv_twist.{uK, uW, uV} K e (rankOneWeilCharacterClass K e 1) χ
  rw [isSupercuspidalCharacterTwist_iff_eq_supercuspidalTwist, hσ',
    rankOneReciprocityEquiv_character, rankOneReciprocityEquiv_character] at hR
  rw [← hσ, htw, extensionMap_trivial K hSC hUTI he, hσ, rankOneReciprocityEquiv_character, hR]

end Langlands.Henniart.Extension
