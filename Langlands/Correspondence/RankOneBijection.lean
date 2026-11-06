import Langlands.Correspondence.RankOneExistence

/-! # Actual rank-one character bijections -/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA uG

private theorem character_eq_of_equiv {G : Type uG} [Group G]
    {χ η : G →* ℂˣ}
    (e : (Langlands.characterRepresentation χ).Equiv
      (Langlands.characterRepresentation η)) : χ = η := by
  have h := FiniteRepresentation.determinantCharacter_eq
    (A := FiniteRepresentation.of (Langlands.characterRepresentation χ))
    (B := FiniteRepresentation.of (Langlands.characterRepresentation η)) e
  ext g
  have hg := congrArg (fun δ : G →* ℂˣ => (δ g : ℂ)) h
  change LinearMap.det (Langlands.characterRepresentation χ g) =
    LinearMap.det (Langlands.characterRepresentation η g) at hg
  rw [LinearMap.det_ring, LinearMap.det_ring] at hg
  change (χ g : ℂ) * 1 = (η g : ℂ) * 1 at hg
  simpa only [mul_one] using hg

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rankOneBijectionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- A rank-one actual automorphic class determines its field character. -/
theorem IsRankOneCharacter.character_unique {χ η : QuasiCharacter F}
    {π : AutomorphicClass.{uF, uA} F 1}
    (hχ : IsRankOneCharacter F χ π) (hη : IsRankOneCharacter F η π) : χ = η := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hχ
  obtain ⟨B, hB, ⟨eB⟩⟩ := hη
  obtain ⟨e⟩ := (automorphicClassOf_eq_iff F A B).mp (hA.trans hB.symm)
  have hdet := character_eq_of_equiv (eA.trans (e.trans eB.symm))
  apply ContinuousMonoidHom.ext
  intro a
  obtain ⟨g, hg⟩ :=
    Matrix.GeneralLinearGroup.det_surjective (n := Fin ((1 : ℕ+) : ℕ)) a
  have h := DFunLike.congr_fun hdet g
  simpa only [determinantQuasiCharacter, MonoidHom.comp_apply, hg,
    ContinuousMonoidHom.coe_toMonoidHom, MonoidHom.coe_coe] using h

/-- The lifted actual supercuspidal character-class map is injective. -/
theorem rankOneSupercuspidalClass_injective :
    Function.Injective (rankOneSupercuspidalClass.{uF, uA} F) := by
  intro χ η h
  apply IsRankOneCharacter.character_unique F
    (rankOneSupercuspidalClass_spec F χ)
  rw [h]
  exact rankOneSupercuspidalClass_spec F η

/-- Continuous field characters classify actual supercuspidal GL₁ classes. -/
def rankOneSupercuspidalCharacterEquiv :
    QuasiCharacter F ≃ SupercuspidalAutomorphicClass.{uF, uA} F 1 :=
  Equiv.ofBijective (rankOneSupercuspidalClass F)
    ⟨rankOneSupercuspidalClass_injective F, rankOneSupercuspidalClass_surjective F⟩

/-- The abstract Weil character of a rank-one actual class is unique. -/
theorem IsRankOneWeilCharacter.character_unique
    {χ η : Weil.Local.localWeilGroup F →* ℂˣ}
    {σ : IrreducibleWeilClass.{uF, uP} F 1}
    (hχ : IsRankOneWeilCharacter F χ σ)
    (hη : IsRankOneWeilCharacter F η σ) : χ = η := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hχ
  obtain ⟨B, hB, ⟨eB⟩⟩ := hη
  obtain ⟨e⟩ := (FiniteRepresentation.classOf_eq_iff A B).mp (hA.trans hB.symm)
  exact character_eq_of_equiv (eA.trans (e.trans eB.symm))

/-- Pullback along a supplied reciprocity candidate is injective on characters. -/
theorem weilCharacter_injective (e : ReciprocityCandidate F) :
    Function.Injective (weilCharacter F e) := by
  intro χ η h
  have hc : LocalFactor.RankOne.weilCharacter F e χ =
      LocalFactor.RankOne.weilCharacter F e η := by
    apply ContinuousMonoidHom.ext
    intro w
    exact DFunLike.congr_fun h w
  calc
    χ = LocalFactor.RankOne.fieldCharacter F e
        (LocalFactor.RankOne.weilCharacter F e χ) :=
      (LocalFactor.RankOne.fieldCharacter_weilCharacter F e χ).symm
    _ = LocalFactor.RankOne.fieldCharacter F e
        (LocalFactor.RankOne.weilCharacter F e η) := congrArg _ hc
    _ = η := LocalFactor.RankOne.fieldCharacter_weilCharacter F e η

end Langlands.Correspondence
