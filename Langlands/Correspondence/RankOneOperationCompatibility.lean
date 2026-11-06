import Langlands.Correspondence.RankOneReciprocityBijection
import Langlands.Representation.Smooth.Contragredient.Equivalence

/-! # Twists and duals for the actual rank-one correspondence -/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA uG

/-- Evaluation at one identifies the algebraic dual of a scalar character
with the scalar representation of its inverse. -/
def scalarCharacterDualEquiv {G : Type uG} [Group G] (χ : G →* ℂˣ) :
    (Langlands.characterRepresentation χ).dual.Equiv
      (Langlands.characterRepresentation χ⁻¹) where
  toLinearEquiv := LinearMap.ringLmapEquivSelf ℂ ℂ ℂ
  isIntertwining' g := by
    ext ℓ
    change ℓ ((χ g⁻¹ : ℂ) • (1 : ℂ)) = ((χ⁻¹ g : ℂ)) • ℓ 1
    rw [map_smul]
    simp

private theorem scalarCharacterDual_smooth {G : Type uG} [Group G]
    [TopologicalSpace G] (χ : G →* ℂˣ)
    (hχ : IsOpen (χ.ker : Set G)) :
    IsSmooth (Langlands.characterRepresentation χ).dual := by
  intro ℓ
  refine ⟨⟨χ.ker, hχ⟩, ?_⟩
  intro g
  change (Langlands.characterRepresentation χ).dual g.val ℓ = ℓ
  apply LinearMap.ext
  intro x
  have hg : χ g.val = 1 := g.property
  change ℓ ((χ g.val⁻¹ : ℂ) • x) = ℓ x
  simp [hg]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rankOneOperationFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance rankOneOperationGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance rankOneOperationGLTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Twisting an actual rank-one Weil class multiplies its scalar character. -/
theorem IsRankOneWeilCharacter.twist
    {η : Weil.Local.localWeilGroup F →* ℂˣ}
    {σ : IrreducibleWeilClass.{uF, uP} F 1}
    (hσ : IsRankOneWeilCharacter F η σ)
    (χ : Weil.Local.localWeilGroup F →ₜ* ℂˣ) :
    IsRankOneWeilCharacter F (χ.toMonoidHom * η)
      (FiniteRepresentation.continuousIrreducibleTwistEquiv χ 1 σ) := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hσ
  refine ⟨FiniteRepresentation.twist χ.toMonoidHom A, ?_, ?_⟩
  · exact (congrArg (FiniteRepresentation.twistClass χ.toMonoidHom) hA).trans
      (FiniteRepresentation.forget_continuousIrreducibleTwistEquiv
        χ ((1 : ℕ+) : ℕ) σ).symm
  · have heq : Langlands.twist χ.toMonoidHom (Langlands.characterRepresentation η) =
        Langlands.characterRepresentation (χ.toMonoidHom * η) :=
      Langlands.twist_twist _ _ _
    exact ⟨(equivOfRepresentationEq heq.symm).trans (Langlands.twistEquiv _ eA)⟩

/-- Duality of an actual rank-one Weil class inverts its scalar character. -/
theorem IsRankOneWeilCharacter.dual
    {χ : Weil.Local.localWeilGroup F →* ℂˣ}
    {σ : IrreducibleWeilClass.{uF, uP} F 1}
    (hσ : IsRankOneWeilCharacter F χ σ) :
    IsRankOneWeilCharacter F χ⁻¹
      (FiniteRepresentation.continuousIrreducibleDualEquiv 1 σ) := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hσ
  refine ⟨FiniteRepresentation.dual A, ?_, ?_⟩
  · exact (congrArg FiniteRepresentation.dualClass hA).trans
      (FiniteRepresentation.forget_continuousIrreducibleDualEquiv
        ((1 : ℕ+) : ℕ) σ).symm
  · exact ⟨(scalarCharacterDualEquiv χ).symm.trans (Langlands.dualEquiv eA).symm⟩

/-- Actual rank-one classes realizing multiplied characters satisfy the
existing character-twist relation. -/
theorem IsRankOneCharacter.characterTwist
    {χ η : QuasiCharacter F} {π π' : AutomorphicClass.{uF, uA} F 1}
    (hπ : IsRankOneCharacter F η π)
    (hπ' : IsRankOneCharacter F (χ * η) π') :
    IsCharacterTwist F χ π π' := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hπ
  obtain ⟨B, hB, ⟨eB⟩⟩ := hπ'
  refine ⟨A, B, hA, hB, ?_⟩
  have heq : Langlands.twist (determinantQuasiCharacter F 1 χ)
        (Langlands.characterRepresentation (determinantQuasiCharacter F 1 η)) =
      Langlands.characterRepresentation (determinantQuasiCharacter F 1 (χ * η)) := by
    rw [Langlands.characterRepresentation, Langlands.twist_twist]
    rfl
  exact ⟨((Langlands.twistEquiv _ eA).symm.trans
    (equivOfRepresentationEq heq)).trans eB⟩

/-- Actual rank-one classes realizing inverse characters satisfy the existing
smooth-contragredient relation. -/
theorem IsRankOneCharacter.smoothDual
    {χ : QuasiCharacter F} {π π' : AutomorphicClass.{uF, uA} F 1}
    (hπ : IsRankOneCharacter F χ π)
    (hπ' : IsRankOneCharacter F χ⁻¹ π') :
    IsSmoothDual F π π' := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hπ
  obtain ⟨B, hB, ⟨eB⟩⟩ := hπ'
  refine ⟨A, B, hA, hB, ?_⟩
  let := F.canonicalGeneralLinearNonarchimedean 1
  let χdet : GeneralLinear 1 F.Carrier →* ℂˣ := determinantQuasiCharacter F 1 χ
  have hcont : Continuous χdet :=
    χ.continuous.comp
      (F.canonicalTopologicalData.generalLinearDeterminant 1).continuous
  have hopen : IsOpen (χdet.ker : Set (GeneralLinear 1 F.Carrier)) :=
    isOpen_ker_of_continuous_complex_character χdet hcont
  have heq : (Langlands.characterRepresentation (determinantQuasiCharacter F 1 χ)⁻¹) =
      Langlands.characterRepresentation (determinantQuasiCharacter F 1 χ⁻¹) := rfl
  exact ⟨(((Langlands.smoothContragredientEquiv eA).trans
    (Langlands.smoothEquiv (scalarCharacterDual_smooth χdet hopen))).trans
      (scalarCharacterDualEquiv χdet)).trans ((equivOfRepresentationEq heq).trans eB)⟩

/-- The actual rank-one bijection respects every continuous field-character twist. -/
theorem rankOneReciprocityEquiv_twist (e : ReciprocityCandidate F)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) (χ : QuasiCharacter F) :
    IsSupercuspidalCharacterTwist F χ (rankOneReciprocityEquiv.{uF, uP, uA} F e σ)
      (rankOneReciprocityEquiv F e
        (FiniteRepresentation.continuousIrreducibleTwistEquiv
          (LocalFactor.RankOne.weilCharacter F e χ) 1 σ)) := by
  obtain ⟨η, hσ⟩ := exists_rankOneWeilFieldCharacter F e σ
  have htw : IsRankOneWeilCharacter F (weilCharacter F e (χ * η))
      (FiniteRepresentation.continuousIrreducibleTwistEquiv
        (LocalFactor.RankOne.weilCharacter F e χ) 1 σ) :=
    IsRankOneWeilCharacter.twist F hσ _
  exact IsRankOneCharacter.characterTwist F
    (rankOneReciprocityEquiv_spec F e η σ hσ)
    (rankOneReciprocityEquiv_spec F e (χ * η) _ htw)

/-- The actual rank-one bijection respects the certified Weil dual and the
actual smooth contragredient. -/
theorem rankOneReciprocityEquiv_dual (e : ReciprocityCandidate F)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) :
    IsSupercuspidalSmoothDual F (rankOneReciprocityEquiv.{uF, uP, uA} F e σ)
      (rankOneReciprocityEquiv F e
        (FiniteRepresentation.continuousIrreducibleDualEquiv 1 σ)) := by
  obtain ⟨χ, hσ⟩ := exists_rankOneWeilFieldCharacter F e σ
  have hdual : IsRankOneWeilCharacter F (weilCharacter F e χ⁻¹)
      (FiniteRepresentation.continuousIrreducibleDualEquiv 1 σ) :=
    IsRankOneWeilCharacter.dual F hσ
  exact IsRankOneCharacter.smoothDual F
    (rankOneReciprocityEquiv_spec F e χ σ hσ)
    (rankOneReciprocityEquiv_spec F e χ⁻¹ _ hdual)

/-- Rank-one compatibility implies the rank-one part of twist compatibility. -/
theorem SupercuspidalRankOneCompatibility.twist_rankOne
    (e : ReciprocityCandidate F) {c : SupercuspidalMap.{uF, uP, uA} F}
    (hc : SupercuspidalRankOneCompatibility F e c)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) (χ : QuasiCharacter F) :
    IsSupercuspidalCharacterTwist F χ (c 1 σ)
      (c 1 (FiniteRepresentation.continuousIrreducibleTwistEquiv
        (LocalFactor.RankOne.weilCharacter F e χ) 1 σ)) := by
  rw [(supercuspidalRankOneCompatibility_iff_eq F e c).mp hc]
  exact rankOneReciprocityEquiv_twist F e σ χ

/-- Rank-one compatibility implies the rank-one part of dual compatibility. -/
theorem SupercuspidalRankOneCompatibility.dual_rankOne
    (e : ReciprocityCandidate F) {c : SupercuspidalMap.{uF, uP, uA} F}
    (hc : SupercuspidalRankOneCompatibility F e c)
    (σ : IrreducibleWeilClass.{uF, uP} F 1) :
    IsSupercuspidalSmoothDual F (c 1 σ)
      (c 1 (FiniteRepresentation.continuousIrreducibleDualEquiv 1 σ)) := by
  rw [(supercuspidalRankOneCompatibility_iff_eq F e c).mp hc]
  exact rankOneReciprocityEquiv_dual F e σ

end Langlands.Correspondence
