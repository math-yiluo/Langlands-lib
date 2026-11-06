import Langlands.Correspondence.RankOneReciprocityBijection

/-! # Determinant and central action for the actual rank-one correspondence -/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rankOneDeterminantFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- The scalar matrix acts by the field character on every actual
rank-one class realizing that character. -/
theorem IsRankOneCharacter.centralActsBy {χ : QuasiCharacter F}
    {π : AutomorphicClass.{uF, uA} F 1}
    (hπ : IsRankOneCharacter F χ π) (a : F.Carrierˣ) :
    CentralActsBy F π a (χ a) := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hπ
  refine ⟨A, hA, ?_⟩
  intro v
  obtain ⟨x, rfl⟩ := eA.toLinearEquiv.surjective v
  have ha : determinantQuasiCharacter F 1 χ (GeneralLinear.scalar a) = χ a := by
    change χ (Matrix.GeneralLinearGroup.det
      (Matrix.GeneralLinearGroup.scalar (Fin 1) a)) = χ a
    rw [Matrix.GeneralLinearGroup.det_scalar]
    simp
  calc
    A.obj.representation (GeneralLinear.scalar a) (eA x) =
        eA (Langlands.characterRepresentation (determinantQuasiCharacter F 1 χ)
          (GeneralLinear.scalar a) x) :=
      (Representation.IntertwiningMap.isIntertwining _ _
        eA.toIntertwiningMap (GeneralLinear.scalar a) x).symm
    _ = (χ a : ℂ) • eA x := by
      change eA ((determinantQuasiCharacter F 1 χ (GeneralLinear.scalar a) : ℂ) • x) = _
      rw [ha, map_smul]

/-- The determinant of an actual rank-one Weil class is its scalar character. -/
theorem IsRankOneWeilCharacter.determinant_eq
    {χ : Weil.Local.localWeilGroup F →* ℂˣ}
    {σ : IrreducibleWeilClass.{uF, uP} F 1}
    (hσ : IsRankOneWeilCharacter F χ σ) :
    irreducibleWeilDeterminant F σ = χ := by
  obtain ⟨A, hA, ⟨eA⟩⟩ := hσ
  change FiniteRepresentation.determinantCharacterClass (weilClassForget F σ) = χ
  rw [← hA]
  change FiniteRepresentation.determinantCharacter A = χ
  rw [← FiniteRepresentation.determinantCharacter_eq
    (A := FiniteRepresentation.of (Langlands.characterRepresentation χ))
    (B := A) eA]
  ext w
  change LinearMap.det (Langlands.characterRepresentation χ w) = (χ w : ℂ)
  rw [LinearMap.det_ring]
  exact mul_one _

/-- The actual continuous central character of a supercuspidal GL₁ class. -/
def rankOneSupercuspidalCentralCharacter
    (π : SupercuspidalAutomorphicClass.{uF, uA} F 1) : QuasiCharacter F :=
  (rankOneSupercuspidalCharacterEquiv F).symm π

/-- The recovered character realizes the original actual class. -/
theorem rankOneSupercuspidalCentralCharacter_spec
    (π : SupercuspidalAutomorphicClass.{uF, uA} F 1) :
    IsSupercuspidalRankOneCharacter F (rankOneSupercuspidalCentralCharacter F π) π := by
  have hπ : rankOneSupercuspidalClass F (rankOneSupercuspidalCentralCharacter F π) = π :=
    (rankOneSupercuspidalCharacterEquiv F).apply_symm_apply π
  have h := rankOneSupercuspidalClass_spec F (rankOneSupercuspidalCentralCharacter F π)
  rw [hπ] at h
  exact h

/-- The recovered continuous character gives the actual central scalar action. -/
theorem rankOneSupercuspidalCentralCharacter_central
    (π : SupercuspidalAutomorphicClass.{uF, uA} F 1) (a : F.Carrierˣ) :
    SupercuspidalCentralActsBy F π a (rankOneSupercuspidalCentralCharacter F π a) :=
  IsRankOneCharacter.centralActsBy F (rankOneSupercuspidalCentralCharacter_spec F π) a

/-- The constructed rank-one bijection satisfies the endpoint's actual
determinant and central-action relation. -/
theorem rankOneReciprocityEquiv_central (e : ReciprocityCandidate F)
    (σ : IrreducibleWeilClass.{uF, uP} F 1)
    (w : Weil.Local.localWeilGroup F) :
    SupercuspidalCentralActsBy F (rankOneReciprocityEquiv.{uF, uP, uA} F e σ)
      (reciprocityHom F e w) (irreducibleWeilDeterminant F σ w) := by
  obtain ⟨χ, hσ⟩ := exists_rankOneWeilFieldCharacter F e σ
  rw [IsRankOneWeilCharacter.determinant_eq F hσ, weilCharacter_eq_comp]
  exact IsRankOneCharacter.centralActsBy F
    (rankOneReciprocityEquiv_spec F e χ σ hσ) (reciprocityHom F e w)

/-- Rank-one compatibility already implies the rank-one part of determinant
compatibility, for any family on the actual endpoint class spaces. -/
theorem SupercuspidalRankOneCompatibility.determinant_rankOne
    (e : ReciprocityCandidate F) {c : SupercuspidalMap.{uF, uP, uA} F}
    (hc : SupercuspidalRankOneCompatibility F e c)
    (σ : IrreducibleWeilClass.{uF, uP} F 1)
    (w : Weil.Local.localWeilGroup F) :
    SupercuspidalCentralActsBy F (c 1 σ) (reciprocityHom F e w)
      (irreducibleWeilDeterminant F σ w) := by
  rw [(supercuspidalRankOneCompatibility_iff_eq F e c).mp hc]
  exact rankOneReciprocityEquiv_central F e σ w

end Langlands.Correspondence
