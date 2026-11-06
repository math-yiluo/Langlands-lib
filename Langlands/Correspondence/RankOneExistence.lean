import Langlands.Correspondence.RankOneComparison
import Langlands.Correspondence.AssemblyEpsilonSystemHelpers
import Langlands.Representation.GodementJacquet.TateCharacterReduction
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Group.GL.CompactOpen
import Langlands.Weil.Representation.CharacterLine

/-!
# Actual rank-one supercuspidal character classes

The scalar model is lifted to the independently specified carrier universe.
The converse uses the published actual GL₁ character classification.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA uG uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rankOneExistenceFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance rankOneExistenceGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance rankOneExistenceGLTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

private theorem rankOneCharacterLine_smooth (χ : QuasiCharacter F) :
    IsSmooth (FiniteRepresentation.characterLine.{uF, uA}
      (determinantQuasiCharacter F 1 χ)).representation := by
  let := F.canonicalGeneralLinearNonarchimedean 1
  let χdet : GeneralLinear 1 F.Carrier →* ℂˣ := determinantQuasiCharacter F 1 χ
  have hcont : Continuous χdet :=
    χ.continuous.comp
      (F.canonicalTopologicalData.generalLinearDeterminant 1).continuous
  have hopen : IsOpen (χdet.ker : Set (GeneralLinear 1 F.Carrier)) :=
    isOpen_ker_of_continuous_complex_character χdet hcont
  intro v
  refine ⟨⟨χdet.ker, hopen⟩, ?_⟩
  intro g
  have hg : determinantQuasiCharacter F 1 χ g.val = 1 :=
    g.property
  change (determinantQuasiCharacter F 1 χ g.val : ℂ) • v = v
  rw [hg, Units.val_one, one_smul]

/-- In GL₁ the actual supercuspidal condition is exactly admissibility:
there is no proper block parabolic. -/
theorem isSupercuspidal_rankOne_iff
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear 1 F.Carrier) V) :
    GeneralLinear.IsSupercuspidal ρ ↔ IsAdmissible ρ := by
  refine ⟨And.left, fun hρ => ⟨hρ, ?_⟩⟩
  intro B hB g
  exfalso
  apply hB
  apply top_unique
  intro a _
  rw [B.mem_parabolic_iff]
  intro i j x y hij
  have hi := i.isLt
  have hj := j.isLt
  have hlen := B.length_le
  omega

/-- The lifted actual smooth character representation of GL₁. -/
def rankOneCharacterObject (χ : QuasiCharacter F) :
    SmoothRep.{0, uF, uA} ℂ (GeneralLinear 1 F.Carrier) :=
  SmoothRep.of
    (FiniteRepresentation.characterLine.{uF, uA}
      (determinantQuasiCharacter F 1 χ)).representation
    (rankOneCharacterLine_smooth F χ)

/-- A continuous field character gives an actual irreducible supercuspidal
object, with no carrier-universe identification. -/
def rankOneSupercuspidalObject (χ : QuasiCharacter F) :
    GeneralLinear.SupercuspidalRep.{uF, uA} (F := F.Carrier) (n := 1) := by
  letI : Module.Finite ℂ (rankOneCharacterObject.{uF, uA} F χ) := by
    change Module.Finite ℂ (ULift.{uA} ℂ)
    infer_instance
  exact ⟨rankOneCharacterObject F χ, FiniteRepresentation.characterLine_isIrreducible _,
    (isSupercuspidal_rankOne_iff F _).mpr
      ⟨rankOneCharacterLine_smooth F χ, fun _ => inferInstance⟩⟩

/-- The genuine supercuspidal class of the lifted character line. -/
def rankOneSupercuspidalClass (χ : QuasiCharacter F) :
    SupercuspidalAutomorphicClass.{uF, uA} F 1 :=
  GeneralLinear.SupercuspidalRep.isoClass (rankOneSupercuspidalObject F χ)

/-- The constructed class satisfies the existing scalar character relation. -/
theorem rankOneSupercuspidalClass_spec (χ : QuasiCharacter F) :
    IsSupercuspidalRankOneCharacter F χ
      (rankOneSupercuspidalClass.{uF, uA} F χ) := by
  refine ⟨(rankOneSupercuspidalObject F χ).toIrreducibleAdmissible, rfl, ?_⟩
  exact ⟨(FiniteRepresentation.characterLineEquiv
    (determinantQuasiCharacter F 1 χ)).symm⟩

/-- Every actual rank-one automorphic class is represented by a continuous
field character, by the published admissible irreducible GL₁ classification. -/
theorem exists_rankOneAutomorphicCharacter (π : AutomorphicClass.{uF, uA} F 1) :
    ∃ χ : QuasiCharacter F, IsRankOneCharacter F χ π := by
  obtain ⟨A, hA⟩ := automorphicClass_has_representative F π
  obtain ⟨χ, ⟨e⟩⟩ := GodementJacquet.exists_tateCharacterModel
    A.obj.representation A.property.2 A.property.1
  exact ⟨χ, A, hA, ⟨e.symm⟩⟩

/-- Every rank-one supercuspidal class is the constructed class of some
continuous field character. -/
theorem rankOneSupercuspidalClass_surjective :
    Function.Surjective (rankOneSupercuspidalClass.{uF, uA} F) := by
  intro π
  obtain ⟨χ, hχ⟩ := exists_rankOneAutomorphicCharacter F (supercuspidalToAutomorphic F π)
  exact ⟨χ, IsSupercuspidalRankOneCharacter.class_unique F
    (rankOneSupercuspidalClass_spec F χ) hχ⟩

end Langlands.Correspondence
