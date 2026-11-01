import Langlands.Representation.Aubert.AlternatingOperator
import Langlands.Representation.Smooth.FiniteLengthGrothendieckTwist
import Langlands.Representation.Parabolic.CharacterTwistEquivalences
import Langlands.Representation.Classification.SupercuspidalTwist

/-!
# Actual character twists and the unadjusted Aubert operator

The actual normalized induction and Jacquet comparisons give identities on the
full exact finite-length smooth Grothendieck group. Their alternating sum
commutes with every smooth ambient character killing the block radicals.
Characters pulled back along the actual determinant satisfy that condition.
-/

noncomputable section

namespace Langlands.Aubert

universe uF uV

open Parabolic SmoothRep

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual scalar twisting on the saturated exact smooth `GL_n` quotient. -/
def characterTwistK0 (n : ℕ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier) →
      GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier →ₗ[ℤ]
        GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} n F.Carrier :=
  letI := T.topology
  fun χ => FiniteLengthGrothendieckGroup.twist χ.toMonoidHom χ.isOpen_ker

/-- The same twist restricted to the actual embedded product Levi. -/
def leviCharacterTwistK0 {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier) →
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
        B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro χ
  exact FiniteLengthGrothendieckGroup.twist
    (B.restrictSmoothCharacter χ).toMonoidHom (B.restrictSmoothCharacter χ).isOpen_ker

/-- Actual normalized Jacquet restriction commutes with a radical-trivial
ambient twist on every virtual finite-length class. -/
theorem normalizedJacquetK0_characterTwist {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ∀ (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier)),
      B.unipotentSubgroup F.Carrier ≤ χ.toMonoidHom.ker →
        (normalizedJacquetK0.{uF, uV} F T B).comp (characterTwistK0 F T n χ) =
          (leviCharacterTwistK0 F T B χ).comp (normalizedJacquetK0 F T B) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro χ hN
  apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (GeneralLinear n F.Carrier)
  intro A
  let χM := B.restrictSmoothCharacter χ
  let J := T.normalizedJacquetFunctor.{uF, max uF uV} B
  have hχA := twistFunctor_preservesFiniteLength χ.toMonoidHom χ.isOpen_ker A.val A.property
  have hJA := normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B A.val A.property
  have hJχA := normalizedJacquetK0_hasFiniteLength.{uF, uV} F T B
    (A.val.twist χ.toMonoidHom χ.isOpen_ker) hχA
  have hχJA := twistFunctor_preservesFiniteLength χM.toMonoidHom χM.isOpen_ker
    (J.obj A.val) hJA
  change normalizedJacquetK0 F T B
      (FiniteLengthGrothendieckGroup.twist χ.toMonoidHom χ.isOpen_ker
        (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) =
    FiniteLengthGrothendieckGroup.twist χM.toMonoidHom χM.isOpen_ker
      (normalizedJacquetK0 F T B
        (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property))
  rw [FiniteLengthGrothendieckGroup.twist_ofRepresentation
    χ.toMonoidHom χ.isOpen_ker A.val A.property hχA]
  have hLeft :
      normalizedJacquetK0 F T B
          (FiniteLengthGrothendieckGroup.ofRepresentation
            (A.val.twist χ.toMonoidHom χ.isOpen_ker) hχA) =
        FiniteLengthGrothendieckGroup.ofRepresentation
          (J.obj (A.val.twist χ.toMonoidHom χ.isOpen_ker)) hJχA :=
    normalizedJacquetK0_finiteLengthClass F T B _ hχA hJχA
  have hRight :
      normalizedJacquetK0 F T B
          (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property) =
        FiniteLengthGrothendieckGroup.ofRepresentation (J.obj A.val) hJA :=
    normalizedJacquetK0_finiteLengthClass F T B A.val A.property hJA
  rw [hLeft, hRight, FiniteLengthGrothendieckGroup.twist_ofRepresentation
    χM.toMonoidHom χM.isOpen_ker (J.obj A.val) hJA hχJA]
  exact FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv _ _
    (B.normalizedJacquetOfCharacterTwistEquiv (T.leviModulus B)
      χ.toMonoidHom hN A.val.representation)

/-- Actual normalized induction commutes with a radical-trivial ambient twist
on every virtual finite-length class of the product Levi. -/
theorem normalizedInductionK0_characterTwist {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ∀ (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier)),
      B.unipotentSubgroup F.Carrier ≤ χ.toMonoidHom.ker →
        (characterTwistK0.{uF, uV} F T n χ).comp (normalizedInductionK0 F T B) =
          (normalizedInductionK0 F T B).comp (leviCharacterTwistK0 F T B χ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro χ hN
  apply FiniteLengthGrothendieckGroup.hom_ext_object ℂ (B.Levi F.Carrier)
  intro A
  let χM := B.restrictSmoothCharacter χ
  let I := T.normalizedParabolicInductionFunctor.{uF, max uF uV} B
  have hχA := twistFunctor_preservesFiniteLength χM.toMonoidHom χM.isOpen_ker A.val A.property
  have hIA := normalizedInductionK0_hasFiniteLength.{uF, uV} F T B A.val A.property
  have hIχA := normalizedInductionK0_hasFiniteLength.{uF, uV} F T B
    (A.val.twist χM.toMonoidHom χM.isOpen_ker) hχA
  have hχIA := twistFunctor_preservesFiniteLength χ.toMonoidHom χ.isOpen_ker
    (I.obj A.val) hIA
  change FiniteLengthGrothendieckGroup.twist χ.toMonoidHom χ.isOpen_ker
      (normalizedInductionK0 F T B
        (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property)) =
    normalizedInductionK0 F T B
      (FiniteLengthGrothendieckGroup.twist χM.toMonoidHom χM.isOpen_ker
        (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property))
  have hLeft :
      normalizedInductionK0 F T B
          (FiniteLengthGrothendieckGroup.ofRepresentation A.val A.property) =
        FiniteLengthGrothendieckGroup.ofRepresentation (I.obj A.val) hIA :=
    normalizedInductionK0_finiteLengthClass F T B A.val A.property hIA
  rw [hLeft, FiniteLengthGrothendieckGroup.twist_ofRepresentation
      χ.toMonoidHom χ.isOpen_ker (I.obj A.val) hIA hχIA,
    FiniteLengthGrothendieckGroup.twist_ofRepresentation
      χM.toMonoidHom χM.isOpen_ker A.val A.property hχA]
  have hRight :
      normalizedInductionK0 F T B
          (FiniteLengthGrothendieckGroup.ofRepresentation
            (A.val.twist χM.toMonoidHom χM.isOpen_ker) hχA) =
        FiniteLengthGrothendieckGroup.ofRepresentation
          (I.obj (A.val.twist χM.toMonoidHom χM.isOpen_ker)) hIχA :=
    normalizedInductionK0_finiteLengthClass F T B _ hχA hIχA
  rw [hRight]
  exact FiniteLengthGrothendieckGroup.ofRepresentation_eq_of_equiv _ _
    (B.normalizedInducedOfCharacterTwistEquiv (T.leviHalfCharacter B)
      χ hN A.val.representation)

/-- The unadjusted actual Aubert operator commutes with every smooth ambient
character trivial on each upper block radical, including in rank zero. -/
theorem alternatingOperator_characterTwist (n : ℕ) :
    letI := T.topology
    ∀ (χ : Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier)),
      (∀ B : GeneralLinear.BlockShape n,
        B.unipotentSubgroup F.Carrier ≤ χ.toMonoidHom.ker) →
      (alternatingOperator.{uF, uV} F T n).comp (characterTwistK0 F T n χ) =
        (characterTwistK0 F T n χ).comp (alternatingOperator F T n) := by
  let := T.topology
  intro χ hN
  let : Fintype (GeneralLinear.BlockShape n) := Fintype.ofFinite _
  apply LinearMap.ext
  intro x
  change alternatingOperator F T n (characterTwistK0 F T n χ x) =
    characterTwistK0 F T n χ (alternatingOperator F T n x)
  rw [alternatingOperator_apply, alternatingOperator_apply, map_sum]
  apply Finset.sum_congr rfl
  intro B _
  rw [map_smul]
  have hJ := LinearMap.congr_fun
    (normalizedJacquetK0_characterTwist F T B χ (hN B)) x
  have hI := LinearMap.congr_fun
    (normalizedInductionK0_characterTwist F T B χ (hN B))
    (normalizedJacquetK0 F T B x)
  change normalizedJacquetK0 F T B (characterTwistK0 F T n χ x) =
    leviCharacterTwistK0 F T B χ (normalizedJacquetK0 F T B x) at hJ
  change characterTwistK0 F T n χ
      (normalizedInductionK0 F T B (normalizedJacquetK0 F T B x)) =
    normalizedInductionK0 F T B
      (leviCharacterTwistK0 F T B χ (normalizedJacquetK0 F T B x)) at hI
  rw [hJ, hI]

/-- Pull back an open-kernel unit character along the actual continuous
determinant of `GL_n(F)`. -/
def determinantSmoothCharacter (n : ℕ) :
    letI := T.topology
    Induction.SmoothCharacter ℂ F.Carrierˣ →
      Induction.SmoothCharacter ℂ (GeneralLinear n F.Carrier) := by
  letI := T.topology
  intro η
  exact
    { toMonoidHom := η.toMonoidHom.comp (T.generalLinearDeterminant n).toMonoidHom
      isOpen_ker := η.isOpen_ker.preimage (T.generalLinearDeterminant n).continuous }

/-- Determinant characters kill every actual upper block radical. -/
theorem determinantSmoothCharacter_radical {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ∀ (η : Induction.SmoothCharacter ℂ F.Carrierˣ),
      B.unipotentSubgroup F.Carrier ≤ (determinantSmoothCharacter F T n η).toMonoidHom.ker := by
  let := T.topology
  intro η g hg
  change η.toMonoidHom (GeneralLinear.determinant g) = 1
  rw [B.determinant_eq_one_of_mem_unipotentSubgroup hg, map_one]

/-- The actual unadjusted Aubert operator commutes with every smooth
determinant-character twist on all virtual classes, in all ranks. -/
theorem alternatingOperator_determinantTwist (n : ℕ) :
    letI := T.topology
    ∀ (η : Induction.SmoothCharacter ℂ F.Carrierˣ),
      (alternatingOperator.{uF, uV} F T n).comp
          (characterTwistK0 F T n (determinantSmoothCharacter F T n η)) =
        (characterTwistK0 F T n (determinantSmoothCharacter F T n η)).comp
          (alternatingOperator F T n) := by
  let := T.topology
  intro η
  exact alternatingOperator_characterTwist F T n (determinantSmoothCharacter F T n η)
    (fun B => determinantSmoothCharacter_radical F T B η)

end Langlands.Aubert
