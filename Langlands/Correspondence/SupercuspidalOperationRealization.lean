import Langlands.Correspondence.OperationCompatibility
import Langlands.Representation.Classification.SupercuspidalContragredient
import Langlands.Representation.Classification.SupercuspidalContragredientProof
import Langlands.Representation.Twist.ContinuousCharacterProof

/-!
# Realization of the supercuspidal twist and dual relations

Canonical endpoint operations obtained from the published class operations and
closure proofs. Compatibility with a correspondence remains an explicit condition.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance operationRealizationFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance operationRealizationGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance operationRealizationGLTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Every continuous field quasi-character gives an open-kernel determinant
character, without any unitarity hypothesis. -/
theorem isOpen_ker_determinantQuasiCharacter (n : ℕ+) (χ : QuasiCharacter F) :
    IsOpen ((determinantQuasiCharacter F n χ).ker :
      Set (GeneralLinear (n : ℕ) F.Carrier)) := by
  let := F.canonicalGeneralLinearNonarchimedean (n : ℕ)
  exact isOpen_ker_of_continuous_complex_character _
    (χ.continuous.comp (F.canonicalTopologicalData.generalLinearDeterminant n).continuous)

/-- The published supercuspidal class twist, specialized to the endpoint topology. -/
def supercuspidalTwist {n : ℕ+} (χ : QuasiCharacter F) :
    SupercuspidalAutomorphicClass.{uF, uA} F n →
      SupercuspidalAutomorphicClass.{uF, uA} F n :=
  GeneralLinear.SupercuspidalClass.twist (determinantQuasiCharacter F n χ)
    (isOpen_ker_determinantQuasiCharacter F n χ)
    (GeneralLinear.ker_determinant_le_ker_comp χ.toMonoidHom)

/-- The actual endpoint twist relation is the graph of the canonical map. -/
theorem isSupercuspidalCharacterTwist_iff_eq_supercuspidalTwist {n : ℕ+}
    (χ : QuasiCharacter F) (π π' : SupercuspidalAutomorphicClass.{uF, uA} F n) :
    IsSupercuspidalCharacterTwist F χ π π' ↔ π' = supercuspidalTwist F χ π :=
  isSupercuspidalCharacterTwist_iff_eq_twist F χ
    (isOpen_ker_determinantQuasiCharacter F n χ) π π'

/-- Twisting by the identity quasi-character fixes every class. -/
@[simp]
theorem supercuspidalTwist_one {n : ℕ+}
    (π : SupercuspidalAutomorphicClass.{uF, uA} F n) :
    supercuspidalTwist F 1 π = π := by
  exact GeneralLinear.SupercuspidalClass.twist_one _ π

/-- Successive endpoint twists multiply their field quasi-characters. -/
theorem supercuspidalTwist_twist {n : ℕ+} (χ η : QuasiCharacter F)
    (π : SupercuspidalAutomorphicClass.{uF, uA} F n) :
    supercuspidalTwist F χ (supercuspidalTwist F η π) =
      supercuspidalTwist F (χ * η) π := by
  exact GeneralLinear.SupercuspidalClass.twist_twist _ _
    (isOpen_ker_determinantQuasiCharacter F n χ)
    (isOpen_ker_determinantQuasiCharacter F n η)
    (isOpen_ker_determinantQuasiCharacter F n (χ * η)) _ _ π

/-- Twisting is an equivalence, with the inverse quasi-character as inverse. -/
def supercuspidalTwistEquiv (n : ℕ+) (χ : QuasiCharacter F) :
    SupercuspidalAutomorphicClass.{uF, uA} F n ≃
      SupercuspidalAutomorphicClass.{uF, uA} F n where
  toFun := supercuspidalTwist F χ
  invFun := supercuspidalTwist F χ⁻¹
  left_inv π := by
    rw [supercuspidalTwist_twist, inv_mul_cancel, supercuspidalTwist_one]
  right_inv π := by
    rw [supercuspidalTwist_twist, mul_inv_cancel, supercuspidalTwist_one]

/-- Every endpoint twist relation has exactly one output. -/
theorem existsUnique_supercuspidalCharacterTwist {n : ℕ+} (χ : QuasiCharacter F)
    (π : SupercuspidalAutomorphicClass.{uF, uA} F n) :
    ∃! π', IsSupercuspidalCharacterTwist F χ π π' := by
  refine ⟨supercuspidalTwist F χ π, ?_, ?_⟩
  · exact (isSupercuspidalCharacterTwist_iff_eq_supercuspidalTwist F χ _ _).mpr rfl
  · intro π' hπ'
    exact (isSupercuspidalCharacterTwist_iff_eq_supercuspidalTwist F χ _ _).mp hπ'

/-- The published contragredient, with its closure hypothesis discharged by the
published all-field supercuspidal contragredient theorem. -/
def supercuspidalDual {n : ℕ+} :
    SupercuspidalAutomorphicClass.{uF, uA} F n →
      SupercuspidalAutomorphicClass.{uF, uA} F n :=
  PadicField.SupercuspidalClass.contragredient GeneralLinear.supercuspidalContragredient

/-- The canonical endpoint dual is involutive. -/
theorem supercuspidalDual_involutive (n : ℕ+) :
    Function.Involutive (supercuspidalDual.{uF, uA} F (n := n)) :=
  PadicField.SupercuspidalClass.contragredient_involutive
    GeneralLinear.supercuspidalContragredient

/-- Smooth duality as a canonical equivalence of the endpoint class space. -/
def supercuspidalDualEquiv (n : ℕ+) :
    SupercuspidalAutomorphicClass.{uF, uA} F n ≃
      SupercuspidalAutomorphicClass.{uF, uA} F n where
  toFun := supercuspidalDual F
  invFun := supercuspidalDual F
  left_inv := supercuspidalDual_involutive F n
  right_inv := supercuspidalDual_involutive F n

/-- The full automorphic smooth-dual relation is the graph of the published
contragredient on classes. -/
theorem isSmoothDual_iff_eq_contragredient {n : ℕ+}
    (π π' : AutomorphicClass.{uF, uA} F n) :
    IsSmoothDual F π π' ↔ π' = SmoothDualClass.contragredient
      (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n) π := by
  constructor
  · rintro ⟨A, B, rfl, rfl, e⟩
    exact ((SmoothDualClass.contragredient_mk_eq_mk_iff
      (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n) A B).mpr e).symm
  · rintro rfl
    obtain ⟨A, rfl⟩ := automorphicClass_has_representative F π
    exact ⟨A, IrreducibleAdmissibleRep.contragredient
      (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n) A,
      rfl, rfl, ⟨equivOfRepresentationEq rfl⟩⟩

/-- Forgetting supercuspidality commutes with the canonical endpoint dual. -/
theorem supercuspidalToAutomorphic_dual {n : ℕ+}
    (π : SupercuspidalAutomorphicClass.{uF, uA} F n) :
    supercuspidalToAutomorphic F (supercuspidalDual F π) =
      SmoothDualClass.contragredient
        (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData n)
        (supercuspidalToAutomorphic F π) :=
  GeneralLinear.SupercuspidalClass.toSmoothDualClass_contragredient _ _ π

/-- The restricted smooth-dual relation is exactly the graph of the canonical dual. -/
theorem isSupercuspidalSmoothDual_iff_eq_supercuspidalDual {n : ℕ+}
    (π π' : SupercuspidalAutomorphicClass.{uF, uA} F n) :
    IsSupercuspidalSmoothDual F π π' ↔ π' = supercuspidalDual F π := by
  unfold IsSupercuspidalSmoothDual
  rw [isSmoothDual_iff_eq_contragredient, ← supercuspidalToAutomorphic_dual]
  exact (supercuspidalToAutomorphic_injective F).eq_iff

/-- Every endpoint smooth-dual relation has exactly one output. -/
theorem existsUnique_supercuspidalSmoothDual {n : ℕ+}
    (π : SupercuspidalAutomorphicClass.{uF, uA} F n) :
    ∃! π', IsSupercuspidalSmoothDual F π π' := by
  refine ⟨supercuspidalDual F π, ?_, ?_⟩
  · exact (isSupercuspidalSmoothDual_iff_eq_supercuspidalDual F _ _).mpr rfl
  · intro π' hπ'
    exact (isSupercuspidalSmoothDual_iff_eq_supercuspidalDual F _ _).mp hπ'

/-- The endpoint smooth-dual relation is symmetric. -/
theorem isSupercuspidalSmoothDual_symm {n : ℕ+}
    {π π' : SupercuspidalAutomorphicClass.{uF, uA} F n}
    (h : IsSupercuspidalSmoothDual F π π') :
    IsSupercuspidalSmoothDual F π' π := by
  apply (isSupercuspidalSmoothDual_iff_eq_supercuspidalDual F _ _).mpr
  rw [(isSupercuspidalSmoothDual_iff_eq_supercuspidalDual F _ _).mp h,
    supercuspidalDual_involutive F n π]

/-- Twist compatibility is precisely the equation commuting with canonical twists. -/
theorem supercuspidalTwistCompatibility_iff (e : ReciprocityCandidate F)
    (c : SupercuspidalMap.{uF, uP, uA} F) :
    SupercuspidalTwistCompatibility F e c ↔
      ∀ n (σ : IrreducibleWeilClass.{uF, uP} F n) (χ : QuasiCharacter F),
        c n (FiniteRepresentation.continuousIrreducibleTwistEquiv
          (LocalFactor.RankOne.weilCharacter F e χ) (n : ℕ) σ) =
            supercuspidalTwist F χ (c n σ) := by
  unfold SupercuspidalTwistCompatibility
  exact forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun χ =>
    isSupercuspidalCharacterTwist_iff_eq_supercuspidalTwist F χ _ _

/-- Dual compatibility is precisely the equation commuting with canonical duals. -/
theorem supercuspidalDualCompatibility_iff
    (c : SupercuspidalMap.{uF, uP, uA} F) :
    SupercuspidalDualCompatibility F c ↔
      ∀ n (σ : IrreducibleWeilClass.{uF, uP} F n),
        c n (FiniteRepresentation.continuousIrreducibleDualEquiv (n : ℕ) σ) =
          supercuspidalDual F (c n σ) := by
  unfold SupercuspidalDualCompatibility
  exact forall_congr' fun _ => forall_congr' fun _ =>
    isSupercuspidalSmoothDual_iff_eq_supercuspidalDual F _ _

end Langlands.Correspondence
