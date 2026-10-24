import Langlands.Representation.Classification.TemperedSupportStatement
import Langlands.Representation.Jacquet.ReciprocityProof

/-! Evaluation from opposite induction to the exact normalized Jacquet action. -/

noncomputable section

namespace Langlands.OppositeSupport

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The opposite normalized Jacquet action used by the tempered support statements. -/
def jacquetAction (π : Representation ℂ (GeneralLinear n F.Carrier) V) :
    Representation ℂ (B.Levi F.Carrier)
      (Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier)) :=
  (Jacquet.normalizedActionOfModulus π
    (B.oppositeUnipotentSubgroup F.Carrier) (B.leviSubgroup F.Carrier)
    (B.leviSubgroup_le_normalizer_oppositeUnipotentSubgroup F.Carrier)
    ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹).comp
      (B.leviEquiv F.Carrier).toMonoidHom

private def inducingCharacter :
    letI := T.topology
    Induction.SmoothCharacter ℂ (B.oppositeParabolic F.Carrier) :=
  letI := T.topology
  ⟨T.oppositeParabolicHalfModulus B, T.isOpen_ker_oppositeParabolicHalfModulus B⟩

variable (π : Representation ℂ (GeneralLinear n F.Carrier) V)
variable (σ : Representation ℂ (B.Levi F.Carrier) W)

/-- Evaluation at the identity of an actual intertwiner into opposite induction. -/
def evaluation (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ)) :
    V →ₗ[ℂ] W :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Jacquet.CharacterReciprocity.evaluation (B.oppositeParabolic F.Carrier) π
    (σ.comp (B.oppositeLeviProjection F.Carrier)) (inducingCharacter T B) j

/-- Evaluation of a translated vector is the induced function's value there. -/
theorem evaluation_translate
    (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ))
    (g : GeneralLinear n F.Carrier) (v : V) :
    evaluation T B π σ j (π g v) = (j v).1.1 g := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  exact Jacquet.CharacterReciprocity.evaluation_translate _ _ _ _ j g v

/-- Evaluation is constant on opposite-unipotent orbits. -/
theorem evaluation_unipotent
    (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ))
    (u : B.oppositeUnipotentSubgroup F.Carrier) (v : V) :
    evaluation T B π σ j (π u v) = evaluation T B π σ j v := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  obtain ⟨a, ha, hua⟩ := u.property
  have h := Jacquet.CharacterReciprocity.evaluation_covariance
    (B.oppositeParabolic F.Carrier) π (σ.comp (B.oppositeLeviProjection F.Carrier))
    (inducingCharacter T B) j a v
  change B.oppositeLeviProjection F.Carrier a = 1 at ha
  change evaluation T B π σ j (π a v) =
    (T.oppositeParabolicHalfModulus B a : ℂ) •
      σ (B.oppositeLeviProjection F.Carrier a) (evaluation T B π σ j v) at h
  have hu : (a : GeneralLinear n F.Carrier) = (u : GeneralLinear n F.Carrier) := hua
  rw [← hu]
  simpa only [T.oppositeParabolicHalfModulus_apply, ha, map_one,
    inv_one, Units.val_one, one_smul, Module.End.one_apply] using h

/-- Descend evaluation through the actual opposite-unipotent coinvariants. -/
def descendedEvaluation
    (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ)) :
    Jacquet.Coinvariants π (B.oppositeUnipotentSubgroup F.Carrier) →ₗ[ℂ] W :=
  Jacquet.lift π (B.oppositeUnipotentSubgroup F.Carrier)
    (evaluation T B π σ j) (by
      intro u
      ext v
      exact evaluation_unipotent T B π σ j u v)

/-- The inverse half of the opposite modulus is the positive upper half. -/
theorem jacquetAction_mk (m : B.Levi F.Carrier) (v : V) :
    jacquetAction T B π m (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) v) =
      (T.leviHalfModulus B m : ℂ) •
        Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier)
          (π (B.leviEmbedding F.Carrier m) v) := by
  change (Jacquet.inverseHalfCharacter
      ((T.leviModulus B).comp (B.leviEquiv F.Carrier).symm.toMonoidHom)⁻¹
      (B.leviEquiv F.Carrier m) : ℂ) •
      Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier)
        (π (B.leviEmbedding F.Carrier m) v) = _
  congr 1
  simp [Jacquet.inverseHalfCharacter, Jacquet.complexCharacter,
    Jacquet.positiveHalfCharacter, PadicField.TopologicalData.leviHalfModulus]

/-- The actual normalized opposite Jacquet map attached to an induced intertwiner. -/
def jacquetEvaluation
    (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ)) :
    (jacquetAction T B π).IntertwiningMap σ where
  toLinearMap := descendedEvaluation T B π σ j
  isIntertwining' m := by
    ext v
    change descendedEvaluation T B π σ j
      (jacquetAction T B π m (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) v)) = _
    rw [jacquetAction_mk, map_smul]
    change (T.leviHalfModulus B m : ℂ) •
      evaluation T B π σ j (π (B.leviEmbedding F.Carrier m) v) =
        σ m (evaluation T B π σ j v)
    let := T.topology
    let := T.generalLinearTopologicalGroup n
    have h := Jacquet.CharacterReciprocity.evaluation_covariance
      (B.oppositeParabolic F.Carrier) π (σ.comp (B.oppositeLeviProjection F.Carrier))
      (inducingCharacter T B) j (B.oppositeLeviInParabolic F.Carrier m) v
    change evaluation T B π σ j (π (B.leviEmbedding F.Carrier m) v) =
      (T.oppositeParabolicHalfModulus B (B.oppositeLeviInParabolic F.Carrier m) : ℂ) •
        σ (B.oppositeLeviProjection F.Carrier (B.oppositeLeviInParabolic F.Carrier m))
          (evaluation T B π σ j v) at h
    rw [h]
    simp [smul_smul]

@[simp]
theorem jacquetEvaluation_mk
    (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ)) (v : V) :
    jacquetEvaluation T B π σ j
      (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) v) = (j v).1.1 1 := rfl

/-- A nonzero induced intertwiner has nonzero descended evaluation. -/
theorem jacquetEvaluation_ne_zero
    (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ)) (hj : j ≠ 0) :
    jacquetEvaluation T B π σ j ≠ 0 := by
  intro h
  apply hj
  ext v g
  change (j v).1.1 g = 0
  rw [← evaluation_translate T B π σ j g v]
  change jacquetEvaluation T B π σ j
    (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π g v)) = 0
  rw [h]
  rfl

/-- A nonzero map into opposite induction yields a surjective Jacquet map when
its inducing representation is irreducible. -/
theorem jacquetEvaluation_surjective
    (hσ : Representation.IsIrreducible σ)
    (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ)) (hj : j ≠ 0) :
    Function.Surjective (jacquetEvaluation T B π σ j) := by
  let := hσ
  exact (Representation.IsIrreducible.surjective_or_eq_zero
    (jacquetEvaluation T B π σ j)).resolve_right
      (jacquetEvaluation_ne_zero T B π σ j hj)

/-- The opposite-support injection supplies the exact Jacquet occurrence used
in the discrete-series summand statement. No temperedness or analytic input
is needed for this algebraic implication. -/
theorem occurs_of_embedding
    (hπ : Representation.IsIrreducible π) (hσ : Representation.IsIrreducible σ)
    (j : letI := T.topology
      π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ))
    (hj : Function.Injective j) :
    ∃ S : Subrepresentation (jacquetAction T B π),
      ∃ q : S.toRepresentation.IntertwiningMap σ, Function.Surjective q := by
  let := hπ
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π.asModule
  have hj0 : j ≠ 0 := by
    intro hz
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    apply hj
    rw [hz]
    rfl
  let S : Subrepresentation (jacquetAction T B π) := ⊤
  let inclusion : S.toRepresentation.IntertwiningMap (jacquetAction T B π) :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let q := (jacquetEvaluation T B π σ j).comp inclusion
  refine ⟨S, q, ?_⟩
  intro w
  obtain ⟨v, hv⟩ := jacquetEvaluation_surjective T B π σ hσ j hj0 w
  exact ⟨⟨v, Submodule.mem_top⟩, hv⟩

end Langlands.OppositeSupport
