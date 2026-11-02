import Langlands.Representation.Aubert.GradedGrothendieck

/-! Unit identities for the actual all-ranks graded induction product. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

open SmoothRep.FiniteLengthGrothendieckGroup

/-- An actual equivalence after the published rank reindex identifies the
homogeneous classes in the direct sum. -/
theorem gradedInclusion_eq_of_rank_equiv {a b : ℕ} (h : a = b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
      (hA : A.HasFiniteLength) (hB : B.HasFiniteLength),
      A.representation.Equiv (B.representation.comp
        (GeneralLinear.reindex (R := F.Carrier) (finCongr h)).toMonoidHom) →
      gradedInclusion F T a (ofRepresentation A hA) =
        gradedInclusion F T b (ofRepresentation B hB) := by
  let := T.topology
  subst b
  intro A B hA hB e
  apply congrArg (gradedInclusion F T a)
  apply ofRepresentation_eq_of_equiv hA hB
  refine e.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ B) fun g => ?_)
  ext v
  change B.representation (GeneralLinear.reindex (R := F.Carrier) (finCongr rfl) g) v =
    B.representation g v
  rw [GeneralLinear.reindex_finCongr_rfl]
  rfl

/-- Left multiplication by the genuine rank-zero line fixes every homogeneous
actual finite-length class, including rank zero. -/
theorem gradedMultiplication_unit_object
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) (b : ℕ) :
    letI := T.topology
    ∀ B : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier),
      gradedMultiplication F T hx (gradedUnit F T)
          (gradedInclusion F T b (ofObject B)) =
        gradedInclusion F T b (ofObject B) := by
  let := T.topology
  intro B
  let U : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ
      (GeneralLinear 0 F.Carrier) :=
    ⟨T.binaryProductUnit, binaryProductUnit_hasFiniteLength F T⟩
  change gradedMultiplication F T hx (gradedInclusion F T 0 (ofObject U)) _ = _
  rw [gradedMultiplication_homogeneous, binaryProductK0_classes]
  apply gradedInclusion_eq_of_rank_equiv F T (Nat.zero_add b)
  exact (T.binaryProductLeftUnitEquiv B.val).trans (BinaryTensor.liftEquiv _).symm

/-- Right multiplication by the genuine rank-zero line fixes every homogeneous
actual finite-length class, including rank zero. -/
theorem gradedMultiplication_object_unit
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) (a : ℕ) :
    letI := T.topology
    ∀ A : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier),
      gradedMultiplication F T hx (gradedInclusion F T a (ofObject A))
          (gradedUnit F T) =
        gradedInclusion F T a (ofObject A) := by
  let := T.topology
  intro A
  let U : SmoothRep.FiniteLengthObject.{0, uF, max uF uV} ℂ
      (GeneralLinear 0 F.Carrier) :=
    ⟨T.binaryProductUnit, binaryProductUnit_hasFiniteLength F T⟩
  change gradedMultiplication F T hx _ (gradedInclusion F T 0 (ofObject U)) = _
  rw [gradedMultiplication_homogeneous, binaryProductK0_classes]
  apply gradedInclusion_eq_of_rank_equiv F T (Nat.add_zero a)
  exact (T.binaryProductRightUnitEquiv A.val).trans (BinaryTensor.liftEquiv _).symm

/-- The actual rank-zero line acts as a left unit on every graded exact class. -/
theorem gradedMultiplication_unit_left
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    letI := T.topology
    ∀ x, gradedMultiplication F T hx (gradedUnit F T) x = x := by
  let := T.topology
  have h : gradedMultiplication F T hx (gradedUnit F T) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro b
    exact hom_ext_object ℂ (GeneralLinear b F.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} F T)
      (l₁ := (gradedMultiplication F T hx (gradedUnit F T)).comp (gradedInclusion F T b))
      (l₂ := gradedInclusion F T b) (gradedMultiplication_unit_object F T hx b)
  exact LinearMap.congr_fun h

/-- The actual rank-zero line acts as a right unit on every graded exact class. -/
theorem gradedMultiplication_unit_right
    (hx : BinaryProductExactnessStatement.{uF, uV} F T) :
    letI := T.topology
    ∀ x, gradedMultiplication F T hx x (gradedUnit F T) = x := by
  let := T.topology
  have h : (gradedMultiplication F T hx).flip (gradedUnit F T) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro a
    exact hom_ext_object ℂ (GeneralLinear a F.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} F T)
      (l₁ := ((gradedMultiplication F T hx).flip (gradedUnit F T)).comp (gradedInclusion F T a))
      (l₂ := gradedInclusion F T a) (gradedMultiplication_object_unit F T hx a)
  exact LinearMap.congr_fun h

end Langlands.Aubert
