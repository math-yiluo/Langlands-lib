import Langlands.Representation.Aubert.LocalFieldGradedGrothendieck

/-! The unit identities of the local-field graded induction product. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Aubert.LocalFieldGraded

open AllFieldBZ.LocalFieldPackage.TopologicalData SmoothRep
open SmoothRep.FiniteLengthGrothendieckGroup

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)
variable (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV})

theorem inclusion_eq_of_rank_equiv {a b : ℕ} (e : a = b) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier))
      (hA : A.HasFiniteLength) (hB : B.HasFiniteLength),
      A.representation.Equiv (B.representation.comp
        (GeneralLinear.reindex (R := K.Carrier) (finCongr e)).toMonoidHom) →
      inclusion T a (ofRepresentation A hA) = inclusion T b (ofRepresentation B hB) := by
  let := T.topology
  subst b
  intro A B hA hB E
  apply congrArg (inclusion T a)
  apply ofRepresentation_eq_of_equiv hA hB
  refine E.trans (Representation.Equiv.mk (LinearEquiv.refl ℂ B) fun g => ?_)
  ext v
  change B.representation (GeneralLinear.reindex (R := K.Carrier) (finCongr rfl) g) v =
    B.representation g v
  rw [GeneralLinear.reindex_finCongr_rfl]
  rfl

private theorem leftUnit_object (b : ℕ) :
    letI := T.topology
    ∀ B : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier),
      multiplication T h (unit T) (inclusion T b (ofObject B)) =
        inclusion T b (ofObject B) := by
  let := T.topology
  intro B
  let U := (⟨unitObject T, unitObject_hasFiniteLength T⟩ :
    FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier))
  change multiplication T h (inclusion T 0 (ofObject U)) _ = _
  rw [multiplication_homogeneous, binaryProduct_objects]
  apply inclusion_eq_of_rank_equiv T (Nat.zero_add b)
  exact (binaryLeftZeroTensorEquiv T rfl (U.val, B.val)).trans
    (BinaryTensor.compEquiv (BinaryTensor.secondFactorUnitEquiv B.val.representation) _)

private theorem rightUnit_object (a : ℕ) :
    letI := T.topology
    ∀ A : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier),
      multiplication T h (inclusion T a (ofObject A)) (unit T) =
        inclusion T a (ofObject A) := by
  let := T.topology
  intro A
  let U := (⟨unitObject T, unitObject_hasFiniteLength T⟩ :
    FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier))
  change multiplication T h _ (inclusion T 0 (ofObject U)) = _
  rw [multiplication_homogeneous, binaryProduct_objects]
  apply inclusion_eq_of_rank_equiv T (Nat.add_zero a)
  exact (binaryRightZeroTensorEquiv T rfl (A.val, U.val)).trans
    (BinaryTensor.compEquiv (BinaryTensor.firstFactorUnitEquiv A.val.representation) _)

/-- The trivial rank-zero line acts by the identity on the left. -/
theorem multiplication_unit_left (x : GradedGrothendieckGroup.{uF, uV} T) :
    multiplication T h (unit T) x = x := by
  let := T.topology
  have hUnit : multiplication T h (unit T) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro b
    exact hom_ext_object ℂ (GeneralLinear b K.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} T)
      (l₁ := (multiplication T h (unit T)).comp (inclusion T b))
      (l₂ := inclusion T b) (leftUnit_object T h b)
  exact LinearMap.congr_fun hUnit x

/-- The trivial rank-zero line acts by the identity on the right. -/
theorem multiplication_unit_right (x : GradedGrothendieckGroup.{uF, uV} T) :
    multiplication T h x (unit T) = x := by
  let := T.topology
  have hUnit : (multiplication T h).flip (unit T) = LinearMap.id := by
    apply DirectSum.linearMap_ext
    intro a
    exact hom_ext_object ℂ (GeneralLinear a K.Carrier)
      (M := GradedGrothendieckGroup.{uF, uV} T)
      (l₁ := ((multiplication T h).flip (unit T)).comp (inclusion T a))
      (l₂ := inclusion T a) (rightUnit_object T h a)
  exact LinearMap.congr_fun hUnit x

end Langlands.Aubert.LocalFieldGraded
