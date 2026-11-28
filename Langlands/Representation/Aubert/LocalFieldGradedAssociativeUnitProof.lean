import Langlands.Representation.Aubert.LocalFieldGradedAssociativeUnitStatement
import Langlands.Representation.Aubert.LocalFieldGradedInductionUnit
import Langlands.Representation.Aubert.LocalFieldGradedPositiveAssociativity
import Langlands.Representation.Smooth.JordanHolderGrothendieck

/-! Exact graded associativity by ordered regrouping and the rank-zero unit. -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open scoped MonoidAlgebra

namespace Langlands.Aubert.LocalFieldGraded

open GeneralLinear SmoothRep
open SmoothRep.FiniteLengthGrothendieckGroup

universe uF uV

variable {K : AllFieldBZ.LocalFieldPackage.{uF}} (T : K.TopologicalData)
variable (h : LocalFieldBinaryProductExactLengthStatement.{uF, uV})

private theorem rankZero_equiv_unit :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 0 K.Carrier)),
      A.IsIrreducible →
        Nonempty (A.representation.Equiv (unitObject.{uF, uV} T).representation) := by
  let := T.topology
  intro A hA
  have : Representation.IsIrreducible A.representation := hA
  have : Subsingleton (GeneralLinear 0 K.Carrier) := subsingleton_of_rank_eq_zero rfl
  have : Nontrivial A :=
    IsSimpleModule.nontrivial ℂ[GeneralLinear 0 K.Carrier] A.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  let f : (Representation.trivial ℂ (GeneralLinear 0 K.Carrier) ℂ).IntertwiningMap
      A.representation :=
    { toLinearMap := LinearMap.toSpanSingleton ℂ A v
      isIntertwining' := by
        intro g
        rw [Subsingleton.elim g 1, map_one, map_one]
        rfl }
  have hf : f ≠ 0 := by
    intro hz
    apply hv
    simpa [f] using congrArg (fun q => q 1) hz
  let e := f.ofBijective ⟨smul_left_injective ℂ hv,
    (Representation.IsIrreducible.surjective_or_eq_zero f).resolve_right hf⟩
  let eU : (Representation.trivial ℂ (GeneralLinear 0 K.Carrier) ℂ).Equiv
      (unitObject.{uF, uV} T).representation :=
    Representation.Equiv.mk (ULift.moduleEquiv (R := ℂ) (M := ℂ)).symm (fun _ => rfl)
  exact ⟨e.symm.trans eU⟩

/-- Every homogeneous exact class in rank zero maps to an integer multiple
of the actual trivial line. -/
theorem inclusion_zero_eq_smul :
    letI := T.topology
    ∀ x : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} 0 K.Carrier,
      ∃ k : ℤ, k • unit T = inclusion T 0 x := by
  let := T.topology
  intro x
  obtain ⟨f, rfl⟩ := (SmoothRep.irreducibleGrothendieckStatement.{0, uF, max uF uV} ℂ
    (GeneralLinear 0 K.Carrier)).2 x
  induction f using Finsupp.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
    obtain ⟨k, hk⟩ := hf
    obtain ⟨l, hl⟩ := hg
    exact ⟨k + l, by rw [map_add, map_add, add_smul, hk, hl]⟩
  | single c k =>
    obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
    have hs : Finsupp.single (irreducibleIsoClass A hA) k =
        k • VirtualRepresentation.generator (irreducibleIsoClass A hA) := by
      simp [VirtualRepresentation.generator]
    obtain ⟨e⟩ := rankZero_equiv_unit.{uF, uV} T A hA
    refine ⟨k, ?_⟩
    rw [hs, map_zsmul, map_zsmul,
      realizeIrreducibles_generator_irreducibleIsoClass A hA (hasFiniteLength_of_isIrreducible hA),
      ofRepresentation_eq_of_equiv _ (unitObject_hasFiniteLength T) e]
    rfl

private theorem assoc_on_objects (a b c : ℕ) :
    letI := T.topology
    ∀ (A : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear a K.Carrier))
      (B : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear b K.Carrier))
      (C : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear c K.Carrier)),
      multiplication T h
          (multiplication T h (inclusion T a (ofObject A)) (inclusion T b (ofObject B)))
          (inclusion T c (ofObject C)) =
        multiplication T h (inclusion T a (ofObject A))
          (multiplication T h (inclusion T b (ofObject B)) (inclusion T c (ofObject C))) := by
  let := T.topology
  intro A B C
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · obtain ⟨k, hk⟩ := inclusion_zero_eq_smul T (ofObject A)
    rw [← hk]
    simp only [LinearMap.map_smul₂, multiplication_unit_left]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · obtain ⟨k, hk⟩ := inclusion_zero_eq_smul T (ofObject B)
    rw [← hk]
    simp only [map_smul, LinearMap.smul_apply, multiplication_unit_left,
      multiplication_unit_right]
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · obtain ⟨k, hk⟩ := inclusion_zero_eq_smul T (ofObject C)
    rw [← hk]
    simp only [map_smul, multiplication_unit_right]
  rw [multiplication_homogeneous T h a b, binaryProduct_objects,
    multiplication_homogeneous T h b c, binaryProduct_objects,
    ofRepresentation, ofRepresentation, multiplication_homogeneous T h (a + b) c,
    multiplication_homogeneous T h a (b + c), binaryProduct_objects, binaryProduct_objects]
  exact inclusion_eq_of_rank_equiv T (Nat.add_assoc a b c) _ _ _ _
    (positiveAssociativityEquiv.{uF, uV} T ha hb hc A.val B.val C.val)

private theorem graded_ext_objects
    {L R : GradedGrothendieckGroup.{uF, uV} T →ₗ[ℤ] GradedGrothendieckGroup.{uF, uV} T}
    (hobj : letI := T.topology
      ∀ n (A : FiniteLengthObject.{0, uF, max uF uV} ℂ (GeneralLinear n K.Carrier)),
        L (inclusion T n (ofObject A)) = R (inclusion T n (ofObject A))) : L = R := by
  let := T.topology
  apply DirectSum.linearMap_ext
  intro n
  exact hom_ext_object ℂ (GeneralLinear n K.Carrier)
    (M := GradedGrothendieckGroup.{uF, uV} T)
    (l₁ := L.comp (inclusion T n)) (l₂ := R.comp (inclusion T n)) (hobj n)

/-- Normalized induction is associative on the full graded exact group. -/
theorem multiplication_assoc (x y z : GradedGrothendieckGroup.{uF, uV} T) :
    multiplication T h (multiplication T h x y) z =
      multiplication T h x (multiplication T h y z) := by
  let := T.topology
  let m := multiplication T h
  refine LinearMap.congr_fun (graded_ext_objects T
    (L := (m.flip z).comp (m.flip y)) (R := m.flip (m y z)) ?_) x
  intro a A
  let i := inclusion T a (ofObject A)
  refine LinearMap.congr_fun (graded_ext_objects T
    (L := (m.flip z).comp (m i)) (R := (m i).comp (m.flip z)) ?_) y
  intro b B
  let j := inclusion T b (ofObject B)
  refine LinearMap.congr_fun (graded_ext_objects T
    (L := m (m i j)) (R := (m i).comp (m j)) ?_) z
  intro c C
  exact assoc_on_objects T h a b c A B C

/-- The exact graded normalized product is associative and unital. -/
theorem localFieldGradedAssociativeUnit :
    LocalFieldGradedAssociativeUnitStatement.{uF, uV} := by
  intro K T h
  exact ⟨multiplication_assoc T h, multiplication_unit_left T h, multiplication_unit_right T h⟩

end Langlands.Aubert.LocalFieldGraded
