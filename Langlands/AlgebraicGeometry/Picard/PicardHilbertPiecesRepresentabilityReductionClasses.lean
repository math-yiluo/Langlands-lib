import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionStatement
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralSheafClassTwistProof
import Langlands.AlgebraicGeometry.Picard.StructureKernelFlatBaseChange
import Langlands.AlgebraicGeometry.Picard.LineBundleDualSectionEvaluation
import Langlands.AlgebraicGeometry.Picard.Functor
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor_monoidalV2

/-! # Picard classes of invertible modules, twists and relative divisors -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction

open ProperFlatIntegralSheafClassTwist

section Classes

variable {Y : Scheme.{u}}

/-- The scheme Picard group is commutative. -/
lemma group_add_comm (x y : Group Y) : x + y = y + x :=
  @add_comm ((Group.functor.{u}).obj (op Y)) _ x y

lemma group_add_left_comm (x y z : Group Y) : x + (y + z) = y + (x + z) := by
  rw [← add_assoc, group_add_comm x y, add_assoc]

/-- The Picard class of an invertible module. -/
def icl (M : Y.Modules) (hM : Scheme.Modules.IsInvertible M) : Group Y :=
  (lineBundleOfIsInvertible M hM).classOf

lemma icl_eq_iff (M M' : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') :
    icl M hM = icl M' hM' ↔ Nonempty (M ≅ M') :=
  LineBundle.classOf_eq_iff _ _

lemma icl_lineBundle (L : LineBundle Y) (h : Scheme.Modules.IsInvertible L.obj) :
    icl L.obj h = L.classOf :=
  (LineBundle.classOf_eq_iff _ _).2 ⟨Iso.refl _⟩

lemma icl_tensor (M M' : Y.Modules) (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') (h : Scheme.Modules.IsInvertible (M ⊗ M')) :
    icl (M ⊗ M') h = icl M hM + icl M' hM' := by
  rw [icl, icl, icl, ← LineBundle.classOf_tensor
    Langlands.Scheme.Modules.pullbackTensorComparisonIsIso]
  exact (LineBundle.classOf_eq_iff _ _).2 ⟨portedTensorExplicitIso M M'⟩

lemma icl_pullback {Y' : Scheme.{u}} (φ : Y' ⟶ Y) (M : Y.Modules)
    (hM : Scheme.Modules.IsInvertible M)
    (h : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback φ).obj M)) :
    icl ((Scheme.Modules.pullback φ).obj M) h = Group.pullback φ (icl M hM) := by
  rw [icl, icl, Group.pullback_lineBundle_classOf]
  exact (LineBundle.classOf_eq_iff _ _).2 ⟨Iso.refl _⟩

lemma icl_unit (h : Scheme.Modules.IsInvertible (SheafOfModules.unit Y.ringCatSheaf)) :
    icl (SheafOfModules.unit Y.ringCatSheaf) h = 0 := by
  rw [← LineBundle.classOf_trivial Y]
  exact (LineBundle.classOf_eq_iff _ _).2 ⟨Iso.refl _⟩

lemma isInvertible_tensor {M M' : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') : Scheme.Modules.IsInvertible (M ⊗ M') :=
  Scheme.Modules.IsInvertible.tensor_monoidalV2 hM hM'

/-- The twists `L ⊗ P^{⊗ m}`, written as in the statements. -/
abbrev twist (L P : Y.Modules) (m : ℕ) : Y.Modules :=
  Nat.rec (motive := fun _ => Y.Modules) L (fun _ M => M ⊗ P) m

lemma isInvertible_twist {L P : Y.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hP : Scheme.Modules.IsInvertible P) (m : ℕ) :
    Scheme.Modules.IsInvertible (twist L P m) := by
  induction m with
  | zero => exact hL
  | succ n ih => exact isInvertible_tensor ih hP

lemma icl_twist {L P : Y.Modules} (hL : Scheme.Modules.IsInvertible L)
    (hP : Scheme.Modules.IsInvertible P) (m : ℕ)
    (h : Scheme.Modules.IsInvertible (twist L P m)) :
    icl (twist L P m) h = icl L hL + m • icl P hP := by
  induction m with
  | zero => simp
  | succ n ih =>
    change icl (twist L P n ⊗ P) h = _
    rw [icl_tensor _ _ (isInvertible_twist hL hP n) hP, ih (isInvertible_twist hL hP n),
      succ_nsmul, add_assoc]

/-- Isomorphic invertible modules from class equations: `M ≅ M' ⊗ N`. -/
lemma nonempty_iso_tensor_of_icl {M M' N : Y.Modules} (hM : Scheme.Modules.IsInvertible M)
    (hM' : Scheme.Modules.IsInvertible M') (hN : Scheme.Modules.IsInvertible N)
    (h : icl M hM = icl M' hM' + icl N hN) : Nonempty (M ≅ M' ⊗ N) := by
  rw [← icl_tensor M' N hM' hN (isInvertible_tensor hM' hN)] at h
  exact (icl_eq_iff _ _ _ _).1 h

/-- The class of the dual line bundle is the negative class. -/
lemma classOf_dual (L : LineBundle Y) : L.dual.classOf = -L.classOf := by
  have h : (LineBundle.tensor Langlands.Scheme.Modules.pullbackTensorComparisonIsIso
      L L.dual).classOf = (LineBundle.trivial Y).classOf := by
    have hI : IsIso (Langlands.Scheme.Modules.dualTensorEval L.obj) :=
      Langlands.Scheme.Modules.isIso_dualTensorEval L.property
    exact (LineBundle.classOf_eq_iff _ _).2
      ⟨@asIso _ _ _ _ (Langlands.Scheme.Modules.dualTensorEval L.obj) hI⟩
  rw [LineBundle.classOf_tensor, LineBundle.classOf_trivial] at h
  exact eq_neg_of_add_eq_zero_right h

end Classes

end Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesReduction
