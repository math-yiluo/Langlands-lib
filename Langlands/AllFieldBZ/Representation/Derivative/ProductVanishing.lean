import Langlands.AllFieldBZ.Representation.Mirabolic.MixedProducts
import Langlands.AllFieldBZ.Representation.Parabolic.ProductInductionSubrepresentation
import Langlands.Representation.Derivative.ProductVanishing

/-!
# All-field port of `Langlands.Representation.Derivative.ProductVanishing`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.ProductVanishing` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open scoped TensorProduct
namespace Langlands.AllFieldBZ.Derivative.ProductVanishing
open Langlands.Derivative.ProductVanishing hiding isZero_of_subsingleton nontrivial_binary nontrivial_normalizedProduct subsingleton_binary subsingleton_leftMixed subsingleton_leftMixed_of_tensor subsingleton_of_isZero subsingleton_rightMixed subsingleton_rightMixed_of_tensor
open Langlands.GeneralLinear
universe uF uV

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-! ## Mixed products with a zero factor -/

theorem subsingleton_leftMixed_of_tensor {k r : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (h : Subsingleton (X.1 ⊗[ℂ] X.2)) :
    Subsingleton ((T.leftMixedProductFunctor k r).obj X) :=
  (T.leftMixedEval_injective X).subsingleton

theorem subsingleton_rightMixed_of_tensor {k r : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (h : Subsingleton (X.1 ⊗[ℂ] X.2)) :
    Subsingleton ((T.rightMixedProductFunctor k r).obj X) :=
  (T.rightMixedEval_injective X).subsingleton

theorem subsingleton_leftMixed {k r : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier))
    (h : Subsingleton X.1 ∨ Subsingleton X.2) :
    Subsingleton ((T.leftMixedProductFunctor k r).obj X) := by
  apply subsingleton_leftMixed_of_tensor
  rcases h with h | h
  · infer_instance
  · infer_instance

theorem subsingleton_rightMixed {k r : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (mirabolic r F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (h : Subsingleton X.1 ∨ Subsingleton X.2) :
    Subsingleton ((T.rightMixedProductFunctor k r).obj X) := by
  apply subsingleton_rightMixed_of_tensor
  rcases h with h | h
  · infer_instance
  · infer_instance

/-! ## Binary products -/

theorem subsingleton_of_isZero {n : ℕ}
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    (hA : letI := T.topology; IsZero A) : Subsingleton A := by
  let _ := T.topology
  refine ⟨fun v w => ?_⟩
  have h0 : ∀ u : A, u = 0 := fun u =>
    congrArg (fun φ => SmoothRep.hom φ u) (hA.eq_of_src (𝟙 A) 0)
  rw [h0 v, h0 w]

theorem isZero_of_subsingleton {n : ℕ}
    {A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)}
    (hA : Subsingleton A) : letI := T.topology; IsZero A := by
  let _ := T.topology
  rw [IsZero.iff_id_eq_zero]
  ext v
  exact Subsingleton.elim _ _

theorem subsingleton_binary {a b : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    (h : Subsingleton X.1 ∨ Subsingleton X.2) :
    Subsingleton ((T.binaryNormalizedProductFunctor a b).obj X) := by
  let _ := T.topology
  apply subsingleton_of_isZero T
  apply T.isZero_binaryNormalizedProductFunctor_obj
  rcases h with h | h
  · exact Or.inl (isZero_of_subsingleton T h)
  · exact Or.inr (isZero_of_subsingleton T h)

/-- A normalized block product of nonzero factors, with at least one block, is
nonzero. -/
theorem nontrivial_normalizedProduct {n : ℕ} (B : BlockShape n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hA : ∀ i, Nontrivial (A i)) (j : Fin B.length) :
    Nontrivial ((T.normalizedProductInductionFunctor B).obj A) := by
  let _ := T.topology
  let _ := T.generalLinearTopologicalGroup n
  have h := Parabolic.normalizedProductSlotSubrepresentation_ne_bot T B
    (fun i => (A i).representation) j (fun h => hA h) ⊤
    (top_ne_bot_of_nontrivial (A j).representation) (fun h => (A h).isSmooth)
  rw [Parabolic.normalizedProductSlotSubrepresentation_top] at h
  exact nontrivial_of_top_ne_bot _ h

theorem nontrivial_binary {a b : ℕ}
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear b F.Carrier))
    [Nontrivial X.1] [Nontrivial X.2] :
    Nontrivial ((T.binaryNormalizedProductFunctor a b).obj X) := by
  let _ := T.topology
  rcases Nat.eq_zero_or_pos a with ha | ha
  · subst ha
    rw [T.binaryNormalizedProductFunctor_zero_left]
    have := nontrivial_tensor X.1 X.2
    change Nontrivial (ULift (X.1 ⊗[ℂ] X.2))
    infer_instance
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    rw [T.binaryNormalizedProductFunctor_of_right_eq_zero ha.ne' rfl]
    have := nontrivial_tensor X.1 X.2
    change Nontrivial (ULift (X.1 ⊗[ℂ] X.2))
    infer_instance
  · rw [show X = (X.1, X.2) from rfl, T.binaryNormalizedProductFunctor_of_pos ha hb]
    change Nontrivial ((T.normalizedProductInductionFunctor (BlockShape.binary a b ha hb)).obj
      ((T.binaryPairFamilyFunctor ha hb).obj (X.1, X.2)))
    refine nontrivial_normalizedProduct T _ _ ?_ ⟨0, Nat.zero_lt_two⟩
    intro i
    fin_cases i
    · change Nontrivial X.1
      infer_instance
    · change Nontrivial X.2
      infer_instance

end Langlands.AllFieldBZ.Derivative.ProductVanishing
