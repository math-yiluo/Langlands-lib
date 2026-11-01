import Langlands.Representation.Mirabolic.MixedProducts
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Parabolic.ProductInductionSubrepresentation

/-!
# Vanishing and nonvanishing of products

A mixed product with a zero factor is zero, and a binary product or a
normalized block product of nonzero factors is nonzero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace Langlands.Derivative.ProductVanishing

open GeneralLinear

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

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

theorem nontrivial_tensor (V W : Type*) [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] [Nontrivial V] [Nontrivial W] : Nontrivial (V ⊗[ℂ] W) := by
  obtain ⟨w, hw⟩ := exists_ne (0 : W)
  refine TensorProduct.nontrivial_of_linearMap_injective_of_flat_left ℂ V W
    (LinearMap.toSpanSingleton ℂ W w) ?_
  intro c d h
  simp only [LinearMap.toSpanSingleton_apply] at h
  exact smul_left_injective ℂ hw h

theorem top_ne_bot_of_nontrivial {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [Nontrivial V] :
    (⊤ : Subrepresentation ρ) ≠ ⊥ := by
  intro h
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
  rw [h] at this
  exact hx this

theorem nontrivial_of_top_ne_bot {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (h : (⊤ : Subrepresentation ρ) ≠ ⊥) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  apply h
  apply Subrepresentation.toSubmodule_injective
  exact Subsingleton.elim (α := Submodule ℂ V) _ _

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

end Langlands.Derivative.ProductVanishing
