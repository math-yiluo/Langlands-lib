import Langlands.GroupScheme.Quaternionic.CocharacterWeightSpaceUniversal
import Mathlib.LinearAlgebra.Dimension.Finite

/-! # Coefficient projections and independence of division-algebra row weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] (σ : FirstKindInvolution K D)
  {n : Type} [Fintype n] [DecidableEq n]

variable (K) in
/-- The coefficient of a Laurent monomial as a linear functional. -/
def cocharacterLaurentCoefficient (c : ℤ) : LaurentPolynomial K →ₗ[K] K :=
  (Finsupp.lapply c).comp (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

/-- Apply a Laurent coefficient functional to the first factor of a tensor. -/
def cocharacterTensorCoefficient (c : ℤ) :
    (LaurentPolynomial K ⊗[K] D) →ₗ[K] D :=
  (TensorProduct.lid K D).toLinearMap.comp
    (TensorProduct.map (cocharacterLaurentCoefficient K c) LinearMap.id)

omit [FiniteDimensional K D] in
theorem cocharacterTensorCoefficient_tmul (c : ℤ)
    (p : LaurentPolynomial K) (v : D) :
    cocharacterTensorCoefficient (D := D) c (p ⊗ₜ[K] v) = p.coeff c • v := by
  rfl

omit [FiniteDimensional K D] in
theorem cocharacterTensorCoefficient_T_tmul (c d : ℤ) (v : D) :
    cocharacterTensorCoefficient (D := D) c (LaurentPolynomial.T d ⊗ₜ[K] v) =
      if d = c then v else 0 := by
  rw [cocharacterTensorCoefficient_tmul, LaurentPolynomial.T_apply]
  split_ifs <;> simp

/-- The universal row action, with the input restricted to vectors over `D`. -/
def cocharacterUniversalRowAction (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q) :
    (n → D) →ₗ[K] (n → LaurentPolynomial K ⊗[K] D) :=
  ((σ.isometryRowActionOver q (cocharacterWeightTestAlgebra K)
      (cocharacterWeightUniversalPoint K ≫ f.hom.hom)).restrictScalars K).comp
    (LinearMap.pi fun i =>
      (TensorProduct.mk K (LaurentPolynomial K) D 1).comp (LinearMap.proj i))

/-- The coefficient of weight `c` in the universal row action. -/
def cocharacterWeightProjector (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (c : ℤ) : (n → D) →ₗ[K] (n → D) :=
  (LinearMap.pi fun i =>
    (cocharacterTensorCoefficient (D := D) c).comp (LinearMap.proj i)).comp
      (σ.cocharacterUniversalRowAction q f)

/-- Coefficient projections isolate every all-test cocharacter weight space. -/
theorem cocharacterWeightProjector_of_mem (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q)
    (c d : ℤ) {v : n → D} (hv : v ∈ σ.cocharacterWeightSpace q f d) :
    σ.cocharacterWeightProjector q f c v = if d = c then v else 0 := by
  have h := (σ.mem_cocharacterWeightSpace_iff_universal q f d v).mp hv
  change σ.cocharacterUniversalRowAction q f v = _ at h
  funext i
  change cocharacterTensorCoefficient c (σ.cocharacterUniversalRowAction q f v i) = _
  rw [h, cocharacterTensorCoefficient_T_tmul]
  split_ifs <;> rfl

/-- The `D`-subspaces of cocharacter row weights are independent over every field. -/
theorem cocharacterWeightSpace_iSupIndep (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q) :
    iSupIndep (σ.cocharacterWeightSpace q f) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro t v hv hsum c hc
  have h : (∑ d ∈ t, σ.cocharacterWeightProjector q f c (v d)) = 0 := by
    rw [← _root_.map_sum, hsum, _root_.map_zero]
  have he : (∑ d ∈ t, σ.cocharacterWeightProjector q f c (v d)) = v c := by
    calc
      (∑ d ∈ t, σ.cocharacterWeightProjector q f c (v d)) =
          ∑ d ∈ t, if d = c then v d else 0 := by
        apply Finset.sum_congr rfl
        intro d hd
        exact σ.cocharacterWeightProjector_of_mem q f c d (hv d hd)
      _ = v c := by simp [hc]
  exact he.symm.trans h

/-- Only finitely many integer cocharacter weights have a nonzero row space. -/
theorem finite_cocharacterWeights (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q) :
    Set.Finite {c : ℤ | σ.cocharacterWeightSpace q f c ≠ ⊥} := by
  exact Set.finite_def.mpr
    ⟨(σ.cocharacterWeightSpace_iSupIndep q f).fintypeNeBotOfFiniteDimensional⟩

/-- The number of occurring weights is at most the dimension of the row module over `D`. -/
theorem card_cocharacterWeights_le (q : σ.QuadraticForms n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ σ.isometryGroup q) :
    Nat.card {c : ℤ // σ.cocharacterWeightSpace q f c ≠ ⊥} ≤ Fintype.card n := by
  let := (σ.cocharacterWeightSpace_iSupIndep q f).fintypeNeBotOfFiniteDimensional
  simpa only [Nat.card_eq_fintype_card, Module.finrank_fintype_fun_eq_card] using
    (σ.cocharacterWeightSpace_iSupIndep q f).subtype_ne_bot_le_finrank

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
