import Langlands.GroupScheme.Dynamic.UnitaryCocharacterDiagonal
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Hermitian weights from a normal separating cocharacter point -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open scoped InnerProductSpace Matrix

namespace Langlands.LinearAlgebra

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]

/-- A normal operator takes an eigenvector to the conjugate eigenvalue under
its adjoint. -/
theorem adjoint_apply_eq_conj_smul_of_normal
    (T : E →L[𝕜] E) [IsStarNormal T] {c : 𝕜} {x : E}
    (hx : T x = c • x) :
    T.adjoint x = star c • x := by
  have hcomm : Commute T (star (c • (1 : E →L[𝕜] E))) := by
    simpa only [star_smul, star_one] using
      (Commute.one_right T |>.smul_right (star c))
  have hS : IsStarNormal (T - c • 1) := hcomm.isStarNormal_sub
  have hz : (T - c • 1) x = 0 := by simp [hx]
  have hz' := ContinuousLinearMap.IsStarNormal.adjoint_apply_eq_zero_iff hS x |>.mpr hz
  simpa [map_sub, map_smulₛₗ, sub_eq_zero] using hz'

/-- Eigenvectors of a normal operator at distinct eigenvalues are orthogonal. -/
theorem inner_eq_zero_of_normal_eigenvectors
    (T : E →L[𝕜] E) [IsStarNormal T] {c μ : 𝕜} {x y : E}
    (hx : T x = c • x) (hy : T y = μ • y) (h : c ≠ μ) :
    inner 𝕜 x y = 0 := by
  have ha := adjoint_apply_eq_conj_smul_of_normal T hx
  have hi := T.adjoint_inner_left y x
  rw [ha, hy, inner_smul_left, inner_smul_right] at hi
  simp only [starRingEnd_apply, star_star] at hi
  exact (mul_eq_mul_right_iff.mp hi).resolve_left h

variable {n : Type*} [Fintype n] [DecidableEq n] {ι : Type*} [DecidableEq ι]

/-- Complete orthogonal idempotents are Hermitian if a normal matrix acts
on their ranges by distinct scalars. -/
theorem hermitian_projectors_of_normal_separating_action
    (F : ι → Matrix n n 𝕜)
    (hF : ∀ a b, F a * F b = if a = b then F a else 0)
    (s : Finset ι) (hs : ∑ a ∈ s, F a = 1)
    (A : Matrix n n 𝕜) [IsStarNormal A] (c : ι → 𝕜)
    (hc : Function.Injective c) (hA : ∀ a, A * F a = c a • F a) :
    ∀ a, (F a).IsHermitian := by
  let L : ι → EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n :=
    fun a => (F a).toEuclideanLin
  let T : EuclideanSpace 𝕜 n →L[𝕜] EuclideanSpace 𝕜 n :=
    Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜) A
  have hT : IsStarNormal T :=
    IsStarNormal.map (Matrix.toEuclideanCLM (n := n) (𝕜 := 𝕜)).toStarAlgHom A
  let := hT
  have heigen (a : ι) (x : EuclideanSpace 𝕜 n) :
      T (L a x) = c a • L a x := by
    change A.toEuclideanLin ((F a).toEuclideanLin x) = _
    change (A.toEuclideanLin.comp (F a).toEuclideanLin) x = _
    rw [← Matrix.toLpLin_mul_same, hA]
    simp [L]
  have horth (a b : ι) (hab : a ≠ b) (x y : EuclideanSpace 𝕜 n) :
      inner 𝕜 (L a x) (L b y) = 0 :=
    inner_eq_zero_of_normal_eigenvectors T (heigen a x) (heigen b y)
      (fun h => hab (hc h))
  have hsum (y : EuclideanSpace 𝕜 n) : ∑ b ∈ s, L b y = y := by
    have h := congrArg (fun B : Matrix n n 𝕜 => B.toEuclideanLin y) hs
    simpa [L, map_sum, Matrix.toEuclideanLin] using h
  have hmul (a b : ι) (x : EuclideanSpace 𝕜 n) :
      L a (L b x) = if a = b then L a x else 0 := by
    change ((F a).toEuclideanLin.comp (F b).toEuclideanLin) x = _
    rw [← Matrix.toLpLin_mul_same, hF]
    split_ifs <;> simp [L]
  intro a
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  have hidem : IsIdempotentElem (L a) := by
    apply LinearMap.ext
    intro x
    simpa using hmul a a x
  apply (LinearMap.IsIdempotentElem.isSymmetric_iff_isOrtho_range_ker hidem).mpr
  rw [Submodule.isOrtho_iff_inner_eq]
  rintro _ ⟨x, rfl⟩ y hy
  rw [← hsum y, inner_sum]
  apply Finset.sum_eq_zero
  intro b _
  by_cases hab : a = b
  · subst b
    rw [show L a y = 0 from hy, inner_zero_right]
  · exact horth a b hab x y

end Langlands.LinearAlgebra

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GeneralLinear

variable {n : Type} [Fintype n] [DecidableEq n]
  {𝕜 : Type u} [RCLike 𝕜]
  (χ : (Gm (Spec (CommRingCat.of 𝕜))).toGrp ⟶ groupScheme n (CommRingCat.of 𝕜))

variable (𝕜) in
/-- The positive scalar two as a unit over a real or complex coefficient field. -/
def positiveTwoUnit : 𝕜ˣ := Units.mk0 2 (by norm_num)

/-- Evaluation of Laurent coordinates at an actual scalar unit. -/
def cocharacterEvalUnit (t : 𝕜ˣ) : LaurentPolynomial 𝕜 →ₐ[𝕜] 𝕜 :=
  { LaurentPolynomial.eval₂ (RingHom.id 𝕜) t with
    commutes' r := by
      change LaurentPolynomial.eval₂ (RingHom.id 𝕜) t
        (algebraMap 𝕜 (LaurentPolynomial 𝕜) r) = r
      rw [← LaurentPolynomial.C_eq_algebraMap]
      simp }

@[simp] theorem cocharacterEvalUnit_single (t : 𝕜ˣ) (a : ℤ) (r : 𝕜) :
    cocharacterEvalUnit t (AddMonoidAlgebra.single a r) = r * (t : 𝕜) ^ a := by
  change LaurentPolynomial.eval₂ (RingHom.id 𝕜) t _ = _
  rw [LaurentPolynomial.single_eq_C_mul_T, LaurentPolynomial.eval₂_C_mul_T]
  simp

/-- The value of a cocharacter is the finite sum of its scalar weight actions. -/
theorem cocharacterUnitsHom_eq_sum_weightProjector (t : 𝕜ˣ) :
    (cocharacterUnitsHom χ 𝕜 t : Matrix n n 𝕜) =
      ∑ a ∈ cocharacterWeightSupport χ, (t : 𝕜) ^ a • weightProjector χ a := by
  have ht : Units.map (cocharacterEvalUnit t).toMonoidHom
      (cocharacterLaurentUnit (CommRingCat.of 𝕜)) = t := by
    apply Units.ext
    change LaurentPolynomial.eval₂ (RingHom.id 𝕜) t (LaurentPolynomial.T 1) = _
    simp
  have h := cocharacterUnitsHom_naturality χ (cocharacterEvalUnit t)
    (cocharacterLaurentUnit (CommRingCat.of 𝕜))
  rw [ht] at h
  ext i j
  have hij := congrArg (fun g : GL n 𝕜 => (g : Matrix n n 𝕜) i j) h
  rw [hij, Matrix.sum_apply]
  change cocharacterEvalUnit t ((weightMatrix χ : Matrix n n (LaurentPolynomial 𝕜)) i j) = _
  rw [weightMatrix_apply, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [cocharacterEvalUnit_single]
  change weightProjector χ a i j * (t : 𝕜) ^ a =
    (t : 𝕜) ^ a * weightProjector χ a i j
  exact mul_comm _ _

/-- On the range of its `a`th projector, a cocharacter value acts by `t^a`. -/
theorem cocharacterUnitsHom_mul_weightProjector (t : 𝕜ˣ) (a : ℤ) :
    (cocharacterUnitsHom χ 𝕜 t : Matrix n n 𝕜) * weightProjector χ a =
      (t : 𝕜) ^ a • weightProjector χ a := by
  rw [cocharacterUnitsHom_eq_sum_weightProjector, Finset.sum_mul]
  simp only [smul_mul_assoc]
  rw [Finset.sum_eq_single a]
  · rw [weightProjector_mul]
    simp
  · intro b _ hba
    rw [weightProjector_mul]
    simp [hba]
  · intro ha
    rw [weightProjector_eq_zero χ ha]
    simp

/-- Normality of the value at two is a sufficient analytic condition for
Hermitian cocharacter weights. -/
def HasNormalPositivePoint : Prop :=
  IsStarNormal (cocharacterUnitsHom χ 𝕜 (positiveTwoUnit 𝕜) : Matrix n n 𝕜)

/-- A normal value at two makes every Laurent weight projector Hermitian. -/
theorem HasNormalPositivePoint.hasHermitianWeightProjectors
    (h : HasNormalPositivePoint χ) : HasHermitianWeightProjectors χ := by
  let : IsStarNormal
      (cocharacterUnitsHom χ 𝕜 (positiveTwoUnit 𝕜) : Matrix n n 𝕜) := h
  apply Langlands.LinearAlgebra.hermitian_projectors_of_normal_separating_action
    (weightProjector χ) (fun a b => by
      rw [weightProjector_mul]
      split_ifs with hab
      · subst b; rfl
      · rfl)
    (cocharacterWeightSupport χ) (sum_weightProjector χ)
    (cocharacterUnitsHom χ 𝕜 (positiveTwoUnit 𝕜) : Matrix n n 𝕜)
    (fun a => (2 : 𝕜) ^ a)
  · intro a b hab
    apply zpow_right_injective₀ (a := (2 : ℝ)) (by norm_num) (by norm_num)
    apply RCLike.ofReal_injective (K := 𝕜)
    simpa only [RCLike.ofReal_zpow, RCLike.ofReal_ofNat] using hab
  · intro a
    exact cocharacterUnitsHom_mul_weightProjector χ (positiveTwoUnit 𝕜) a

end Langlands.GroupScheme.GeneralLinear
