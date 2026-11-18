import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteAffinoidAlgebraDescent.FiniteBanachPresentation
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # Finite free square-zero extensions of presented affinoid algebras -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FreeSquareZero

open TrivSqZeroExt

abbrev Coordinates (A : Type v) (n : ℕ) := TrivSqZeroExt A (Fin n → A)

variable {A : Type v} {n : ℕ}

private def asPair [AddCommGroup A] : Coordinates A n ≃+ A × (Fin n → A) where
  toFun x := (x.fst, x.snd)
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

instance [NormedCommRing A] [IsUltrametricDist A] : NormedCommRing (Coordinates A n) where
  __ := (inferInstance : CommRing (TrivSqZeroExt A (Fin n → A)))
  __ := NormedAddCommGroup.induced _ _ asPair.toAddMonoidHom asPair.injective
  norm_mul_le x y := by
    let X := max ‖x.fst‖ ‖x.snd‖
    let Y := max ‖y.fst‖ ‖y.snd‖
    change max ‖(x * y).fst‖ ‖(x * y).snd‖ ≤ X * Y
    rw [fst_mul, snd_mul, op_smul_eq_smul]
    have hx₀ : ‖x.fst‖ ≤ X := le_max_left _ _
    have hx₁ : ‖x.snd‖ ≤ X := le_max_right _ _
    have hy₀ : ‖y.fst‖ ≤ Y := le_max_left _ _
    have hy₁ : ‖y.snd‖ ≤ Y := le_max_right _ _
    have hX : 0 ≤ X := (norm_nonneg _).trans hx₀
    have hY : 0 ≤ Y := (norm_nonneg _).trans hy₀
    refine max_le (le_trans (norm_mul_le _ _) (mul_le_mul hx₀ hy₀ (norm_nonneg _) hX)) ?_
    apply (IsUltrametricDist.norm_add_le_max _ _).trans
    exact max_le
      ((norm_smul_le _ _).trans (mul_le_mul hx₀ hy₁ (norm_nonneg _) hX))
      ((norm_smul_le _ _).trans ((mul_le_mul hy₀ hx₁ (norm_nonneg _) hY).trans_eq (mul_comm Y X)))

variable [NormedCommRing A] [IsUltrametricDist A]

theorem norm_def (x : Coordinates A n) : ‖x‖ = max ‖x.fst‖ ‖x.snd‖ := rfl

theorem norm_fst_le (x : Coordinates A n) : ‖x.fst‖ ≤ ‖x‖ := le_max_left _ _

theorem norm_snd_le (x : Coordinates A n) : ‖x.snd‖ ≤ ‖x‖ := le_max_right _ _

@[simp] theorem norm_inl (x : A) : ‖(inl x : Coordinates A n)‖ = ‖x‖ := by
  rw [norm_def, fst_inl, snd_inl, norm_zero, max_eq_left (norm_nonneg _)]

@[simp] theorem norm_inr (v : Fin n → A) : ‖(inr v : Coordinates A n)‖ = ‖v‖ := by
  rw [norm_def, fst_inr, snd_inr, norm_zero, max_eq_right (norm_nonneg _)]

private def toProduct : Coordinates A n ≃ᵢ A × (Fin n → A) where
  toEquiv := asPair.toEquiv
  isometry_toFun := Isometry.of_dist_eq fun x y => by
    simp only [dist_eq_norm, AddEquiv.toEquiv_eq_coe]
    rfl

instance [CompleteSpace A] : CompleteSpace (Coordinates A n) := toProduct.completeSpace_iff.mpr inferInstance

instance : IsUltrametricDist (Coordinates A n) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    rw [norm_def, fst_add, snd_add]
    exact max_le
      ((IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (le_max_of_le_left (norm_fst_le x)) (le_max_of_le_right (norm_fst_le y))))
      ((IsUltrametricDist.norm_add_le_max _ _).trans
        (max_le (le_max_of_le_left (norm_snd_le x)) (le_max_of_le_right (norm_snd_le y))))

variable (K : Type u) [NormedField K] [NormedAlgebra K A]

instance : NormedAlgebra K (Coordinates A n) where
  __ := (inferInstance : Algebra K (TrivSqZeroExt A (Fin n → A)))
  norm_smul_le k x := by
    change ‖k • (asPair x : A × (Fin n → A))‖ ≤ ‖k‖ * ‖asPair x‖
    exact norm_smul_le _ _

/-- The constant-coordinate inclusion with its original base norm. -/
def scalarMap : BoundedAlgHom K A (Coordinates A n) where
  toAlgHom := inlAlgHom K A (Fin n → A)
  bounded := ⟨1, zero_lt_one, fun x => by
    change ‖(inl x : Coordinates A n)‖ ≤ 1 * ‖x‖
    rw [norm_inl, one_mul]⟩

/-- The degree-one element at a single coordinate. -/
def basisElement (j : Fin n) : Coordinates A n := inr (Pi.single j 1)

/-- Each coordinate pair is a linear combination of the unit and the specified
square-zero basis. -/
theorem expansion (x : Coordinates A n) :
    scalarMap K x.fst + ∑ j, scalarMap K (x.snd j) * basisElement j = x := by
  classical
  change inl x.fst + ∑ j, inl (x.snd j) * inr (Pi.single j 1) = x
  have hsingle (j : Fin n) : x.snd j • Pi.single j (1 : A) = Pi.single j (x.snd j) := by
    ext i
    by_cases hij : j = i
    · subst i
      simp [smul_eq_mul]
    · simp [hij]
  simp_rw [inl_mul_inr, hsingle, ← inr_sum]
  have hv : (∑ j, Pi.single j (x.snd j)) = x.snd := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hv, inl_fst_add_inr_snd_eq]

/-- The algebra has a controlled lift in its finite free coordinates. -/
theorem scalarMap_isFiniteBanach : (scalarMap (A := A) (n := n) K).IsFiniteBanach := by
  refine ⟨n + 1, Fin.cons 1 basisElement, 1, zero_lt_one, fun x =>
    ⟨Fin.cons x.fst x.snd, ?_, ?_⟩⟩
  · simpa only [BoundedAlgHom.coefficientMap_apply, Fin.sum_univ_succ, Fin.cons_zero,
      Fin.cons_succ, mul_one] using expansion K x
  · rw [one_mul]
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).2 fun j => ?_
    refine Fin.cases (norm_fst_le x) (fun i => ?_) j
    exact (norm_le_pi_norm x.snd i).trans (norm_snd_le x)

variable [IsUltrametricDist K] [CompleteSpace K]

/-- A presented algebra for the rank `n` free square-zero ideal over `A`. -/
def presentation (A : PresentedAffinoidAlgebra K) (n : ℕ) :
    {P : PresentedAffinoidAlgebra K // Nonempty (BoundedAlgEquiv K P (Coordinates A n))} := by
  have h := FiniteBanachPresentation.exists_presentation (scalarMap (A := A) (n := n) K)
    (by simpa only [norm_def, fst_one, snd_one, norm_zero, max_eq_left (norm_nonneg _)]
      using PresentedAffinoidAlgebra.norm_one_le K A)
    (scalarMap_isFiniteBanach K)
  exact ⟨h.choose, h.choose_spec⟩

abbrev algebra (A : PresentedAffinoidAlgebra K) (n : ℕ) : PresentedAffinoidAlgebra K :=
  (presentation K A n).val

/-- The bounded coordinates of the actual presented square-zero algebra. -/
def coordinateEquiv (A : PresentedAffinoidAlgebra K) (n : ℕ) :
    BoundedAlgEquiv K (algebra K A n) (Coordinates A n) :=
  Classical.choice (presentation K A n).property

/-- The structural map into the actual presented square-zero algebra. -/
def baseMap (A : PresentedAffinoidAlgebra K) (n : ℕ) : BoundedAlgHom K A (algebra K A n) :=
  (coordinateEquiv K A n).symm.toBoundedAlgHom.comp (scalarMap K)

@[simp] theorem coordinateEquiv_baseMap (A : PresentedAffinoidAlgebra K) (n : ℕ) (x : A) :
    coordinateEquiv K A n (baseMap K A n x) = inl x :=
  (coordinateEquiv K A n).apply_symm_apply (inl x)

end Langlands.Analytic.PresentedAffinoidAlgebra.FreeSquareZero
