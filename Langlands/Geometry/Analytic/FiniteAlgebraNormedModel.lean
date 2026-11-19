import Langlands.Geometry.Analytic.Affinoid
import Langlands.Geometry.Analytic.ClosedSubmodulesBanach
import Langlands.Geometry.Analytic.StrictTestDomain.FiniteRationalTensorComparisonProof
import Mathlib.Topology.MetricSpace.Ultra.Pi

/-! # Complete normed models of finite algebras over Noetherian Banach algebras -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FiniteNormedModel

open scoped BigOperators

variable (K : Type u) [NontriviallyNormedField K]
  (R : Type v) [NormedCommRing R] [NormedAlgebra K R]
  (E : Type w) [CommRing E] [Algebra R E] [Module.Finite R E]

/-- The number of chosen module generators. -/
def rank : ℕ := (Module.Finite.exists_fin (R := R) (M := E)).choose

/-- Chosen generators of `E` as an `R`-module. -/
def gen : Fin (rank R E) → E :=
  (Module.Finite.exists_fin (R := R) (M := E)).choose_spec.choose

theorem span_gen : Submodule.span R (Set.range (gen R E)) = ⊤ :=
  (Module.Finite.exists_fin (R := R) (M := E)).choose_spec.choose_spec

/-- The coefficient map `w ↦ ∑ i, w i • gen i`. -/
def coeff : (Fin (rank R E) → R) →ₗ[R] E :=
  Fintype.linearCombination R (gen R E)

theorem coeff_apply (w : Fin (rank R E) → R) : coeff R E w = ∑ i, w i • gen R E i :=
  rfl

theorem coeff_surjective : Function.Surjective (coeff R E) := by
  rw [← LinearMap.range_eq_top]
  exact (Fintype.range_linearCombination R (gen R E)).trans (span_gen R E)

/-- The quotient of coefficient tuples by the kernel of the coefficient map. -/
abbrev Quot := (Fin (rank R E) → R) ⧸ LinearMap.ker (coeff R E)

/-- The identification of `E` with the coefficient quotient. -/
def gam : E ≃ₗ[R] Quot R E :=
  (LinearMap.quotKerEquivOfSurjective (coeff R E) (coeff_surjective R E)).symm

theorem gam_eq_mk_iff (x : E) (w : Fin (rank R E) → R) :
    gam R E x = Submodule.Quotient.mk w ↔ coeff R E w = x := by
  have hmk : (LinearMap.quotKerEquivOfSurjective (coeff R E) (coeff_surjective R E))
      (Submodule.Quotient.mk w) = coeff R E w :=
    LinearMap.quotKerEquivOfSurjective_apply_mk _ _ w
  rw [gam, LinearEquiv.symm_apply_eq, hmk, eq_comm]

theorem gam_coeff (w : Fin (rank R E) → R) :
    gam R E (coeff R E w) = Submodule.Quotient.mk w :=
  (gam_eq_mk_iff R E _ w).2 rfl

/-- Chosen coefficients of the products of two generators. -/
def structConst (i j : Fin (rank R E)) : Fin (rank R E) → R :=
  Function.surjInv (coeff_surjective R E) (gen R E i * gen R E j)

theorem coeff_structConst (i j : Fin (rank R E)) :
    coeff R E (structConst R E i j) = gen R E i * gen R E j :=
  Function.surjInv_eq (coeff_surjective R E) _

/-- A positive bound for the chosen product coefficients. -/
def bound : ℝ := (∑ ij : Fin (rank R E) × Fin (rank R E), ‖structConst R E ij.1 ij.2‖) + 1

theorem bound_pos : 0 < bound R E := by
  have : 0 ≤ ∑ ij : Fin (rank R E) × Fin (rank R E), ‖structConst R E ij.1 ij.2‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold bound
  linarith

theorem norm_structConst_le (i j : Fin (rank R E)) : ‖structConst R E i j‖ ≤ bound R E := by
  have h := Finset.single_le_sum
    (f := fun ij : Fin (rank R E) × Fin (rank R E) => ‖structConst R E ij.1 ij.2‖)
    (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
  unfold bound
  simp only at h
  linarith

theorem coeff_mul (u w : Fin (rank R E) → R) :
    coeff R E (∑ i, ∑ j, (u i * w j) • structConst R E i j) = coeff R E u * coeff R E w := by
  rw [coeff_apply R E u, coeff_apply R E w, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, coeff_structConst, smul_mul_smul_comm]

/-- Elements of `R` act boundedly on the coefficient quotient. -/
theorem norm_smul_quot_le (r : R) (v : Quot R E) : ‖r • v‖ ≤ ‖r‖ * ‖v‖ :=
  le_mul_norm_quotient_of_forall_mk v (norm_nonneg r) fun w hw => by
    rw [← hw, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_smul_le r w)

/-- Scalars act boundedly on the coefficient quotient. -/
theorem norm_scalar_smul_quot_le (k : K) (v : Quot R E) : ‖k • v‖ ≤ ‖k‖ * ‖v‖ :=
  le_mul_norm_quotient_of_forall_mk v (norm_nonneg k) fun w hw => by
    rw [← hw, ← Submodule.Quotient.mk_smul]
    exact (Submodule.Quotient.norm_mk_le _ _).trans (norm_smul_le k w)

variable [IsUltrametricDist R]

/-- The quotient norm is submultiplicative up to the structure bound. -/
theorem norm_gam_mul_le (x y : E) :
    ‖gam R E (x * y)‖ ≤ bound R E * (‖gam R E x‖ * ‖gam R E y‖) := by
  apply le_mul_norm_mul_norm_quotient_of_forall_mk _ _ (bound_pos R E).le
  intro u w hu hw
  have hxu : coeff R E u = x := (gam_eq_mk_iff R E x u).1 hu.symm
  have hyw : coeff R E w = y := (gam_eq_mk_iff R E y w).1 hw.symm
  rw [← hxu, ← hyw, ← coeff_mul, gam_coeff]
  refine (Submodule.Quotient.norm_mk_le _ _).trans ?_
  have h0 : 0 ≤ bound R E * (‖u‖ * ‖w‖) := by
    have := bound_pos R E
    positivity
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0
  intro i _
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg h0
  intro j _
  calc
    ‖(u i * w j) • structConst R E i j‖ ≤ ‖u i * w j‖ * ‖structConst R E i j‖ :=
      norm_smul_le _ _
    _ ≤ (‖u i‖ * ‖w j‖) * bound R E :=
      mul_le_mul (norm_mul_le _ _) (norm_structConst_le R E i j) (norm_nonneg _)
        (by positivity)
    _ ≤ (‖u‖ * ‖w‖) * bound R E := by
      have := bound_pos R E
      gcongr
      · exact norm_le_pi_norm u i
      · exact norm_le_pi_norm w j
    _ = _ := by ring

variable [CompleteSpace R] [IsNoetherianRing R]

omit [IsUltrametricDist R] in
include K in
theorem isClosed_ker : IsClosed (LinearMap.ker (coeff R E) : Set (Fin (rank R E) → R)) :=
  isClosed_submodule_pi_of_noetherian_banach (K := K) _

/-- The underlying type of the normed model: a copy of `E`. -/
def Model (_K : Type u) (_R : Type v) (E : Type w) : Type w := E

instance : CommRing (Model K R E) := inferInstanceAs (CommRing E)

instance : Algebra R (Model K R E) := inferInstanceAs (Algebra R E)

/-- The identification of the model with `E`, as `R`-algebras. -/
def ofModel : Model K R E ≃ₐ[R] E := AlgEquiv.refl

/-- The norm of the model, transported to `E`. -/
def modelNorm (x : E) : ℝ := bound R E * ‖gam R E x‖

/-- The scaled coefficient-quotient norm. -/
def addGroupNorm : AddGroupNorm (Model K R E) where
  toFun x := modelNorm R E (ofModel K R E x)
  map_zero' := by
    simp only [modelNorm, map_zero, norm_zero, mul_zero]
  add_le' x y := by
    simp only [modelNorm, map_add, ← mul_add]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (bound_pos R E).le
  neg' x := by
    simp only [modelNorm, map_neg, norm_neg]
  eq_zero_of_map_eq_zero' x hx := by
    have : IsClosed (LinearMap.ker (coeff R E) : Set (Fin (rank R E) → R)) :=
      isClosed_ker K R E
    have h0 : ‖gam R E (ofModel K R E x)‖ = 0 :=
      (mul_eq_zero.mp hx).resolve_left (bound_pos R E).ne'
    have h1 : gam R E (ofModel K R E x) = 0 := norm_eq_zero.mp h0
    exact (ofModel K R E).injective ((gam R E).injective (h1.trans (map_zero _).symm) |>.trans
      (map_zero _).symm)

instance normedAddCommGroup : NormedAddCommGroup (Model K R E) :=
  (addGroupNorm K R E).toNormedAddCommGroup

omit [IsUltrametricDist R] in
theorem norm_def (x : Model K R E) : ‖x‖ = bound R E * ‖gam R E (ofModel K R E x)‖ :=
  rfl

instance normedCommRing : NormedCommRing (Model K R E) :=
  { normedAddCommGroup K R E, (inferInstance : CommRing (Model K R E)) with
    norm_mul_le := fun x y => by
      rw [norm_def, norm_def, norm_def, map_mul]
      calc
        bound R E * ‖gam R E (ofModel K R E x * ofModel K R E y)‖ ≤
            bound R E * (bound R E *
              (‖gam R E (ofModel K R E x)‖ * ‖gam R E (ofModel K R E y)‖)) :=
          mul_le_mul_of_nonneg_left (norm_gam_mul_le R E _ _) (bound_pos R E).le
        _ = bound R E * ‖gam R E (ofModel K R E x)‖ *
            (bound R E * ‖gam R E (ofModel K R E y)‖) := by ring }

instance algebraK : Algebra K (Model K R E) :=
  ((algebraMap R (Model K R E)).comp (algebraMap K R)).toAlgebra

instance : IsScalarTower K R (Model K R E) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

instance normedAlgebra : NormedAlgebra K (Model K R E) :=
  { algebraK K R E with
    norm_smul_le := fun k x => by
      have hsmul : k • x = (algebraMap K R k) • x := (algebraMap_smul R k x).symm
      rw [hsmul, norm_def, norm_def, map_smul, LinearEquiv.map_smul, algebraMap_smul]
      calc
        bound R E * ‖k • gam R E (ofModel K R E x)‖ ≤
            bound R E * (‖k‖ * ‖gam R E (ofModel K R E x)‖) :=
          mul_le_mul_of_nonneg_left (norm_scalar_smul_quot_le K R E k _) (bound_pos R E).le
        _ = ‖k‖ * (bound R E * ‖gam R E (ofModel K R E x)‖) := by ring }

instance isUltrametricDist : IsUltrametricDist (Model K R E) := by
  have : IsUltrametricDist (Quot R E) := isUltrametricDist_submoduleQuotient _
  exact IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y => by
    rw [norm_def, norm_def, norm_def, map_add, map_add,
      ← mul_max_of_nonneg _ _ (bound_pos R E).le]
    exact mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_add_le_max _ _) (bound_pos R E).le

instance completeSpace : CompleteSpace (Model K R E) := by
  have : IsClosed (LinearMap.ker (coeff R E) : Set (Fin (rank R E) → R)) :=
    isClosed_ker K R E
  let e : Model K R E ≃+ Quot R E :=
    (ofModel K R E).toLinearEquiv.toAddEquiv.trans (gam R E).toAddEquiv
  have he : ∀ x, e x = gam R E (ofModel K R E x) := fun _ => rfl
  have hD := bound_pos R E
  have hanti : AntilipschitzWith ⟨bound R E, hD.le⟩ e :=
    AntilipschitzWith.of_le_mul_dist fun x y => by
      simp only [dist_eq_norm, ← map_sub]
      rw [norm_def, he]
      rfl
  have hlip : LipschitzWith ⟨1 / bound R E, by positivity⟩ e :=
    LipschitzWith.of_dist_le_mul fun x y => by
      simp only [dist_eq_norm, ← map_sub]
      rw [norm_def, he]
      change _ ≤ (1 / bound R E) * _
      exact le_of_eq (by field_simp)
  rw [completeSpace_iff_isComplete_range (hanti.isUniformInducing hlip.uniformContinuous),
    e.surjective.range_eq]
  exact isComplete_univ

/-- The structure map from `R` to the model is bounded. -/
def baseHom : BoundedAlgHom K R (Model K R E) where
  toAlgHom := IsScalarTower.toAlgHom K R (Model K R E)
  bounded := by
    refine ⟨bound R E * ‖gam R E 1‖ + 1, by have := bound_pos R E; positivity, fun r => ?_⟩
    change ‖algebraMap R (Model K R E) r‖ ≤ _
    rw [norm_def, AlgEquiv.commutes, Algebra.algebraMap_eq_smul_one, LinearEquiv.map_smul]
    have hD := bound_pos R E
    calc
      bound R E * ‖r • gam R E 1‖ ≤ bound R E * (‖r‖ * ‖gam R E 1‖) :=
        mul_le_mul_of_nonneg_left (norm_smul_quot_le R E r _) hD.le
      _ ≤ (bound R E * ‖gam R E 1‖ + 1) * ‖r‖ := by
        nlinarith [norm_nonneg r, norm_nonneg (gam R E 1)]

theorem baseHom_apply (r : R) : baseHom K R E r = algebraMap R (Model K R E) r :=
  rfl

theorem ofModel_baseHom (r : R) : ofModel K R E (baseHom K R E r) = algebraMap R E r :=
  AlgEquiv.commutes _ r

end Langlands.Analytic.FiniteNormedModel
