import Langlands.AlgebraicGeometry.ProjectiveSpace.CoordinateAtlasGluing
import Langlands.AlgebraicGeometry.Modules.TensorPowerGauge
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleFrame

/-! # Powered evaluation brackets as local projective coordinates -/

noncomputable section

universe u v

open CategoryTheory MonoidalCategory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.EvaluationBracket

open Langlands.AlgebraicGeometry.Picard.CocycleGluing
open Langlands.AlgebraicGeometry.Modules.TensorPowerGauge

variable {X : Scheme.{u}} {E : X.Modules} {Λ : Type v} {Q : Λ → X.Modules}

/-- A morphism of module sheaves commutes with restriction of sections. -/
lemma app_res {M N : X.Modules} (φ : M ⟶ N) {V V' : X.Opens} (h : V' ≤ V) (x : Γ(M, V)) :
    φ.app V' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app V x) :=
  congrFun (congrArg (fun f => (ConcreteCategory.hom f : _ → _))
    (φ.mapPresheaf.naturality (homOfLE h).op)) x

variable (ev : ∀ r, E ⟶ Q r) (M : ℕ)

/-- A bracket chart: an open `W`, local generators `q r` of all targets on `W`, and `M`
labels whose joint evaluation is bijective on sections over every open inside `W`. -/
structure Chart where
  /-- The frame labels. -/
  ρ : Fin M → Λ
  /-- The chart open. -/
  W : X.Opens
  /-- Local generators of the evaluation targets. -/
  q : ∀ r, Γ(Q r, W)
  isFrame : ∀ r, Scheme.Modules.IsFrameOn (q r) W
  bij : ∀ V : X.Opens, V ≤ W →
    Function.Bijective (fun (s : Γ(E, V)) (l : Fin M) => (ev (ρ l)).app V s)

namespace Chart

variable {ev M} (C : Chart ev M)

/-- The coefficient of the evaluation of `s` at the label `r` in the chart generator. -/
def coef {V : X.Opens} (hV : V ≤ C.W) (r : Λ) (s : Γ(E, V)) : Γ(X, V) :=
  frameCoeff (C.isFrame r) hV ((ev r).app V s)

lemma coef_spec {V : X.Opens} (hV : V ≤ C.W) (r : Λ) (s : Γ(E, V)) :
    C.coef hV r s • (Q r).presheaf.map (homOfLE hV).op (C.q r) = (ev r).app V s :=
  frameCoeff_smul_frame _ hV _

/-- Coefficients as a linear map on sections. -/
def coefLinear {V : X.Opens} (hV : V ≤ C.W) (r : Λ) : Γ(E, V) →ₗ[Γ(X, V)] Γ(X, V) where
  toFun := C.coef hV r
  map_add' s t := by
    simp only [coef, map_add]
    exact frameCoeff_add _ hV _ _
  map_smul' g s := by
    simp only [coef, Scheme.Modules.Hom.app_smul, RingHom.id_apply, smul_eq_mul]
    exact frameCoeff_smul _ hV _ _

lemma coefLinear_apply {V : X.Opens} (hV : V ≤ C.W) (r : Λ) (s : Γ(E, V)) :
    C.coefLinear hV r s = C.coef hV r s := rfl

lemma coef_restrict {V V' : X.Opens} (hV : V ≤ C.W) (h : V' ≤ V) (r : Λ) (s : Γ(E, V)) :
    X.presheaf.map (homOfLE h).op (C.coef hV r s) =
      C.coef (h.trans hV) r (E.presheaf.map (homOfLE h).op s) := by
  rw [coef, res_frameCoeff, coef, app_res]

/-- The target vector of the `k`-th frame vector under joint evaluation. -/
def frameTarget (k : Fin M) : ∀ l : Fin M, Γ(Q (C.ρ l), C.W) :=
  fun l => if l = k then C.q (C.ρ l) else 0

/-- The frame of sections dual to the generators at the frame labels. -/
def e (k : Fin M) : Γ(E, C.W) :=
  Function.surjInv (C.bij C.W le_rfl).2 (C.frameTarget k)

lemma ev_e (l k : Fin M) :
    (ev (C.ρ l)).app C.W (C.e k) = if l = k then C.q (C.ρ l) else 0 :=
  congrFun (Function.surjInv_eq (C.bij C.W le_rfl).2 (C.frameTarget k)) l

/-- The frame restricted to a smaller open. -/
def eV {V : X.Opens} (hV : V ≤ C.W) (k : Fin M) : Γ(E, V) :=
  E.presheaf.map (homOfLE hV).op (C.e k)

lemma coef_frame {V : X.Opens} (hV : V ≤ C.W) (l k : Fin M) :
    C.coef hV (C.ρ l) (C.eV hV k) = if l = k then 1 else 0 := by
  apply frameCoeff_eq
  rw [eV, app_res, ev_e]
  split_ifs
  · rw [one_smul]
  · rw [zero_smul, map_zero]

/-- Every section over an open inside the chart is the combination of the frame with its
coefficients at the frame labels. -/
lemma expand {V : X.Opens} (hV : V ≤ C.W) (s : Γ(E, V)) :
    s = ∑ k, C.coef hV (C.ρ k) s • C.eV hV k := by
  apply (C.bij V hV).1
  funext l
  simp only
  rw [map_sum]
  simp only [Scheme.Modules.Hom.app_smul, eV, app_res, ev_e, apply_ite, map_zero,
    smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (C.coef_spec hV _ s).symm

/-- The coefficient matrix of the frame at a tuple of labels. -/
def mat {V : X.Opens} (hV : V ≤ C.W) (σ : Fin M → Λ) : Matrix (Fin M) (Fin M) Γ(X, V) :=
  Matrix.of fun l k => C.coef hV (σ l) (C.eV hV k)

lemma mat_frame {V : X.Opens} (hV : V ≤ C.W) : C.mat hV C.ρ = 1 := by
  ext l k
  simp only [mat, Matrix.of_apply, coef_frame, Matrix.one_apply]

lemma mat_restrict {V V' : X.Opens} (hV : V ≤ C.W) (h : V' ≤ V) (σ : Fin M → Λ) :
    (C.mat hV σ).map (X.presheaf.map (homOfLE h).op).hom = C.mat (h.trans hV) σ := by
  ext l k
  simp only [mat, Matrix.map_apply, Matrix.of_apply]
  change X.presheaf.map (homOfLE h).op (C.coef hV (σ l) (C.eV hV k)) = _
  rw [coef_restrict, eV, eV, mres_mres]

variable {n : ℕ} (τ : ∀ r, (Q r).tensorPow n ≅ 𝟙_ X.Modules)

/-- The powered bracket coordinate of a label tuple: the `n`-th power of the determinant of
the coefficient matrix times the gauges of the generators at the labels. -/
def coord (σ : Fin M → Λ) : Γ(X, C.W) :=
  (C.mat le_rfl σ).det ^ n * ∏ l, gauge (τ (σ l)) (C.q (σ l))

lemma coord_restrict {V : X.Opens} (hV : V ≤ C.W) (σ : Fin M → Λ) :
    X.presheaf.map (homOfLE hV).op (C.coord τ σ) =
      (C.mat hV σ).det ^ n *
        ∏ l, gauge (τ (σ l)) ((Q (σ l)).presheaf.map (homOfLE hV).op (C.q (σ l))) := by
  have hm : (X.presheaf.map (homOfLE hV).op).hom.mapMatrix (C.mat le_rfl σ) = C.mat hV σ := by
    rw [RingHom.mapMatrix_apply]
    exact C.mat_restrict le_rfl hV σ
  rw [coord, map_mul, map_pow, map_prod, RingHom.map_det]
  erw [hm]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  exact gauge_restrict (τ (σ l)) (homOfLE hV) (C.q (σ l))

lemma isUnit_coord_frame : IsUnit (C.coord τ C.ρ) := by
  rw [coord, mat_frame, Matrix.det_one, one_pow, one_mul]
  exact IsUnit.prod_univ_iff.mpr fun l => isUnit_gauge (τ (C.ρ l)) (C.isFrame (C.ρ l))

section Transition

variable (D : Chart ev M)

/-- The scaling unit of the generators of two charts on their overlap. -/
def ratio (r : Λ) : Γ(X, C.W ⊓ D.W) :=
  frameCoeff (C.isFrame r) inf_le_left ((Q r).presheaf.map (homOfLE inf_le_right).op (D.q r))

lemma ratio_spec (r : Λ) :
    (Q r).presheaf.map (homOfLE inf_le_right).op (D.q r) =
      C.ratio D r • (Q r).presheaf.map (homOfLE inf_le_left).op (C.q r) :=
  (frameCoeff_smul_frame _ _ _).symm

/-- The inverse scaling unit. -/
def ratioInv (r : Λ) : Γ(X, C.W ⊓ D.W) :=
  frameCoeff (D.isFrame r) inf_le_right ((Q r).presheaf.map (homOfLE inf_le_left).op (C.q r))

lemma ratio_mul (r : Λ) : C.ratio D r * C.ratioInv D r = 1 :=
  frameCoeff_mul_frameCoeff (C.isFrame r) (D.isFrame r) inf_le_left inf_le_right

lemma coef_change (r : Λ) (s : Γ(E, C.W ⊓ D.W)) :
    C.coef inf_le_left r s = C.ratio D r * D.coef inf_le_right r s := by
  apply frameCoeff_eq
  rw [mul_comm, mul_smul, ← ratio_spec]
  exact D.coef_spec inf_le_right r s

lemma coef_change' (r : Λ) (s : Γ(E, C.W ⊓ D.W)) :
    D.coef inf_le_right r s = C.ratioInv D r * C.coef inf_le_left r s := by
  rw [coef_change, ← mul_assoc, mul_comm (C.ratioInv D r), ratio_mul, one_mul]

/-- The change-of-frame matrix on the overlap: column `k` holds the coefficients of the
`k`-th frame vector of `D` in the frame of `C`. -/
def trans : Matrix (Fin M) (Fin M) Γ(X, C.W ⊓ D.W) :=
  Matrix.of fun j k => C.coef inf_le_left (C.ρ j) (D.eV inf_le_right k)

lemma coef_eV_change (r : Λ) (k : Fin M) :
    C.coef inf_le_left r (D.eV inf_le_right k) =
      ∑ j, C.coef inf_le_left r (C.eV inf_le_left j) * C.trans D j k := by
  have h := C.expand inf_le_left (D.eV inf_le_right k)
  conv_lhs => rw [h]
  rw [← coefLinear_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.map_smul, coefLinear_apply, smul_eq_mul, mul_comm]
  rfl

lemma mat_change (σ : Fin M → Λ) :
    D.mat inf_le_right σ =
      Matrix.diagonal (fun l => C.ratioInv D (σ l)) * (C.mat inf_le_left σ * C.trans D) := by
  ext l k
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  simp only [mat, Matrix.of_apply]
  rw [coef_change', coef_eV_change]

lemma det_change (σ : Fin M → Λ) :
    (D.mat inf_le_right σ).det =
      (∏ l, C.ratioInv D (σ l)) * ((C.mat inf_le_left σ).det * (C.trans D).det) := by
  rw [mat_change, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]

lemma isUnit_det_trans : IsUnit (C.trans D).det := by
  have h := C.det_change D D.ρ
  rw [D.mat_frame, Matrix.det_one] at h
  have h1 : IsUnit ((C.mat inf_le_left D.ρ).det * (C.trans D).det) :=
    IsUnit.of_mul_eq_one_right _ h.symm
  exact isUnit_of_mul_isUnit_right h1

lemma gauge_change (r : Λ) :
    gauge (τ r) ((Q r).presheaf.map (homOfLE inf_le_right).op (D.q r)) =
      C.ratio D r ^ n * gauge (τ r) ((Q r).presheaf.map (homOfLE inf_le_left).op (C.q r)) := by
  rw [ratio_spec, gauge_smul]

/-- On an overlap, the powered bracket coordinates of two charts differ by the common unit
`det (trans) ^ n`. -/
lemma coord_change (σ : Fin M → Λ) :
    X.presheaf.map (homOfLE inf_le_right).op (D.coord τ σ) =
      (C.trans D).det ^ n * X.presheaf.map (homOfLE inf_le_left).op (C.coord τ σ) := by
  rw [coord_restrict, coord_restrict, det_change]
  simp only [C.gauge_change τ D]
  rw [Finset.prod_mul_distrib]
  have hwv : (∏ l, C.ratioInv D (σ l)) ^ n * ∏ l, C.ratio D (σ l) ^ n = 1 := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun l _ => by rw [← mul_pow, mul_comm, ratio_mul, one_pow]
  linear_combination ((C.trans D).det ^ n * (C.mat inf_le_left σ).det ^ n *
    ∏ l, gauge (τ (σ l)) ((Q (σ l)).presheaf.map (homOfLE inf_le_left).op (C.q (σ l)))) * hwv

end Transition

end Chart

open Chart in
variable {ev M} in
/-- Bracket charts covering the scheme, with their powered bracket coordinates indexed through
an enumeration of the label tuples, form a coordinate atlas. -/
theorem isAtlas {ι : Type*} (chart : ι → Chart ev M) (hcov : ∀ x, ∃ i, x ∈ (chart i).W)
    {n : ℕ} (τ : ∀ r, (Q r).tensorPow n ≅ 𝟙_ X.Modules) {m : ℕ}
    (eqv : Fin (m + 1) ≃ (Fin M → Λ)) :
    CoordinateAtlas.IsAtlas (V := fun i => (chart i).W)
      (fun i a => (chart i).coord τ (eqv a)) where
  covers x := by
    obtain ⟨i, hx⟩ := hcov x
    refine ⟨i, eqv.symm (chart i).ρ, ?_⟩
    simp only [Equiv.apply_symm_apply]
    rw [Scheme.basicOpen_of_isUnit _ ((chart i).isUnit_coord_frame τ)]
    exact hx
  compat i k := by
    refine ⟨(((chart i).isUnit_det_trans (chart k)).pow n).unit, fun a => ?_⟩
    rw [IsUnit.unit_spec]
    exact (chart i).coord_change τ (chart k) (eqv a)


end Langlands.AlgebraicGeometry.EvaluationBracket
