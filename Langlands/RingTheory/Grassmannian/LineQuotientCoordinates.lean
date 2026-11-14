import Langlands.RingTheory.Grassmannian.Charts
import Langlands.RingTheory.Grassmannian.ProjectiveEmbedding

/-! # Coordinates of rank-one quotients on the charts of the Grassmannian

For a rank-one quotient `N` of `A ⊗ Q` in the chart of `x : Q` (the class of `1 ⊗ x` is a basis
of the quotient) we write `coord x N : Q →ₗ[R] A` for the coordinate of the class of `1 ⊗ m` in
that basis. Coordinates are natural in `A` and change by a unit between charts. Conversely, every
`v : Q →ₗ[R] A` whose values generate the unit ideal defines the rank-one quotient
`A ⊗ Q → A`. -/

universe u

open TensorProduct

noncomputable section

namespace Langlands.RingTheory.Grassmannian.LineQuotientCoordinates

open Module.Grassmannian.ProjectiveEmbedding (InChart)

variable {R : Type u} [CommRing R] {Q : Type u} [AddCommGroup Q] [Module R Q]

/-- The chosen chart equivalences of the chart of `x`. -/
def chartPts (x : Q) :=
  (Module.Grassmannian.exists_chart_equiv_linearMap R Q 1 (fun _ => x)).choose

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The coordinate map of a rank-one quotient in the chart of `x`.** -/
def coord (x : Q) (N : Module.Grassmannian A (A ⊗[R] Q) 1) (hN : InChart (fun _ => x) N) :
    Q →ₗ[R] A :=
  (LinearMap.proj (0 : Fin 1)) ∘ₗ (chartPts x A ⟨N, hN⟩).1

lemma coord_self (x : Q) (N : Module.Grassmannian A (A ⊗[R] Q) 1)
    (hN : InChart (fun _ => x) N) : coord x N hN x = 1 := by
  have h := (chartPts x A ⟨N, hN⟩).2 0
  simp only [coord, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
    Function.eval]
  rw [h]
  rfl

lemma coord_spec (x : Q) (N : Module.Grassmannian A (A ⊗[R] Q) 1)
    (hN : InChart (fun _ => x) N) (m : Q) :
    coord x N hN m • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x) = N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] m) := by
  have h := (Module.Grassmannian.exists_chart_equiv_linearMap R Q 1 (fun _ => x)).choose_spec.1 A ⟨N, hN⟩ m
  simp only [Fin.sum_univ_one] at h
  exact h

lemma smul_basis_injective (x : Q) (N : Module.Grassmannian A (A ⊗[R] Q) 1)
    (hN : InChart (fun _ => x) N) {a a' : A}
    (h : a • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x) = a' • N.toSubmodule.mkQ ((1 : A) ⊗ₜ[R] x)) :
    a = a' := by
  have := hN.1 (a₁ := fun _ => a) (a₂ := fun _ => a') (by simpa [Fin.sum_univ_one] using h)
  exact congrFun this 0

/-- **Coordinates are natural in the algebra.** -/
lemma coord_map {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (x : Q)
    (N : Module.Grassmannian A (A ⊗[R] Q) 1) (hN : InChart (fun _ => x) N)
    (hN' : InChart (fun _ => x) (Module.Grassmannian.map φ N)) :
    coord x (Module.Grassmannian.map φ N) hN' = φ.toLinearMap ∘ₗ coord x N hN := by
  obtain ⟨h, hh⟩ := (Module.Grassmannian.exists_chart_equiv_linearMap R Q 1 (fun _ => x)).choose_spec.2.2 A B φ ⟨N, hN⟩
  ext m
  exact hh m 0

/-- **Change of chart.** -/
lemma coord_change (x x' : Q) (N : Module.Grassmannian A (A ⊗[R] Q) 1)
    (hN : InChart (fun _ => x) N) (hN' : InChart (fun _ => x') N) :
    IsUnit (coord x N hN x') ∧ coord x N hN = coord x N hN x' • coord x' N hN' := by
  have key : ∀ m, coord x N hN m = coord x N hN x' * coord x' N hN' m := by
    intro m
    apply smul_basis_injective x N hN
    rw [coord_spec, ← coord_spec x' N hN' m, ← coord_spec x N hN x', smul_smul, mul_comm]
  refine ⟨isUnit_iff_exists_inv.mpr ⟨coord x' N hN' x, ?_⟩, ?_⟩
  · rw [← key, coord_self]
  · ext m
    rw [LinearMap.smul_apply, smul_eq_mul, key]

section LinePoint

lemma liftBaseChange_surjective (v : Q →ₗ[R] A) (hv : Ideal.span (Set.range v) = ⊤) :
    Function.Surjective (v.liftBaseChange A) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  have hle : Ideal.span (Set.range v) ≤ LinearMap.range (v.liftBaseChange A) := by
    rw [Ideal.span_le]
    rintro _ ⟨q, rfl⟩
    exact ⟨(1 : A) ⊗ₜ q, by simp⟩
  rw [hv] at hle
  exact hle

/-- **The rank-one quotient `A ⊗ Q → A` given by `v`.** -/
def linePt (v : Q →ₗ[R] A) (hv : Ideal.span (Set.range v) = ⊤) :
    Module.Grassmannian A (A ⊗[R] Q) 1 :=
  let e := (v.liftBaseChange A).quotKerEquivOfSurjective (liftBaseChange_surjective v hv)
  { toSubmodule := LinearMap.ker (v.liftBaseChange A)
    finite_quotient := Module.Finite.equiv e.symm
    projective_quotient := Module.Projective.of_equiv e.symm
    rankAtStalk_eq := fun p => by
      have : Nontrivial A := by
        by_contra h
        have := not_nontrivial_iff_subsingleton.mp h
        exact IsEmpty.false p
      rw [Module.rankAtStalk_eq_of_equiv e, Module.rankAtStalk_eq_finrank_of_free,
        Module.finrank_self]
      rfl }

lemma linePt_toSubmodule (v : Q →ₗ[R] A) (hv : Ideal.span (Set.range v) = ⊤) :
    (linePt v hv).toSubmodule = LinearMap.ker (v.liftBaseChange A) := rfl

/-- The class of `1 ⊗ m` in the quotient corresponds to `v m`. -/
lemma linePt_mkQ_eq_iff (v : Q →ₗ[R] A) (hv : Ideal.span (Set.range v) = ⊤) (z z' : A ⊗[R] Q) :
    (linePt v hv).toSubmodule.mkQ z = (linePt v hv).toSubmodule.mkQ z' ↔
      v.liftBaseChange A z = v.liftBaseChange A z' := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, linePt_toSubmodule,
    LinearMap.mem_ker, map_sub, sub_eq_zero]

lemma linePt_inChart (v : Q →ₗ[R] A) (hv : Ideal.span (Set.range v) = ⊤) (x : Q)
    (hx : IsUnit (v x)) : InChart (fun _ => x) (linePt v hv) := by
  constructor
  · intro a a' h
    simp only [Fin.sum_univ_one] at h
    rw [← map_smul, ← map_smul, linePt_mkQ_eq_iff] at h
    simp only [map_smul, LinearMap.liftBaseChange_tmul, smul_eq_mul, one_mul] at h
    funext i
    rw [Subsingleton.elim i 0]
    exact hx.mul_left_injective h
  · intro z
    obtain ⟨w, rfl⟩ := Submodule.mkQ_surjective _ z
    refine ⟨fun _ => v.liftBaseChange A w * hx.unit⁻¹, ?_⟩
    simp only [Fin.sum_univ_one]
    rw [← map_smul, linePt_mkQ_eq_iff, map_smul, LinearMap.liftBaseChange_tmul, one_smul,
      smul_eq_mul, mul_assoc, IsUnit.val_inv_mul, mul_one]

/-- Coordinates of the quotient defined by `v`. -/
lemma coord_linePt (v : Q →ₗ[R] A) (hv : Ideal.span (Set.range v) = ⊤) (x : Q)
    (hx : IsUnit (v x)) (hN : InChart (fun _ => x) (linePt v hv)) :
    coord x (linePt v hv) hN = (↑hx.unit⁻¹ : A) • v := by
  ext m
  have h := coord_spec x (linePt v hv) hN m
  rw [← map_smul, linePt_mkQ_eq_iff, map_smul, LinearMap.liftBaseChange_tmul,
    LinearMap.liftBaseChange_tmul, one_smul, one_smul, smul_eq_mul] at h
  rw [LinearMap.smul_apply, smul_eq_mul, ← h, mul_comm, mul_assoc, IsUnit.mul_val_inv, mul_one]

/-- **Base change of the quotient defined by `v`.** -/
lemma map_linePt {B : Type u} [CommRing B] [Algebra R B] (φ : A →ₐ[R] B) (v : Q →ₗ[R] A)
    (hv : Ideal.span (Set.range v) = ⊤) (hv' : Ideal.span (Set.range (φ.toLinearMap ∘ₗ v)) = ⊤) :
    Module.Grassmannian.map φ (linePt v hv) = linePt (φ.toLinearMap ∘ₗ v) hv' := by
  let _ : Algebra A B := φ.toAlgebra
  let _ : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  ext1
  rw [Module.Grassmannian.map_toSubmodule, linePt_toSubmodule, linePt_toSubmodule]
  let e := (v.liftBaseChange A).quotKerEquivOfSurjective (liftBaseChange_surjective v hv)
  let Φ : B ⊗[A] ((A ⊗[R] Q) ⧸ LinearMap.ker (v.liftBaseChange A)) ≃ₗ[B] B :=
    (e.baseChange A B _ _).trans (TensorProduct.AlgebraTensorModule.rid A B B)
  have hcomp : Φ.toLinearMap ∘ₗ Module.Grassmannian.baseChangeMkQ B
      (LinearMap.ker (v.liftBaseChange A)) = (φ.toLinearMap ∘ₗ v).liftBaseChange B := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext b
    simp [Φ, e, Module.Grassmannian.baseChangeMkQ]
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [← hcomp, LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]

/-- A point in a chart is the quotient defined by its coordinates. -/
lemma eq_linePt_coord (x : Q) (N : Module.Grassmannian A (A ⊗[R] Q) 1)
    (hN : InChart (fun _ => x) N)
    (hv : Ideal.span (Set.range (coord x N hN)) = ⊤) :
    N = linePt (coord x N hN) hv := by
  have hker := (Module.Grassmannian.exists_chart_equiv_linearMap R Q 1 (fun _ => x)).choose_spec.2.1
    A (chartPts x A ⟨N, hN⟩)
  have e1 : ((Module.Grassmannian.exists_chart_equiv_linearMap R Q 1 (fun _ => x)).choose A).symm
      (chartPts x A ⟨N, hN⟩) = ⟨N, hN⟩ := Equiv.symm_apply_apply _ _
  rw [e1] at hker
  ext1
  rw [linePt_toSubmodule]
  change N.toSubmodule = _ at hker
  rw [hker]
  ext z
  simp only [LinearMap.mem_ker]
  have hcomp : (LinearMap.proj (R := A) (φ := fun _ : Fin 1 => A) 0) ∘ₗ
      ((chartPts x A ⟨N, hN⟩).1.liftBaseChange A) = (coord x N hN).liftBaseChange A := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext a q
    simp [coord]
  constructor
  · intro h
    rw [← hcomp, LinearMap.comp_apply, h, map_zero]
  · intro h
    rw [← hcomp, LinearMap.comp_apply] at h
    funext i
    rw [Subsingleton.elim i 0]
    exact h

/-- Scaling by a unit does not change the quotient. -/
lemma linePt_smul (v : Q →ₗ[R] A) (hv : Ideal.span (Set.range v) = ⊤) (c : A) (hc : IsUnit c)
    (hv' : Ideal.span (Set.range (c • v)) = ⊤) : linePt (c • v) hv' = linePt v hv := by
  ext1
  rw [linePt_toSubmodule, linePt_toSubmodule]
  have h : (c • v).liftBaseChange A = c • v.liftBaseChange A := by
    apply TensorProduct.AlgebraTensorModule.curry_injective
    ext a q
    simp [smul_eq_mul, mul_left_comm]
  ext z
  simp only [LinearMap.mem_ker, h, LinearMap.smul_apply, smul_eq_mul]
  exact ⟨fun h0 => (hc.mul_right_eq_zero).1 h0, fun h0 => by rw [h0, mul_zero]⟩

/-- In the chart of `x`, the value of `v` at `x` is a unit. -/
lemma isUnit_of_inChart_linePt (v : Q →ₗ[R] A) (hv : Ideal.span (Set.range v) = ⊤) (x : Q)
    (hN : InChart (fun _ => x) (linePt v hv)) : IsUnit (v x) := by
  obtain ⟨z, hz⟩ := liftBaseChange_surjective v hv 1
  obtain ⟨a, ha⟩ := hN.2 ((linePt v hv).toSubmodule.mkQ z)
  simp only [Fin.sum_univ_one] at ha
  rw [← map_smul, linePt_mkQ_eq_iff, map_smul, LinearMap.liftBaseChange_tmul, one_smul, hz,
    smul_eq_mul] at ha
  exact isUnit_iff_exists_inv'.mpr ⟨a 0, ha⟩

end LinePoint

end Langlands.RingTheory.Grassmannian.LineQuotientCoordinates
