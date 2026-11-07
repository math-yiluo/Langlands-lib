import Langlands.Algebra.FiniteBialgebraHom
import Langlands.Algebra.HopfPointExtension
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra
import Mathlib.RingTheory.Bialgebra.MonoidAlgebra

/-! # Hopf points into `C ⊗ R[M]` and into `C[M]` -/

noncomputable section

universe u v

open TensorProduct

namespace Langlands.Algebra.HopfPointBridge

open HopfPointExtension

variable {R : Type u} [CommRing R] {A : Type u} [CommRing A] [Bialgebra R A]
  {C : Type v} [CommRing C] [Algebra R C] {M : Type u} [AddCommGroup M]

variable (R C M) in
/-- The scalar extension `C ⊗[R] R[M] ≅ C[M]`, as an `R`-algebra map. -/
abbrev scalarMap : C ⊗[R] AddMonoidAlgebra R M →ₐ[R] AddMonoidAlgebra C M :=
  (AddMonoidAlgebra.scalarTensorEquiv R C (M := M)).toAlgHom.restrictScalars R

/-- A point `A → C ⊗[R] R[M]` viewed as a point `A → C[M]`. -/
abbrev toGroupAlgebra (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    A →ₐ[R] AddMonoidAlgebra C M :=
  (scalarMap R C M).comp f

@[simp] theorem scalarMap_tmul_single (c : C) (a : M) (r : R) :
    scalarMap R C M (c ⊗ₜ AddMonoidAlgebra.single a r) =
      AddMonoidAlgebra.single a (c * algebraMap R C r) := by
  simp [scalarMap, AddMonoidAlgebra.scalarTensorEquiv_tmul]

variable (R C M) in
/-- The comparison `C ⊗[R] (R[M] ⊗[R] R[M]) → C[M × M]`. -/
def squareMap : C ⊗[R] (AddMonoidAlgebra R M ⊗[R] AddMonoidAlgebra R M) →ₐ[R]
    AddMonoidAlgebra C (M × M) :=
  Algebra.TensorProduct.lift
    ((Algebra.ofId C (AddMonoidAlgebra C (M × M))).restrictScalars R)
    (Algebra.TensorProduct.lift
      ((inlMap R C M).comp (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R C)))
      ((inrMap R C M).comp (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R C)))
      (fun _ _ => Commute.all _ _))
    (fun _ _ => Commute.all _ _)

theorem squareMap_tmul (c : C) (a b : M) (r s : R) :
    squareMap R C M (c ⊗ₜ (AddMonoidAlgebra.single a r ⊗ₜ AddMonoidAlgebra.single b s)) =
      AddMonoidAlgebra.single (a, b) (c * algebraMap R C r * algebraMap R C s) := by
  simp [squareMap, inlMap, inrMap, AddMonoidAlgebra.single_mul_single, Algebra.ofId_apply,
    AddMonoidAlgebra.coe_algebraMap, mul_assoc]

theorem squareMap_comp_map_comul :
    (squareMap R C M).comp
        (Algebra.TensorProduct.map (AlgHom.id R C)
          (Bialgebra.comulAlgHom R (AddMonoidAlgebra R M))) =
      (diagMap R C M).comp (scalarMap R C M) := by
  apply Algebra.TensorProduct.ext'
  intro c p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
  | single a r =>
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Bialgebra.comulAlgHom_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply,
      TensorProduct.map_tmul, AddMonoidAlgebra.lsingle_apply, scalarMap_tmul_single, diagMap,
      AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    rw [squareMap_tmul]
    simp

theorem squareMap_comp_inclFirst :
    (squareMap R C M).comp
        (FiniteBialgebraHom.inclFirst R (C := C) (P := AddMonoidAlgebra R M)) =
      (inlMap R C M).comp (scalarMap R C M) := by
  apply Algebra.TensorProduct.ext'
  intro c p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
  | single a r =>
    simp only [AlgHom.comp_apply, FiniteBialgebraHom.inclFirst, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.TensorProduct.includeLeft_apply, scalarMap_tmul_single, inlMap,
      AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    rw [AddMonoidAlgebra.one_def, squareMap_tmul]
    simp

theorem squareMap_comp_inclSecond :
    (squareMap R C M).comp
        (FiniteBialgebraHom.inclSecond R (C := C) (P := AddMonoidAlgebra R M)) =
      (inrMap R C M).comp (scalarMap R C M) := by
  apply Algebra.TensorProduct.ext'
  intro c p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
  | single a r =>
    simp only [AlgHom.comp_apply, FiniteBialgebraHom.inclSecond, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.TensorProduct.includeRight_apply, scalarMap_tmul_single, inrMap,
      AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
    rw [AddMonoidAlgebra.one_def, squareMap_tmul]
    simp

theorem groupCounit_comp_scalarMap :
    (groupCounit R C M).comp (scalarMap R C M) =
      (Algebra.TensorProduct.rid R R C).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id R C)
          (Bialgebra.counitAlgHom R (AddMonoidAlgebra R M))) := by
  apply Algebra.TensorProduct.ext'
  intro c p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
  | single a r =>
    simp [groupCounit, AddMonoidAlgebra.lift_single, Algebra.smul_def, mul_comm]

theorem squareMap_injective : Function.Injective (squareMap R C M) := by
  let L : C ⊗[R] (AddMonoidAlgebra R M ⊗[R] AddMonoidAlgebra R M) ≃ₗ[R]
      C ⊗[R] AddMonoidAlgebra R (M × M) :=
    LinearEquiv.lTensor C (AddMonoidAlgebra.tensorEquiv R)
  let E : C ⊗[R] AddMonoidAlgebra R (M × M) ≃ₗ[R] AddMonoidAlgebra C (M × M) :=
    (AddMonoidAlgebra.scalarTensorEquiv R C (M := M × M)).toLinearEquiv.restrictScalars R
  have h : ∀ x, squareMap R C M x = E (L x) := by
    intro x
    induction x with
    | tmul c y =>
      induction y with
      | tmul p q =>
        induction p using AddMonoidAlgebra.induction_linear with
        | zero => simp
        | add p p' hp hp' => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add,
            hp, hp']
        | single a r =>
          induction q using AddMonoidAlgebra.induction_linear with
          | zero => simp
          | add q q' hq hq' => simp only [TensorProduct.tmul_add, map_add, hq, hq']
          | single b t =>
            rw [squareMap_tmul]
            simp [L, E, AddMonoidAlgebra.scalarTensorEquiv_tmul, mul_comm, mul_left_comm]
      | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | add x x' hx hx' => simp only [map_add, hx, hx']
  intro x y hxy
  rw [h, h] at hxy
  exact L.injective (E.injective hxy)

/-- The two notions of Hopf point agree under `C ⊗[R] R[M] ≅ C[M]`. -/
theorem isHopfPoint_iff (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    FiniteBialgebraHom.IsHopfPoint R f ↔ IsHopfPoint (toGroupAlgebra f) := by
  have hleft : (squareMap R C M).comp (FiniteBialgebraHom.comulLeft R f) =
      (diagMap R C M).comp (toGroupAlgebra f) := by
    rw [FiniteBialgebraHom.comulLeft, ← AlgHom.comp_assoc, squareMap_comp_map_comul,
      AlgHom.comp_assoc]
  have hright : (squareMap R C M).comp (FiniteBialgebraHom.comulRight R f) =
      (pairMap (toGroupAlgebra f)).comp (Bialgebra.comulAlgHom R A) := by
    rw [FiniteBialgebraHom.comulRight, ← AlgHom.comp_assoc]
    congr 1
    apply Algebra.TensorProduct.ext'
    intro a b
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.lift_tmul, map_mul, pairMap]
    rw [← AlgHom.comp_apply (squareMap R C M), squareMap_comp_inclFirst,
      ← AlgHom.comp_apply (squareMap R C M), squareMap_comp_inclSecond]
    rfl
  have hcounit : FiniteBialgebraHom.counitMap R f = (groupCounit R C M).comp (toGroupAlgebra f) := by
    rw [FiniteBialgebraHom.counitMap, ← AlgHom.comp_assoc, groupCounit_comp_scalarMap]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · rw [← hright, ← h1, hleft]
    · rw [← hcounit, h2]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · apply AlgHom.ext
      intro a
      apply squareMap_injective
      have := congrArg (fun F => F a) (hleft.trans (h1.symm.trans hright.symm))
      simpa using this
    · rw [hcounit, h2]

theorem scalarMap_comp_map {D : Type*} [CommRing D] [Algebra R D] (g : C →ₐ[R] D) :
    (scalarMap R D M).comp (Algebra.TensorProduct.map g (AlgHom.id R (AddMonoidAlgebra R M))) =
      (AddMonoidAlgebra.mapAlgHom M g).comp (scalarMap R C M) := by
  classical
  apply Algebra.TensorProduct.ext'
  intro c p
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [TensorProduct.tmul_add, map_add, hp, hq]
  | single a r =>
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      scalarMap_tmul_single]
    apply AddMonoidAlgebra.coeff_injective
    ext b
    rw [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_single,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    split_ifs
    · rw [map_mul, AlgHom.commutes]
    · rw [map_zero]

/-- Changing coefficients of a point commutes with `toGroupAlgebra`. -/
theorem toGroupAlgebra_pushPoint {D : Type*} [CommRing D] [Algebra R D] (g : C →ₐ[R] D)
    (f : A →ₐ[R] C ⊗[R] AddMonoidAlgebra R M) :
    toGroupAlgebra (FiniteBialgebraHom.pushPoint R g f) =
      (AddMonoidAlgebra.mapAlgHom M g).comp (toGroupAlgebra f) := by
  rw [toGroupAlgebra, FiniteBialgebraHom.pushPoint, ← AlgHom.comp_assoc, scalarMap_comp_map,
    AlgHom.comp_assoc]

end Langlands.Algebra.HopfPointBridge
