import Langlands.GroupScheme.IntegralModel.Smoothening.TerminationGamma
import Langlands.GroupScheme.IntegralModel.Smoothening.Smoothness
import Mathlib.RingTheory.HopfAlgebra.Quotient
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # The closure of the reduced integral points is smooth

Let `C` be a commutative Hopf algebra over a local ring `R` with residue field `k`, and let `Γ` be a
set of `R`-points of `C` containing the counit and stable under products and the antipode. The
functions on `k ⊗ C` vanishing at the reductions of the points of `Γ` form a Hopf ideal `Jbar`.
The quotient is the coordinate ring of the Zariski closure `Y` of the reduced points. It is
reduced, so it is smooth over `k` when `k` is algebraically closed. -/

noncomputable section

universe u

open scoped TensorProduct
open IsLocalRing Coalgebra Bialgebra HopfAlgebra

namespace Langlands.GroupScheme.IntegralModel.Smoothening.Termination

variable {R : Type u} [CommRing R] [IsLocalRing R] {C : Type u} [CommRing C] [HopfAlgebra R C]

/-- The functions on the special fibre vanishing at the reductions of the points of `Γ`. -/
def jbar (Γ : Set (C →ₐ[R] R)) : Ideal (ResidueField R ⊗[R] C) :=
  ⨅ φ ∈ Γ, RingHom.ker (evPt φ)

theorem mem_jbar {Γ : Set (C →ₐ[R] R)} {x : ResidueField R ⊗[R] C} :
    x ∈ jbar Γ ↔ ∀ φ ∈ Γ, evPt φ x = 0 := by
  simp [jbar, Submodule.mem_iInf, RingHom.mem_ker]

theorem counit_eq_evPt (x : ResidueField R ⊗[R] C) :
    counit (R := ResidueField R) x = evPt (counitAlgHom R C) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    rw [TensorProduct.counit_tmul, evPt_tmul, Algebra.smul_def, mul_comm]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem lid_map_evPt_comul (φ ψ : C →ₐ[R] R) (x : ResidueField R ⊗[R] C) :
    TensorProduct.lid (ResidueField R) (ResidueField R)
        (TensorProduct.map (evPt φ).toLinearMap (evPt ψ).toLinearMap (comul x)) =
      evPt ((Algebra.TensorProduct.lift φ ψ (fun _ _ => .all _ _)).comp (comulAlgHom R C)) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, evPt_tmul, AlgHom.comp_apply,
      comulAlgHom_apply]
    induction (comul (R := R) c) using TensorProduct.inductionOn with
    | tmul p q =>
      rw [TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul]
      simp only [TensorProduct.map_tmul, AlgHom.toLinearMap_apply, evPt_tmul,
        TensorProduct.lid_tmul, smul_eq_mul, Algebra.TensorProduct.lift_tmul, map_mul]
      ring
    | add v w hv hw =>
      rw [TensorProduct.tmul_add, map_add, map_add, map_add, hv, hw, map_add, map_add, mul_add]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

theorem evPt_antipode (φ : C →ₐ[R] R) (x : ResidueField R ⊗[R] C) :
    evPt φ (antipode (ResidueField R) x) = evPt (φ.comp (antipodeAlgHom R C)) x := by
  induction x using TensorProduct.inductionOn with
  | tmul a c =>
    rw [TensorProduct.antipode_def, TensorProduct.AlgebraTensorModule.map_tmul,
      CommSemiring.antipode_eq_id, LinearMap.id_apply, evPt_tmul, evPt_tmul, AlgHom.comp_apply]
    rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

section HopfIdeal

variable {Γ : Set (C →ₐ[R] R)}
  (h1 : counitAlgHom R C ∈ Γ)
  (h2 : ∀ φ ∈ Γ, ∀ ψ ∈ Γ,
    (Algebra.TensorProduct.lift φ ψ (fun _ _ => .all _ _)).comp (comulAlgHom R C) ∈ Γ)
  (h3 : ∀ φ ∈ Γ, φ.comp (antipodeAlgHom R C) ∈ Γ)

/-- The forms on the quotient by `Jbar` given by the points. -/
def quotEv (Γ : Set (C →ₐ[R] R)) (φ : Γ) :
    (ResidueField R ⊗[R] C) ⧸ (jbar Γ).restrictScalars (ResidueField R) →ₗ[ResidueField R]
      ResidueField R :=
  Submodule.liftQ _ (evPt (φ : C →ₐ[R] R)).toLinearMap fun x hx => by
    rw [LinearMap.mem_ker]
    exact (mem_jbar.mp hx) φ φ.2

theorem quotEv_detects (Γ : Set (C →ₐ[R] R)) : Detects (quotEv Γ) := by
  intro v hv
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  rw [Submodule.Quotient.mk_eq_zero, Submodule.restrictScalars_mem, mem_jbar]
  intro φ hφ
  exact hv ⟨φ, hφ⟩

include h1 h2 h3 in
theorem isHopfIdeal_jbar : (jbar Γ).IsHopfIdeal (ResidueField R) where
  counit_eq_zero x hx := by
    rw [counit_eq_evPt]
    exact (mem_jbar.mp hx) _ h1
  map_mkQ_comul_eq_zero x hx := by
    refine detects_tensor (quotEv_detects Γ) (quotEv_detects Γ) _ fun φ ψ => ?_
    have hcomp : ∀ θ : Γ, quotEv Γ θ ∘ₗ ((jbar Γ).restrictScalars (ResidueField R)).mkQ =
        (evPt (θ : C →ₐ[R] R)).toLinearMap := fun θ => by
      ext y
      rfl
    rw [← LinearMap.comp_apply (TensorProduct.map _ _), ← TensorProduct.map_comp, hcomp, hcomp,
      lid_map_evPt_comul]
    exact (mem_jbar.mp hx) _ (h2 _ φ.2 _ ψ.2)
  antipode_mem x hx := by
    rw [mem_jbar]
    intro φ hφ
    rw [evPt_antipode]
    exact (mem_jbar.mp hx) _ (h3 _ hφ)

theorem jbar_isRadical (Γ : Set (C →ₐ[R] R)) : (jbar Γ).IsRadical := by
  intro x ⟨n, hn⟩
  rw [mem_jbar] at hn ⊢
  intro φ hφ
  have := hn φ hφ
  rw [map_pow] at this
  exact pow_eq_zero_iff'.mp this |>.1

include h1 h2 h3 in
/-- **The closure of the reduced points is smooth.** -/
theorem smooth_quotient_jbar [IsAlgClosed (ResidueField R)] [Algebra.FiniteType R C] :
    Algebra.Smooth (ResidueField R) ((ResidueField R ⊗[R] C) ⧸ jbar Γ) := by
  have := isHopfIdeal_jbar h1 h2 h3
  have : IsReduced ((ResidueField R ⊗[R] C) ⧸ jbar Γ) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp (jbar_isRadical Γ)
  exact smooth_of_isReduced_of_isAlgClosed _

end HopfIdeal

section PtLocus

variable {C' : Type u} [CommRing C'] [Algebra R C'] (Γ : Set (C' →ₐ[R] R))

/-- The elements whose values at all points of `Γ` lie in the maximal ideal. -/
def ptLocus : Ideal C' := ⨅ φ ∈ Γ, (maximalIdeal R).comap φ

theorem mem_ptLocus {c : C'} : c ∈ ptLocus Γ ↔ ∀ φ ∈ Γ, φ c ∈ maximalIdeal R := by
  simp [ptLocus, Submodule.mem_iInf]

end PtLocus

section Bridge

variable (Γ : Set (C →ₐ[R] R))

/-- The map from `C` to the coordinate ring of the closure of the reduced points. -/
def quotMap : C →ₐ[R] (ResidueField R ⊗[R] C) ⧸ jbar Γ :=
  (Ideal.Quotient.mkₐ R (jbar Γ)).comp Algebra.TensorProduct.includeRight

theorem quotMap_apply (c : C) :
    quotMap Γ c = Ideal.Quotient.mk (jbar Γ) ((1 : ResidueField R) ⊗ₜ c) := rfl

theorem quotMap_surjective : Function.Surjective (quotMap Γ) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨c, rfl⟩ := exists_one_tmul_eq x
  exact ⟨c, rfl⟩

theorem ker_quotMap : RingHom.ker (quotMap Γ) = ptLocus Γ := by
  ext c
  rw [RingHom.mem_ker, quotMap_apply, Ideal.Quotient.eq_zero_iff_mem, mem_jbar, mem_ptLocus]
  refine forall₂_congr fun φ _ => ?_
  rw [evPt_tmul, one_mul, IsLocalRing.ResidueField.algebraMap_eq, residue_eq_zero_iff]

variable {Γ} in
/-- The identity point of the closure of the reduced points. -/
def quotPoint (h1 : counitAlgHom R C ∈ Γ) :
    (ResidueField R ⊗[R] C) ⧸ jbar Γ →ₐ[ResidueField R] ResidueField R :=
  Ideal.Quotient.liftₐ (jbar Γ) (evPt (counitAlgHom R C)) fun _ hx => (mem_jbar.mp hx) _ h1

theorem quotPoint_quotMap {Γ : Set (C →ₐ[R] R)} (h1 : counitAlgHom R C ∈ Γ) (c : C) :
    quotPoint h1 (quotMap Γ c) = residue R (counitAlgHom R C c) := by
  change evPt (counitAlgHom R C) ((1 : ResidueField R) ⊗ₜ c) = _
  rw [evPt_tmul, one_mul, IsLocalRing.ResidueField.algebraMap_eq]

end Bridge

end Langlands.GroupScheme.IntegralModel.Smoothening.Termination
