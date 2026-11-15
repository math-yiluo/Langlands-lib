import Langlands.Representation.Archimedean.BGChaseEnveloping

/-!
# The Bernstein–Gelfand chase: the map `E ⊗ U → V`

Data of the bimodule statement (two commuting representations `ℓ`, `r` of `𝔤𝔩_n(ℂ)` on `V`
and a subspace `E` stable under `ℓ(Y) - r(Yᵀ)`), the representation `κ(Y) = r(Y) - ℓ(Yᵀ)` on `E`,
and the map `p : E ⊗ U → V`, `e ⊗ u ↦ ρ(u) e` with `ρ(u) = Λ_ℓ(uᵗ)`.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean.BGChase

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Algebra.UniversalEnveloping

universe uV uX uY uZ

variable {n : ℕ}

local notation "gl" => Matrix (Fin n) (Fin n) ℂ
local notation "U" => UniversalEnvelopingAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)

/-! ## Tensor product lemmas -/

section Tensor

variable {X : Type uX} [AddCommGroup X] [Module ℂ X] {Y : Type uY} [AddCommGroup Y] [Module ℂ Y]
  {Z : Type uZ} [AddCommGroup Z] [Module ℂ Z]

/-- Contracting the left factor with `α` commutes with a map on the right factor. -/
theorem lid_rTensor_lTensor (α : X →ₗ[ℂ] ℂ) (φ : Y →ₗ[ℂ] Z) (t : X ⊗[ℂ] Y) :
    TensorProduct.lid ℂ Z (LinearMap.rTensor Z α (LinearMap.lTensor X φ t)) =
      φ (TensorProduct.lid ℂ Y (LinearMap.rTensor Y α t)) := by
  induction t with
  | tmul x y =>
    simp only [LinearMap.lTensor_tmul, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul]
  | add a b ha hb => simp only [map_add, ha, hb]

/-- Expansion of a tensor along a basis of the left factor. -/
theorem eq_sum_basis_tmul {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ X) (t : X ⊗[ℂ] Y) :
    t = ∑ i, b i ⊗ₜ TensorProduct.lid ℂ Y (LinearMap.rTensor Y (b.coord i) t) := by
  induction t with
  | tmul x y =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, TensorProduct.tmul_smul,
      Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr x]
    rw [TensorProduct.sum_tmul]
    exact Finset.sum_congr rfl fun i _ => (TensorProduct.smul_tmul' _ _ _).symm
  | add a c ha hc =>
    simp only [map_add, TensorProduct.tmul_add, Finset.sum_add_distrib]
    rw [← ha, ← hc]

end Tensor

/-! ## The data -/

/-- The data of the bimodule statement: commuting representations `ℓ`, `r` of `𝔤𝔩_n(ℂ)` on `V`
and a subspace `E` stable under `ℓ(Y) - r(Yᵀ)`. -/
structure BData (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V] where
  /-- The left representation. -/
  ℓ : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V
  /-- The right representation. -/
  r : Matrix (Fin n) (Fin n) ℂ →ₗ⁅ℂ⁆ Module.End ℂ V
  comm : ∀ X Y, ℓ X * r Y = r Y * ℓ X
  /-- The subspace. -/
  E : Submodule ℂ V
  stable : ∀ Y : Matrix (Fin n) (Fin n) ℂ, ∀ e ∈ E, ℓ Y e - r Y.transpose e ∈ E

namespace BData

variable {V : Type uV} [AddCommGroup V] [Module ℂ V] (D : BData n V)

/-- The representation `κ(Y) = r(Y) - ℓ(Yᵀ)` of `𝔤𝔩_n(ℂ)` on `V`. -/
def kappa : gl →ₗ⁅ℂ⁆ Module.End ℂ V where
  toFun Y := D.r Y - D.ℓ Y.transpose
  map_add' X Y := by simp only [map_add, Matrix.transpose_add]; abel
  map_smul' c Y := by
    simp only [map_smul, Matrix.transpose_smul, RingHom.id_apply, smul_sub]
  map_lie' {X Y} := by
    have h1 : (⁅X, Y⁆ : gl).transpose = ⁅Y.transpose, X.transpose⁆ := by
      rw [Ring.lie_def, Ring.lie_def, Matrix.transpose_sub, Matrix.transpose_mul,
        Matrix.transpose_mul]
    show D.r ⁅X, Y⁆ - D.ℓ (⁅X, Y⁆ : gl).transpose =
      ⁅D.r X - D.ℓ X.transpose, D.r Y - D.ℓ Y.transpose⁆
    rw [h1, LieHom.map_lie, LieHom.map_lie, Ring.lie_def, Ring.lie_def, Ring.lie_def]
    simp only [sub_mul, mul_sub]
    rw [D.comm X.transpose Y, D.comm Y.transpose X]
    abel

theorem kappa_apply (Y : gl) : D.kappa Y = D.r Y - D.ℓ Y.transpose := rfl

theorem kappa_mem (Y : gl) {e : V} (he : e ∈ D.E) : D.kappa Y e ∈ D.E := by
  have h := D.E.neg_mem (D.stable Y.transpose e he)
  rw [Matrix.transpose_transpose, neg_sub] at h
  exact h

/-- The representation `κ` restricted to `E`. -/
def kE : gl →ₗ⁅ℂ⁆ Module.End ℂ D.E :=
  restrictLie D.kappa D.E fun Y _ he => D.kappa_mem Y he

theorem kE_apply (Y : gl) (e : D.E) :
    ((D.kE Y e : D.E) : V) = D.r Y e - D.ℓ Y.transpose e := rfl

/-- The representation `κ ⊗ ad` on `E ⊗ U`. -/
def adP : gl →ₗ⁅ℂ⁆ Module.End ℂ (D.E ⊗[ℂ] U) := tensorLie D.kE adU

theorem adP_tmul (Y : gl) (e : D.E) (u : U) :
    D.adP Y (e ⊗ₜ u) = D.kE Y e ⊗ₜ u + e ⊗ₜ adU Y u := rfl

/-- The map `p : E ⊗ U → V`, `e ⊗ u ↦ ρ(u) e`. -/
def pmap : D.E ⊗[ℂ] U →ₗ[ℂ] V := TensorProduct.lift ((rhoR D.ℓ).flip ∘ₗ D.E.subtype)

theorem pmap_tmul (e : D.E) (u : U) : D.pmap (e ⊗ₜ u) = rhoR D.ℓ u e := rfl

theorem pmap_tmul_one (e : D.E) : D.pmap (e ⊗ₜ 1) = e := by
  rw [pmap_tmul, rhoR_one, Module.End.one_apply]

/-- Right multiplication by `u` on the second factor of `E ⊗ U`. -/
def rmul (u : U) : Module.End ℂ (D.E ⊗[ℂ] U) := LinearMap.lTensor D.E (LinearMap.mulRight ℂ u)

theorem rmul_tmul (u : U) (e : D.E) (a : U) : D.rmul u (e ⊗ₜ a) = e ⊗ₜ (a * u) := rfl

theorem pmap_rmul (u : U) (x : D.E ⊗[ℂ] U) : D.pmap (D.rmul u x) = rhoR D.ℓ u (D.pmap x) := by
  induction x with
  | tmul e a => rw [rmul_tmul, pmap_tmul, pmap_tmul, rhoR_mul, Module.End.mul_apply]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem pmap_adP (Y : gl) (x : D.E ⊗[ℂ] U) : D.pmap (D.adP Y x) = D.kappa Y (D.pmap x) := by
  induction x with
  | tmul e a =>
    have hc := LinearMap.congr_fun (rhoR_commute D.ℓ (D.r Y) (fun X => D.comm X Y) a) e
    simp only [Module.End.mul_apply] at hc
    rw [adP_tmul, map_add, pmap_tmul, pmap_tmul, pmap_tmul, kE_apply, adU_apply]
    simp only [map_sub, LinearMap.sub_apply, rhoR_mul, rhoR_ι, Module.End.mul_apply,
      kappa_apply, hc]
    abel
  | add a b ha hb => simp only [map_add, ha, hb]

theorem ℓ_pmap (X : gl) (x : D.E ⊗[ℂ] U) :
    D.ℓ X (D.pmap x) = D.pmap (D.rmul (UniversalEnvelopingAlgebra.ι ℂ X.transpose) x) := by
  rw [pmap_rmul, rhoR_ι, Matrix.transpose_transpose]

/-- If `E` generates `V` under `ℓ`, then `p` is surjective. -/
theorem range_pmap (hgen : ∀ S : Submodule ℂ V, D.E ≤ S → (∀ X, ∀ s ∈ S, D.ℓ X s ∈ S) → S = ⊤) :
    LinearMap.range D.pmap = ⊤ := by
  refine hgen _ (fun e he => ⟨⟨e, he⟩ ⊗ₜ 1, D.pmap_tmul_one ⟨e, he⟩⟩) ?_
  rintro X _ ⟨x, rfl⟩
  exact ⟨_, (D.ℓ_pmap X x).symm⟩

theorem rmul_mem_ker {u : U} {x : D.E ⊗[ℂ] U} (hx : x ∈ LinearMap.ker D.pmap) :
    D.rmul u x ∈ LinearMap.ker D.pmap := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [pmap_rmul, hx, map_zero]

theorem adP_mem_ker (Y : gl) {x : D.E ⊗[ℂ] U} (hx : x ∈ LinearMap.ker D.pmap) :
    D.adP Y x ∈ LinearMap.ker D.pmap := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [pmap_adP, hx, map_zero]

/-- `p` in coordinates along a basis of `E`. -/
theorem pmap_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι ℂ D.E) (x : D.E ⊗[ℂ] U) :
    D.pmap x = ∑ i, rhoR D.ℓ (TensorProduct.lid ℂ U (LinearMap.rTensor U (b.coord i) x)) (b i) := by
  induction x with
  | tmul e u =>
    simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, map_smul, LinearMap.smul_apply,
      pmap_tmul]
    have he : (e : V) = ∑ i, b.coord i e • (b i : V) := by
      conv_lhs => rw [← b.sum_repr e]
      simp only [Module.Basis.coord_apply, Submodule.coe_sum, Submodule.coe_smul]
    conv_lhs => rw [he]
    simp only [map_sum, map_smul]
  | add a c ha hc =>
    simp only [map_add, LinearMap.add_apply, Finset.sum_add_distrib, ha, hc]

/-! ## Integral weights -/

theorem intSpan_kE
    (hW : D.E ≤ Submodule.span ℂ {e | e ∈ D.E ∧ ∃ m : Fin n → ℤ, ∀ p : Fin n,
        D.ℓ (Matrix.single p p 1) e - D.r (Matrix.single p p 1) e = (m p : ℂ) • e}) :
    intSpan (diagOps D.kE) = ⊤ := by
  refine intSpan_restrictLie D.E _ (hW.trans (Submodule.span_mono ?_))
  rintro e ⟨he, m, hm⟩
  refine ⟨he, -m, fun p => ?_⟩
  change D.kappa _ e = _
  rw [kappa_apply, Matrix.transpose_single, LinearMap.sub_apply, ← neg_sub, hm p]
  simp only [Pi.neg_apply, Int.cast_neg, neg_smul]

/-! ## The right action on the annihilator ideal -/

theorem rhoR_eq_zero_of_mem_span (χ : Subalgebra.center ℂ U →ₐ[ℂ] ℂ)
    (hχ : ∀ z : Subalgebra.center ℂ U, rhoR D.ℓ z = algebraMap ℂ (Module.End ℂ V) (χ z)) {u : U}
    (hu : u ∈ Ideal.span {x | ∃ z : Subalgebra.center ℂ U, x = (z : U) - algebraMap ℂ U (χ z)}) :
    rhoR D.ℓ u = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨z, rfl⟩ := hx
    rw [map_sub, hχ, rhoR_algebraMap, sub_self]
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul a x _ hx => rw [smul_eq_mul, rhoR_mul, hx, zero_mul]

end BData

end Langlands.Archimedean.BGChase
