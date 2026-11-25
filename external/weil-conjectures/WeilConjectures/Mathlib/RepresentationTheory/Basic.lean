/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.DirectSum.Finite
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Intertwining
public import WeilConjectures.Mathlib.Algebra.DirectSum.LinearMap
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# The determinant character and the exterior powers of a representation

Two constructions on a monoid representation `ρ : Representation k W V` that Mathlib does not
have, alongside `Representation.tprod` and `Representation.dual`:

* the *determinant character* `δ(w) = det ρ(w)`, a homomorphism `W →* kˣ` (the determinant of
  `ρ w` is a unit because `ρ w` is invertible);
* the representation of `W` on the exterior power `⋀^s V`, by functoriality of `⋀^s`.

## Main declarations

* `Representation.detCharacter`: the determinant character `δ` of a representation.
* `Representation.exteriorPower`: the representation induced on `⋀^s V`.
* `Representation.ofCharacter`: the representation on a module in which `g` acts by the scalar
  `χ g` of a character `χ : G →* kˣ`.
* `Representation.directSumSummand`: a summand of a direct sum of representations, as a
  subrepresentation; the summands form an internal direct sum decomposition
  (`Representation.isInternal_directSumSummand`).
* `Representation.charpoly_directSum`: the characteristic polynomial of `g` acting on a direct
  sum of representations is the product of the characteristic polynomials on the summands.
* `Matrix.GeneralLinearGroup.toRepresentation`: the defining representation of `GL n k` on
  `n → k`.
* `Representation.hasEigenvalue_dual_iff`: the eigenvalues of `g` on the dual representation are
  those of `g⁻¹`.

## Blueprint

`Representation.detCharacter` implements part of `definition-determinant-weight--1`.
`Representation.exteriorPower` is the exterior power `⋀^s V` of `det-d-linear`, and `⋀^r V` for
`r = dim V` its determinant representation.
-/

@[expose] public section

open scoped Matrix

namespace Representation

variable {k : Type*} [Field k] {W : Type*} [Group W]
variable {V : Type*} [AddCommGroup V] [Module k V]

/-- The *determinant character* of a representation `ρ` is the homomorphism `δ(w) = det ρ(w)`,
valued in the units of `k` because `ρ(w)` is invertible.
(blueprint: `definition-determinant-weight--1`) -/
noncomputable def detCharacter (ρ : Representation k W V) : W →* kˣ :=
  (Units.map (LinearMap.det : Module.End k V →* k)).comp (MonoidHom.toHomUnits ρ)

@[simp]
theorem coe_detCharacter_apply (ρ : Representation k W V) (w : W) :
    (ρ.detCharacter w : k) = LinearMap.det (ρ w) :=
  rfl

section Equiv

variable {V' : Type*} [AddCommGroup V'] [Module k V'] {ρ : Representation k W V}
  {σ : Representation k W V'}

/-- An equivalence of representations commutes with the actions. -/
theorem Equiv.apply_apply (e : ρ.Equiv σ) (w : W) (x : V) : e (ρ w x) = σ w (e x) :=
  LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' w) x

/-- Equivalent representations have the same determinant character. -/
theorem Equiv.detCharacter_eq (e : ρ.Equiv σ) : σ.detCharacter = ρ.detCharacter := by
  ext w
  have : σ w = (e.toLinearEquiv : V →ₗ[k] V') ∘ₗ ρ w ∘ₗ (e.toLinearEquiv.symm : V' →ₗ[k] V) := by
    ext x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      e.toLinearEquiv_apply, e.coe_toIntertwiningMap, e.apply_apply]
    exact congrArg _ (e.toLinearEquiv.apply_symm_apply x).symm
  rw [coe_detCharacter_apply, coe_detCharacter_apply, this, LinearMap.det_conj]

end Equiv

/-- The representation induced on the `s`-th exterior power `⋀^s V`, by functoriality of the
exterior power. The name shadows the root namespace `exteriorPower`, whose declarations are
therefore spelled `_root_.exteriorPower.*` below. (blueprint: `det-d-linear`) -/
noncomputable def exteriorPower (ρ : Representation k W V) (s : ℕ) :
    Representation k W ↥(⋀[k]^s V) where
  toFun w := _root_.exteriorPower.map s (ρ w)
  map_one' := by
    rw [map_one]
    exact _root_.exteriorPower.map_id
  map_mul' v w := by
    rw [map_mul]
    exact _root_.exteriorPower.map_comp (ρ w) (ρ v)

section Equiv

variable {k G V V' : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]
  [AddCommGroup V'] [Module k V'] {ρ : Representation k G V} {σ : Representation k G V'}

/-- Equivalent representations are conjugate: `σ g = e ∘ ρ g ∘ e⁻¹`. -/
theorem Equiv.apply_eq_conj (e : ρ.Equiv σ) (g : G) : σ g = e.toLinearEquiv.conj (ρ g) := by
  ext v
  have h := LinearMap.congr_fun (e.isIntertwining' g) (e.toLinearEquiv.symm v)
  change e.toLinearEquiv (ρ g (e.toLinearEquiv.symm v)) =
    σ g (e.toLinearEquiv (e.toLinearEquiv.symm v)) at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Equivalent representations have the same determinants. -/
theorem Equiv.det_apply (e : ρ.Equiv σ) (g : G) :
    LinearMap.det (σ g) = LinearMap.det (ρ g) := by
  rw [e.apply_eq_conj, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj]

/-- Equivalent representations have the same characteristic polynomials. -/
theorem Equiv.charpoly_apply [Module.Finite k V] [Module.Finite k V'] (e : ρ.Equiv σ) (g : G) :
    (σ g).charpoly = (ρ g).charpoly := by
  rw [e.apply_eq_conj, LinearEquiv.charpoly_conj]

/-- Equivalent representations have the same dimension. -/
theorem Equiv.finrank_eq (e : ρ.Equiv σ) : Module.finrank k V' = Module.finrank k V :=
  e.toLinearEquiv.finrank_eq.symm

end Equiv

section Character

variable {k G : Type*} [Field k] [Monoid G]

/-- The representation of `G` on a `k`-module `M` in which `g` acts as multiplication by the
scalar `χ g`, for a character `χ : G →* kˣ`. On `M = k` this is the one-dimensional
representation with character `χ`; applied to `ρ.detCharacter` it is the determinant line of
`ρ`. -/
noncomputable def ofCharacter (χ : G →* kˣ) (M : Type*) [AddCommGroup M] [Module k M] :
    Representation k G M where
  toFun g := (χ g : k) • LinearMap.id
  map_one' := by
    ext
    simp
  map_mul' g h := by
    ext
    simp [mul_smul, smul_comm (χ g : k)]

@[simp]
theorem ofCharacter_apply (χ : G →* kˣ) (M : Type*) [AddCommGroup M] [Module k M] (g : G)
    (v : M) : ofCharacter χ M g v = (χ g : k) • v :=
  rfl

end Character

section DirectSum

variable {k G ι : Type*} [Field k] [Monoid G] {V : ι → Type*} [∀ i, AddCommGroup (V i)]
  [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i))

open DirectSum

variable [DecidableEq ι]

/-- The summand `V i` of a direct sum `⨁ i, V i` of representations, as a subrepresentation of
`Representation.directSum ρ`. -/
noncomputable def directSumSummand (i : ι) : Subrepresentation (directSum ρ) where
  toSubmodule := LinearMap.range (lof k ι V i)
  apply_mem_toSubmodule g := by
    rintro _ ⟨v, rfl⟩
    exact ⟨ρ i g v, by simp⟩

/-- The summands of a direct sum of representations form an internal direct sum
decomposition. -/
theorem isInternal_directSumSummand :
    IsInternal fun i ↦ (directSumSummand ρ i).toSubmodule := by
  let e (i : ι) : V i ≃ₗ[k] (directSumSummand ρ i).toSubmodule :=
    LinearEquiv.ofInjective (lof k ι V i) (of_injective (β := V) i)
  let Φ : (⨁ i, V i) →ₗ[k] ⨁ i, (directSumSummand ρ i).toSubmodule :=
    lmap fun i ↦ (e i).toLinearMap
  let Ψ : (⨁ i, (directSumSummand ρ i).toSubmodule) →ₗ[k] ⨁ i, V i :=
    lmap fun i ↦ (e i).symm.toLinearMap
  have hΦΨ : Φ ∘ₗ Ψ = LinearMap.id := by
    refine linearMap_ext k fun i ↦ LinearMap.ext fun x ↦ ?_
    simp [Φ, Ψ]
  have hcΦ : coeLinearMap (fun i ↦ (directSumSummand ρ i).toSubmodule) ∘ₗ Φ = LinearMap.id := by
    refine linearMap_ext k fun i ↦ LinearMap.ext fun x ↦ ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, lmap_lof, Φ, LinearMap.id_comp]
    exact coeLinearMap_of _ i _
  have hΦ : Function.Surjective Φ := fun x ↦ ⟨Ψ x, LinearMap.congr_fun hΦΨ x⟩
  refine ⟨fun x y hxy ↦ ?_, fun x ↦ ⟨Φ x, LinearMap.congr_fun hcΦ x⟩⟩
  obtain ⟨x, rfl⟩ := hΦ x
  obtain ⟨y, rfl⟩ := hΦ y
  have h := LinearMap.congr_fun hcΦ x
  have h' := LinearMap.congr_fun hcΦ y
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_apply] at h h'
  rw [h.symm.trans (hxy.trans h')]

/-- The summand `V i` of a direct sum of representations is equivalent to `ρ i`. -/
noncomputable def directSumSummandEquiv (i : ι) :
    (ρ i).Equiv (directSumSummand ρ i).toRepresentation :=
  Equiv.mk (LinearEquiv.ofInjective (lof k ι V i) (of_injective (β := V) i)) fun g ↦
    LinearMap.ext fun v ↦ Subtype.ext (by
      change lof k ι V i (ρ i g v) = directSum ρ g (lof k ι V i v)
      simp)

omit [DecidableEq ι] in
/-- The characteristic polynomial of `g` acting on a finite direct sum of finite-dimensional
representations is the product of the characteristic polynomials of `g` on the summands. -/
theorem charpoly_directSum [Fintype ι] [LinearOrder ι] [∀ i, FiniteDimensional k (V i)] (g : G) :
    (directSum ρ g).charpoly = ∏ i, (ρ i g).charpoly := by
  rw [LinearMap.charpoly_eq_prod_charpoly_restrict (isInternal_directSumSummand ρ)
    fun i ↦ (directSumSummand ρ i).apply_mem_toSubmodule g]
  refine Finset.prod_congr rfl fun i _ ↦ (LinearMap.charpoly_eq_of_comp_eq
    (directSumSummandEquiv ρ i).toLinearEquiv ?_).symm
  exact (directSumSummandEquiv ρ i).isIntertwining' g

end DirectSum

section Dual

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V)

/-- If `α` is an eigenvalue of `ρ g`, then `α⁻¹` is an eigenvalue of `ρ g⁻¹`. -/
theorem hasEigenvalue_inv {g : G} {α : k} (h : Module.End.HasEigenvalue (ρ g) α) :
    Module.End.HasEigenvalue (ρ g⁻¹) α⁻¹ := by
  obtain ⟨v, hv⟩ := h.exists_hasEigenvector
  have hgv : ρ g v = α • v := hv.apply_eq_smul
  have hα : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hgv
    have : v = ρ g⁻¹ (ρ g v) := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    exact hv.2 (by rw [this, hgv, map_zero])
  refine Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩
  rw [Module.End.mem_eigenspace_iff]
  calc ρ g⁻¹ v = α⁻¹ • ρ g⁻¹ (α • v) := by rw [map_smul, smul_smul, inv_mul_cancel₀ hα, one_smul]
    _ = α⁻¹ • v := by
      rw [← hgv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

/-- The eigenvalues of `g` on the dual representation are those of `g⁻¹` on `V`
(`lemma-filtrations-spectra`). -/
theorem hasEigenvalue_dual_iff [FiniteDimensional k V] {g : G} {α : k} :
    Module.End.HasEigenvalue (ρ.dual g) α ↔ Module.End.HasEigenvalue (ρ g⁻¹) α := by
  have h : ρ.dual g = (ρ g⁻¹).dualMap := by
    ext f v
    simp [dual_apply, Module.Dual.transpose_apply]
  rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Module.End.hasEigenvalue_iff_isRoot_charpoly,
    h, LinearMap.charpoly_dualMap]

variable {ρ} {V' : Type*} [AddCommGroup V'] [Module k V'] {σ : Representation k G V'}

/-- Equivalent representations have equivalent contragredients. -/
noncomputable def Equiv.dualCongr (e : ρ.Equiv σ) : ρ.dual.Equiv σ.dual :=
  .mk e.toLinearEquiv.symm.dualMap fun w ↦ by
    refine LinearMap.ext fun f ↦ LinearMap.ext fun x ↦ ?_
    simp only [LinearEquiv.coe_coe, LinearEquiv.dualMap_apply, dual_apply,
      Module.Dual.transpose_apply, LinearMap.comp_apply]
    congr 1
    exact (e.symm.apply_apply w⁻¹ x).symm

end Dual

end Representation

namespace Matrix.GeneralLinearGroup

variable (n : Type*) [Fintype n] [DecidableEq n] (k : Type*) [Field k]

/-- The defining representation of `GL n k` on `n → k`, by matrix-vector multiplication. -/
noncomputable def toRepresentation : Representation k (GL n k) (n → k) where
  toFun g := Matrix.toLinAlgEquiv' (g : Matrix n n k)
  map_one' := by simp
  map_mul' x y := by simp

variable {n k}

@[simp]
theorem toRepresentation_apply (g : GL n k) (v : n → k) :
    toRepresentation n k g v = (g : Matrix n n k) *ᵥ v :=
  rfl

end Matrix.GeneralLinearGroup
