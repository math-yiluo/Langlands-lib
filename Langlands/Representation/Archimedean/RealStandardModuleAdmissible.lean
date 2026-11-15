import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.LinearAlgebra.TriangularUnitary

/-!
# Admissibility of real standard modules

Every `g ∈ GL_n(ℝ)` factors as `g = diag(a) · u · k` with `a` invertible diagonal entries, `u`
upper unipotent and `k ∈ O(n)` (Iwasawa decomposition). A function of the principal series is
therefore determined by its restriction to `O(n)`, and a `K`-intertwiner `T` from a matrix
representation `τ` of `O(n)` into the `O(n)`-finite functions of a subspace of a principal
series is determined by the functional `x ↦ (T x)(1)`. So the space of such intertwiners has
dimension at most the degree of `τ`, and the `(𝔤𝔩_n(ℝ), O(n))`-module of every real standard
module is admissible.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

/-! ## The Iwasawa decomposition of `GL_n(ℝ)` -/

/-- Every `g ∈ GL_n(ℝ)` is `diag(a) · u · k` with `a : Fin n → ℝˣ`, `u` upper unipotent and
`k ∈ O(n)`. -/
theorem exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact {n : ℕ}
    (g : Langlands.GeneralLinear n ℝ) :
    ∃ (a : Fin n → ℝˣ) (u : upperUnipotent n ℝ) (k : Langlands.GeneralLinear n ℝ),
      k ∈ unitaryCompact ℝ n ∧
        g = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
          (u : Langlands.GeneralLinear n ℝ) * k := by
  obtain ⟨b, w, hb, hbu, hw, hg⟩ :=
    Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary
      (g : Matrix (Fin n) (Fin n) ℝ) g.isUnit
  have hdet : b.det = ∏ i, b i i := Matrix.det_of_isUpperTriangular hb
  have hdiag : ∀ i, b i i ≠ 0 := by
    have h0 : b.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det b).mp hbu).ne_zero
    rw [hdet] at h0
    exact fun i => Finset.prod_ne_zero_iff.mp h0 i (Finset.mem_univ i)
  let a : Fin n → ℝˣ := fun i => Units.mk0 (b i i) (hdiag i)
  let B : Langlands.GeneralLinear n ℝ := hbu.unit
  let D : Langlands.GeneralLinear n ℝ := Iwasawa.diagonalUnits a
  have hDinv : ((D⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      Matrix.diagonal fun i => (b i i)⁻¹ := by
    rfl
  have hu : D⁻¹ * B ∈ upperUnipotent n ℝ := by
    have hval : ((D⁻¹ * B : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
        Matrix.diagonal (fun i => (b i i)⁻¹) * b := by
      rw [Units.val_mul, hDinv]
      rfl
    refine ⟨?_, fun i => ?_⟩
    · change ((D⁻¹ * B : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ).BlockTriangular id
      rw [hval]
      exact (Matrix.blockTriangular_diagonal _).mul hb
    · change ((D⁻¹ * B : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i i = 1
      rw [hval, Matrix.diagonal_mul]
      exact inv_mul_cancel₀ (hdiag i)
  let k : Langlands.GeneralLinear n ℝ := Unitary.toUnits ⟨w, hw⟩
  refine ⟨a, ⟨D⁻¹ * B, hu⟩, k, hw, ?_⟩
  apply Units.ext
  change (g : Matrix (Fin n) (Fin n) ℝ) = ((D * (D⁻¹ * B) * k : Langlands.GeneralLinear n ℝ) :
    Matrix (Fin n) (Fin n) ℝ)
  rw [mul_inv_cancel_left]
  rw [hg]
  rfl

/-! ## Principal series functions are determined on `O(n)` -/

/-- A function of the principal series of `GL_n(ℝ)` is determined by its values on `O(n)`. -/
theorem eq_of_eqOn_unitaryCompact_of_mem_principalSeries {n : ℕ} {χ : ℕ → ℝˣ → ℂ}
    {f₁ f₂ : Langlands.GeneralLinear n ℝ → ℂ} (h₁ : f₁ ∈ principalSeries ℝ n χ)
    (h₂ : f₂ ∈ principalSeries ℝ n χ)
    (h : ∀ k ∈ unitaryCompact ℝ n, f₁ k = f₂ k) : f₁ = f₂ := by
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  rw [h₁.2 a u k, h₂.2 a u k, h k hk]

/-- A function of the principal series of `GL_n(ℝ)` vanishing on `O(n)` vanishes. -/
theorem eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact {n : ℕ} {χ : ℕ → ℝˣ → ℂ}
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ principalSeries ℝ n χ)
    (h : ∀ k ∈ unitaryCompact ℝ n, f k = 0) : f = 0 :=
  eq_of_eqOn_unitaryCompact_of_mem_principalSeries hf (principalSeries ℝ n χ).zero_mem h

/-! ## Intertwiners from matrix representations of `O(n)` -/

section KFinite

variable {n : ℕ} {χ : ℕ → ℝˣ → ℂ} (V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
  (hVK : ∀ k ∈ unitaryCompact ℝ n, ∀ f ∈ V,
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) k f ∈ V)

/-- The value at the identity of the image of a `K`-intertwiner into the `K`-finite functions
of `V`: the linear functional `x ↦ (T x)(1)`. -/
def gkIntertwinerValueAtOne (d : ℕ) (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ) :
    gkIntertwiners (kFiniteRep V hVK) d τ →ₗ[ℂ] ((Fin d → ℂ) →ₗ[ℂ] ℂ) where
  toFun T :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear n ℝ => ℂ) 1).comp
      ((kFiniteFunctions V (unitaryCompact ℝ n)).subtype.comp (T : (Fin d → ℂ) →ₗ[ℂ] _))
  map_add' S T := by
    ext x
    rfl
  map_smul' c T := by
    ext x
    rfl

theorem gkIntertwinerValueAtOne_apply (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)
    (T : gkIntertwiners (kFiniteRep V hVK) d τ) (x : Fin d → ℂ) :
    gkIntertwinerValueAtOne V hVK d τ T x =
      ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℝ n)) x :
        Langlands.GeneralLinear n ℝ → ℂ) 1 :=
  rfl

open Matrix in
/-- The value of `T x` at `k ∈ O(n)` is the value at the identity of `T (τ(k) x)`. -/
theorem gkIntertwiner_apply_unitary (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ)
    (T : gkIntertwiners (kFiniteRep V hVK) d τ) (x : Fin d → ℂ)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℝ n)) x :
        Langlands.GeneralLinear n ℝ → ℂ) (Unitary.toUnits k) =
      gkIntertwinerValueAtOne V hVK d τ T (τ k *ᵥ x) := by
  rw [gkIntertwinerValueAtOne_apply, T.2 k x, kFiniteRep_apply_coe]
  change _ = ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℝ n)) x :
    Langlands.GeneralLinear n ℝ → ℂ) (1 * Unitary.toUnits k)
  rw [one_mul]

variable {V}

include hVK in
/-- An intertwiner into the `K`-finite functions of a subspace of a principal series is
determined by its values at the identity. -/
theorem gkIntertwinerValueAtOne_injective (hVχ : V ≤ principalSeries ℝ n χ) (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ) :
    Function.Injective (gkIntertwinerValueAtOne V hVK d τ) := by
  intro S T hST
  apply Subtype.ext
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (hVχ (((S : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℝ n)) x).2.1))
    (hVχ (((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact ℝ n)) x).2.1)) ?_
  intro k hk
  have hk' : (Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) ℝ), hk⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) : Langlands.GeneralLinear n ℝ) = k :=
    Units.ext rfl
  rw [← hk', gkIntertwiner_apply_unitary, gkIntertwiner_apply_unitary, hST]

include hVK in
/-- The `K`-intertwiners from a matrix representation of degree `d` of `O(n)` into the
`K`-finite functions of a subspace of a principal series form a space of dimension at most
`d`. -/
theorem finrank_gkIntertwiners_kFiniteRep_le (hVχ : V ≤ principalSeries ℝ n χ) (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ) :
    Module.finrank ℂ (gkIntertwiners (kFiniteRep V hVK) d τ) ≤ d := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (gkIntertwinerValueAtOne_injective hVK hVχ d τ)
  simpa [Module.finrank_linearMap, Module.finrank_fin_fun] using h

include hVK in
/-- The `K`-finite functions of a right-translation-stable subspace of a principal series of
`GL_n(ℝ)` form an admissible representation of `O(n)`. -/
theorem isAdmissibleGKModule_kFiniteRep (hVχ : V ≤ principalSeries ℝ n χ) :
    IsAdmissibleGKModule (kFiniteRep V hVK) := by
  intro d τ _
  exact Module.Finite.of_injective _ (gkIntertwinerValueAtOne_injective hVK hVχ d τ)

end KFinite

/-! ## Real standard modules -/

/-- The `(𝔤𝔩_n(ℝ), O(n))`-module of the `O(n)`-finite functions of every real standard module
is admissible: every irreducible continuous matrix representation of `O(n)` (indeed every
matrix representation) occurs in it with finite multiplicity. -/
def RealStandardAdmissibleStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), IsAdmissibleGKModule (realStandardRep n ds)

/-- The `O(n)`-intertwiners from a matrix representation of degree `d` into the
`O(n)`-finite functions of a real standard module form a space of dimension at most `d`. -/
theorem finrank_gkIntertwiners_realStandardRep_le (n : ℕ) (ds : List RealBlock) (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) ℝ →* Matrix (Fin d) (Fin d) ℂ) :
    Module.finrank ℂ (gkIntertwiners (realStandardRep n ds) d τ) ≤ d :=
  finrank_gkIntertwiners_kFiniteRep_le _ (realStandardModule_le_principalSeries n ds) d τ

/-- Real standard modules are admissible. -/
theorem realStandardAdmissible : RealStandardAdmissibleStatement := fun n ds =>
  isAdmissibleGKModule_kFiniteRep _ (realStandardModule_le_principalSeries n ds)

end Langlands.Archimedean
