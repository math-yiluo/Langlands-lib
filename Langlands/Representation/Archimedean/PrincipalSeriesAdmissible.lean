import Langlands.Representation.Archimedean.PrincipalSeriesGKModule
import Langlands.LinearAlgebra.TriangularUnitary

/-!
# Admissibility of principal series over `ℝ` and `ℂ`

Let `F` be `ℝ` or `ℂ` (any `RCLike` field). Every `g ∈ GL_n(F)` factors as
`g = diag(a) · u · k` with `a` invertible diagonal entries, `u` upper unipotent and `k` in the
unitary group `K` (`O(n)` over `ℝ`, `U(n)` over `ℂ`): the Iwasawa decomposition. A function of
the principal series `principalSeries F n χ` is therefore determined by its restriction to `K`,
and a `K`-intertwiner `T` from a matrix representation `τ` of `K` into the `K`-finite functions
of a right-translation-stable subspace of a principal series is determined by the functional
`x ↦ (T x)(1)`. So the space of such intertwiners has dimension at most the degree of `τ`, and
the `K`-finite functions of the principal series form an admissible representation of `K`.

The results restate, for an arbitrary `RCLike` field, the real results of
`Langlands.Representation.Archimedean.RealStandardModuleAdmissible`, with the same proofs. They
live in the namespace `Langlands.Archimedean.PrincipalSeries` so that their names do not clash
with the real ones.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean.PrincipalSeries

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

universe uF

variable {F : Type uF} [RCLike F]

/-! ## The Iwasawa decomposition of `GL_n(F)` -/

/-- Every `g ∈ GL_n(F)` is `diag(a) · u · k` with `a : Fin n → Fˣ`, `u` upper unipotent and
`k` in the unitary group `unitaryCompact F n`. -/
theorem exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact {n : ℕ}
    (g : Langlands.GeneralLinear n F) :
    ∃ (a : Fin n → Fˣ) (u : upperUnipotent n F) (k : Langlands.GeneralLinear n F),
      k ∈ unitaryCompact F n ∧
        g = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n F) *
          (u : Langlands.GeneralLinear n F) * k := by
  obtain ⟨b, w, hb, hbu, hw, hg⟩ :=
    Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary
      (g : Matrix (Fin n) (Fin n) F) g.isUnit
  have hdet : b.det = ∏ i, b i i := Matrix.det_of_isUpperTriangular hb
  have hdiag : ∀ i, b i i ≠ 0 := by
    have h0 : b.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det b).mp hbu).ne_zero
    rw [hdet] at h0
    exact fun i => Finset.prod_ne_zero_iff.mp h0 i (Finset.mem_univ i)
  let a : Fin n → Fˣ := fun i => Units.mk0 (b i i) (hdiag i)
  let B : Langlands.GeneralLinear n F := hbu.unit
  let D : Langlands.GeneralLinear n F := Iwasawa.diagonalUnits a
  have hDinv : ((D⁻¹ : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (b i i)⁻¹ := by
    rfl
  have hu : D⁻¹ * B ∈ upperUnipotent n F := by
    have hval : ((D⁻¹ * B : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) =
        Matrix.diagonal (fun i => (b i i)⁻¹) * b := by
      rw [Units.val_mul, hDinv]
      rfl
    refine ⟨?_, fun i => ?_⟩
    · change ((D⁻¹ * B : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F).BlockTriangular id
      rw [hval]
      exact (Matrix.blockTriangular_diagonal _).mul hb
    · change ((D⁻¹ * B : Langlands.GeneralLinear n F) : Matrix (Fin n) (Fin n) F) i i = 1
      rw [hval, Matrix.diagonal_mul]
      exact inv_mul_cancel₀ (hdiag i)
  let k : Langlands.GeneralLinear n F := Unitary.toUnits ⟨w, hw⟩
  refine ⟨a, ⟨D⁻¹ * B, hu⟩, k, hw, ?_⟩
  apply Units.ext
  change (g : Matrix (Fin n) (Fin n) F) = ((D * (D⁻¹ * B) * k : Langlands.GeneralLinear n F) :
    Matrix (Fin n) (Fin n) F)
  rw [mul_inv_cancel_left]
  rw [hg]
  rfl

/-! ## Principal series functions are determined on `K` -/

/-- A function of the principal series of `GL_n(F)` is determined by its values on the unitary
group `unitaryCompact F n`. -/
theorem eq_of_eqOn_unitaryCompact_of_mem_principalSeries {n : ℕ} {χ : ℕ → Fˣ → ℂ}
    {f₁ f₂ : Langlands.GeneralLinear n F → ℂ} (h₁ : f₁ ∈ principalSeries F n χ)
    (h₂ : f₂ ∈ principalSeries F n χ)
    (h : ∀ k ∈ unitaryCompact F n, f₁ k = f₂ k) : f₁ = f₂ := by
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  rw [h₁.2 a u k, h₂.2 a u k, h k hk]

/-- A function of the principal series of `GL_n(F)` vanishing on the unitary group vanishes. -/
theorem eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact {n : ℕ} {χ : ℕ → Fˣ → ℂ}
    {f : Langlands.GeneralLinear n F → ℂ} (hf : f ∈ principalSeries F n χ)
    (h : ∀ k ∈ unitaryCompact F n, f k = 0) : f = 0 :=
  eq_of_eqOn_unitaryCompact_of_mem_principalSeries hf (principalSeries F n χ).zero_mem h

/-! ## Intertwiners from matrix representations of `K` -/

section KFinite

variable {n : ℕ} {χ : ℕ → Fˣ → ℂ} (V : Submodule ℂ (Langlands.GeneralLinear n F → ℂ))
  (hVK : ∀ k ∈ unitaryCompact F n, ∀ f ∈ V,
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n F) k f ∈ V)

/-- The value at the identity of the image of a `K`-intertwiner into the `K`-finite functions
of `V`: the linear functional `x ↦ (T x)(1)`. -/
def gkIntertwinerValueAtOne (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) F →* Matrix (Fin d) (Fin d) ℂ) :
    gkIntertwiners (kFiniteRep V hVK) d τ →ₗ[ℂ] ((Fin d → ℂ) →ₗ[ℂ] ℂ) where
  toFun T :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Langlands.GeneralLinear n F => ℂ) 1).comp
      ((kFiniteFunctions V (unitaryCompact F n)).subtype.comp (T : (Fin d → ℂ) →ₗ[ℂ] _))
  map_add' S T := by
    ext x
    rfl
  map_smul' c T := by
    ext x
    rfl

theorem gkIntertwinerValueAtOne_apply (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) F →* Matrix (Fin d) (Fin d) ℂ)
    (T : gkIntertwiners (kFiniteRep V hVK) d τ) (x : Fin d → ℂ) :
    gkIntertwinerValueAtOne V hVK d τ T x =
      ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact F n)) x :
        Langlands.GeneralLinear n F → ℂ) 1 :=
  rfl

open Matrix in
/-- The value of `T x` at `k ∈ K` is the value at the identity of `T (τ(k) x)`. -/
theorem gkIntertwiner_apply_unitary (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) F →* Matrix (Fin d) (Fin d) ℂ)
    (T : gkIntertwiners (kFiniteRep V hVK) d τ) (x : Fin d → ℂ)
    (k : Matrix.unitaryGroup (Fin n) F) :
    ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact F n)) x :
        Langlands.GeneralLinear n F → ℂ) (Unitary.toUnits k) =
      gkIntertwinerValueAtOne V hVK d τ T (τ k *ᵥ x) := by
  rw [gkIntertwinerValueAtOne_apply, T.2 k x, kFiniteRep_apply_coe]
  change _ = ((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact F n)) x :
    Langlands.GeneralLinear n F → ℂ) (1 * Unitary.toUnits k)
  rw [one_mul]

variable {V}

include hVK in
/-- An intertwiner into the `K`-finite functions of a subspace of a principal series is
determined by its values at the identity. -/
theorem gkIntertwinerValueAtOne_injective (hVχ : V ≤ principalSeries F n χ) (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) F →* Matrix (Fin d) (Fin d) ℂ) :
    Function.Injective (gkIntertwinerValueAtOne V hVK d τ) := by
  intro S T hST
  apply Subtype.ext
  refine LinearMap.ext fun x => ?_
  apply Subtype.ext
  refine eq_of_eqOn_unitaryCompact_of_mem_principalSeries
    (hVχ (((S : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact F n)) x).2.1))
    (hVχ (((T : (Fin d → ℂ) →ₗ[ℂ] kFiniteFunctions V (unitaryCompact F n)) x).2.1)) ?_
  intro k hk
  have hk' : (Unitary.toUnits (⟨(k : Matrix (Fin n) (Fin n) F), hk⟩ :
      Matrix.unitaryGroup (Fin n) F) : Langlands.GeneralLinear n F) = k :=
    Units.ext rfl
  rw [← hk', gkIntertwiner_apply_unitary, gkIntertwiner_apply_unitary, hST]

include hVK in
/-- The `K`-intertwiners from a matrix representation of degree `d` of `K` into the
`K`-finite functions of a subspace of a principal series form a space of dimension at most
`d`. -/
theorem finrank_gkIntertwiners_kFiniteRep_le (hVχ : V ≤ principalSeries F n χ) (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) F →* Matrix (Fin d) (Fin d) ℂ) :
    Module.finrank ℂ (gkIntertwiners (kFiniteRep V hVK) d τ) ≤ d := by
  have h := LinearMap.finrank_le_finrank_of_injective
    (gkIntertwinerValueAtOne_injective hVK hVχ d τ)
  simpa [Module.finrank_linearMap, Module.finrank_fin_fun] using h

include hVK in
/-- The `K`-finite functions of a right-translation-stable subspace of a principal series of
`GL_n(F)` form an admissible representation of `K`. -/
theorem isAdmissibleGKModule_kFiniteRep (hVχ : V ≤ principalSeries F n χ) :
    IsAdmissibleGKModule (kFiniteRep V hVK) := by
  intro d τ _
  exact Module.Finite.of_injective _ (gkIntertwinerValueAtOne_injective hVK hVχ d τ)

end KFinite

/-! ## The principal series -/

variable (F) in
/-- The `K`-intertwiners from a matrix representation of degree `d` of `K` into the
`K`-finite functions of the principal series `principalSeries F n χ` form a space of dimension
at most `d`. -/
theorem finrank_gkIntertwiners_principalSeriesRep_le (n : ℕ) (χ : ℕ → Fˣ → ℂ) (d : ℕ)
    (τ : Matrix.unitaryGroup (Fin n) F →* Matrix (Fin d) (Fin d) ℂ) :
    Module.finrank ℂ (gkIntertwiners (principalSeriesRep F n χ) d τ) ≤ d :=
  finrank_gkIntertwiners_kFiniteRep_le _ le_rfl d τ

variable (F) in
/-- The `K`-finite functions of the principal series `principalSeries F n χ` form an
admissible representation of `K`. -/
theorem isAdmissibleGKModule_principalSeriesRep (n : ℕ) (χ : ℕ → Fˣ → ℂ) :
    IsAdmissibleGKModule (principalSeriesRep F n χ) :=
  isAdmissibleGKModule_kFiniteRep _ le_rfl

end Langlands.Archimedean.PrincipalSeries
