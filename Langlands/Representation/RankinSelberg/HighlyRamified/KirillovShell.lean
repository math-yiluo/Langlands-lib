import Langlands.Representation.RankinSelberg.HighlyRamified.AdjacentStep
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.Representation.RankinSelberg.HighlyRamified.DualShellIntegral
import Langlands.Representation.RankinSelberg.TwistInvariance
import Langlands.Representation.RankinSelberg.RankOneTestReduction
import Langlands.Representation.RankinSelberg.Measures
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.HarmonicAnalysis.AlgebraicIntegral
import Langlands.HarmonicAnalysis.AlgebraicIntegrand
import Langlands.Group.GL.MirabolicProjection

/-!
# The Kirillov shell vector

Let `σ` be a generic representation of `GL_(m+2)` with central character `ω_σ` and a nonzero
functional `ℓ'` for the inverse standard character of `ψ`, where `ψ` has conductor exponent
`0`. For a continuous character `χ`, a unit `ϖ` and `c : ℕ`, the model of `(σ, ℓ')` contains
a function `f'` with

* `f'(diag(B,1)) ≠ 0` only if `u B ϖ^c ∈ GL_(m+1)(O)` for some upper unipotent `u`;
* `f'(diag(k ϖ^(-c), 1)) = χ(det k)⁻¹` for `k ∈ GL_(m+1)(O)`;
* `f'(g · diag(I, d)) = ω_σ(d) χ(d)^(m+1) f'(g)` for integral units `d`.

The adjacent-rank step of this project uses this vector where Jacquet and Shalika (1985),
§4.4, use the vector `W'` of (4.4.16)–(4.4.17). It is an internal construction, not their
vector: their `W'` lies in the model of `σ ⊗ χ`, and its Weyl translate is supported on a
level-`f` shell with a prescribed constant value (see `KirillovShell.md`, Provenance). The
vector is a Kirillov lift of the function `u · diag(k, 1) ↦ ψ⁻¹(u) χ(det k)⁻¹` on
`N · diag(GL_(m+1)(O), 1)`, translated by `diag(ϖ^c, 1)` and averaged over the scalars
`diag(d I, 1)`, `d ∈ O^×`, with weight `χ(d)^(m+1)`. The last theorem,
`kirillovShellInput`, proves the input `KirillovShellInput` of the adjacent-rank step.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open Langlands.GeneralLinear.Iwasawa

universe uF uV uW

/-! ### The integral shell function -/

section Shell

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

/-- `g = u · diag(k, 1)` with `u` upper unipotent and `k ∈ GL_(m+1)(O)`. -/
def IsIntegralShell (g : GeneralLinear (m + 1 + 1) F) : Prop :=
  ∃ (u : upperUnipotent (m + 1 + 1) F) (k : GeneralLinear (m + 1) F),
    IsIntegralMatrix k ∧ g = u.val * rankInclusion 1 k

theorem isIntegralMatrix_iff_mem_integralSubgroup (k : GeneralLinear (m + 1) F) :
    IsIntegralMatrix k ↔ k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer m :=
  (Conductor.mem_integralSubgroup _ _ _).symm

omit [ValuativeRel F] in
theorem determinant_rankInclusion_one (k : GeneralLinear (m + 1) F) :
    determinant (rankInclusion 1 k) = determinant k :=
  Units.ext (det_rankInclusion 1 k)

omit [ValuativeRel F] in
theorem determinant_upperUnipotent_val {n : ℕ} (u : upperUnipotent n F) :
    determinant u.val = 1 :=
  Units.ext (unipotent_det u)

variable {θ : upperUnipotent (m + 1 + 1) F →* ℂˣ}
  (hθ : IsIntegrallyTrivial (ValuativeRel.valuation F) θ) (χ : Fˣ →* ℂˣ)

include hθ in
/-- The value `θ(u) χ(det k)⁻¹` does not depend on the decomposition `u · diag(k, 1)`:
two decompositions differ by `diag(n, 1)` with `n` integral upper unipotent. -/
theorem integralShell_value_unique {u₁ u₂ : upperUnipotent (m + 1 + 1) F}
    {k₁ k₂ : GeneralLinear (m + 1) F} (hk₁ : IsIntegralMatrix k₁) (hk₂ : IsIntegralMatrix k₂)
    (h : u₁.val * rankInclusion 1 k₁ = u₂.val * rankInclusion 1 k₂) :
    (θ u₁ : ℂ) * ((χ (determinant k₁) : ℂ))⁻¹ = (θ u₂ : ℂ) * ((χ (determinant k₂) : ℂ))⁻¹ := by
  have hu : (u₂⁻¹ * u₁).val = rankInclusion 1 (k₂ * k₁⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, eq_mul_inv_iff_mul_eq, mul_assoc,
      h, inv_mul_cancel_left]
  have hmem : k₂ * k₁⁻¹ ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer m :=
    Subgroup.mul_mem _ ((isIntegralMatrix_iff_mem_integralSubgroup k₂).1 hk₂)
      (Subgroup.inv_mem _ ((isIntegralMatrix_iff_mem_integralSubgroup k₁).1 hk₁))
  have hθ1 : θ (u₂⁻¹ * u₁) = 1 := by
    apply hθ
    rw [hu]
    exact rankInclusion_mem_integralSubgroup hmem
  have hdet : determinant (k₂ * k₁⁻¹) = 1 := by
    rw [← determinant_rankInclusion_one, ← hu, determinant_upperUnipotent_val]
  have hθe : θ u₁ = θ u₂ := by
    rw [← mul_inv_cancel_left u₂ u₁, map_mul, hθ1, mul_one]
  have hde : determinant k₂ = determinant k₁ :=
    calc determinant k₂ = determinant (k₂ * k₁⁻¹ * k₁) := by rw [inv_mul_cancel_right]
      _ = determinant k₁ := by rw [map_mul, hdet, one_mul]
  rw [hθe, hde]

open Classical in
/-- The function `u · diag(k, 1) ↦ θ(u) χ(det k)⁻¹` on `N · diag(GL_(m+1)(O), 1)`, and `0`
off this set. -/
def integralShellValue (θ : upperUnipotent (m + 1 + 1) F →* ℂˣ) (χ : Fˣ →* ℂˣ)
    (g : GeneralLinear (m + 1 + 1) F) : ℂ :=
  if h : IsIntegralShell g then
    (θ h.choose : ℂ) * ((χ (determinant h.choose_spec.choose) : ℂ))⁻¹
  else 0

include hθ in
theorem integralShellValue_mul (u : upperUnipotent (m + 1 + 1) F) (k : GeneralLinear (m + 1) F)
    (hk : IsIntegralMatrix k) :
    integralShellValue θ χ (u.val * rankInclusion 1 k) =
      (θ u : ℂ) * ((χ (determinant k) : ℂ))⁻¹ := by
  have h : IsIntegralShell (u.val * rankInclusion 1 k) := ⟨u, k, hk, rfl⟩
  rw [integralShellValue, dite_eq_left h]
  exact integralShell_value_unique hθ χ h.choose_spec.choose_spec.1 hk
    h.choose_spec.choose_spec.2.symm

theorem integralShellValue_of_not {g : GeneralLinear (m + 1 + 1) F} (h : ¬ IsIntegralShell g) :
    integralShellValue θ χ g = 0 := by
  rw [integralShellValue, dite_eq_right h]

include hθ in
theorem integralShellValue_rankInclusion (k : GeneralLinear (m + 1) F) (hk : IsIntegralMatrix k) :
    integralShellValue θ χ (rankInclusion 1 k) = ((χ (determinant k) : ℂ))⁻¹ := by
  have h := integralShellValue_mul hθ χ 1 k hk
  rwa [Subgroup.coe_one, one_mul, map_one, Units.val_one, one_mul] at h

include hθ in
theorem integralShellValue_unipotent_mul (u : upperUnipotent (m + 1 + 1) F)
    (g : GeneralLinear (m + 1 + 1) F) :
    integralShellValue θ χ (u.val * g) = (θ u : ℂ) * integralShellValue θ χ g := by
  by_cases hg : IsIntegralShell g
  · obtain ⟨u', k, hk, rfl⟩ := hg
    have he : u.val * (u'.val * rankInclusion 1 k) = (u * u').val * rankInclusion 1 k := by
      rw [Subgroup.coe_mul, mul_assoc]
    rw [he, integralShellValue_mul hθ χ _ k hk, integralShellValue_mul hθ χ _ k hk, map_mul,
      Units.val_mul, mul_assoc]
  · have hug : ¬ IsIntegralShell (u.val * g) := by
      rintro ⟨u', k, hk, he⟩
      refine hg ⟨u⁻¹ * u', k, hk, ?_⟩
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, ← he, inv_mul_cancel_left]
    rw [integralShellValue_of_not χ hug, integralShellValue_of_not χ hg, mul_zero]

/-- The integral shell function as a `θ`-Whittaker function. -/
def integralShell : (equivariantFunctions (upperUnipotent (m + 1 + 1) F) θ).toSubmodule :=
  ⟨integralShellValue θ χ, fun u g => integralShellValue_unipotent_mul hθ χ u g⟩

include hθ in
/-- Right multiplication by an integral mirabolic `k` with `χ(det k) = 1` preserves the shell
decomposition and its value. Write `k = r · diag(A, 1)` with `r` in the radical; then
`u · diag(k₀, 1) · k = (u r') · diag(k₀ A, 1)` with `r' = diag(k₀,1) r diag(k₀,1)⁻¹`
integral upper unipotent. -/
theorem integralShell_mul_right_aux {k : GeneralLinear (m + 1 + 1) F}
    (hkP : k ∈ mirabolic (m + 1) F)
    (hkO : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer (m + 1))
    (hkχ : χ (determinant k) = 1) (u : upperUnipotent (m + 1 + 1) F)
    (k₀ : GeneralLinear (m + 1) F) (hk₀ : IsIntegralMatrix k₀) :
    ∃ (u' : upperUnipotent (m + 1 + 1) F) (k₁ : GeneralLinear (m + 1) F),
      IsIntegralMatrix k₁ ∧ u.val * rankInclusion 1 k₀ * k = u'.val * rankInclusion 1 k₁ ∧
      (θ u' : ℂ) * ((χ (determinant k₁) : ℂ))⁻¹ = (θ u : ℂ) * ((χ (determinant k₀) : ℂ))⁻¹ := by
  let kM : mirabolic (m + 1) F := ⟨k, hkP⟩
  let A := Mirabolic.projection kM
  have hrad : kM * (Mirabolic.levi A)⁻¹ ∈ Mirabolic.radical (m + 1) F := by
    rw [← Mirabolic.projection_eq_one_iff, map_mul, map_inv, Mirabolic.projection_levi,
      mul_inv_cancel]
  have hrad' : Mirabolic.levi k₀ * (kM * (Mirabolic.levi A)⁻¹) * (Mirabolic.levi k₀)⁻¹ ∈
      Mirabolic.radical (m + 1) F :=
    Mirabolic.radical_normal.conj_mem _ hrad _
  let r := Mirabolic.radicalToUpperUnipotent ⟨_, hrad'⟩
  have hr : r.val = rankInclusion 1 k₀ * (k * (rankInclusion 1 A)⁻¹) *
      (rankInclusion 1 k₀)⁻¹ := rfl
  have hA : IsIntegralMatrix A := by
    obtain ⟨h1, h2⟩ := (Conductor.mem_integralSubgroup _ _ _).1 hkO
    exact ⟨fun i j => h1 i.castSucc j.castSucc, fun i j => h2 i.castSucc j.castSucc⟩
  have hdetA : determinant A = determinant k := by
    have h0 : determinant (k * (rankInclusion 1 A)⁻¹) = 1 :=
      determinant_upperUnipotent_val (Mirabolic.radicalToUpperUnipotent ⟨_, hrad⟩)
    calc determinant A = determinant (rankInclusion 1 A) := (determinant_rankInclusion_one A).symm
      _ = determinant (k * (rankInclusion 1 A)⁻¹) * determinant (rankInclusion 1 A) := by
        rw [h0, one_mul]
      _ = determinant k := by rw [← map_mul, inv_mul_cancel_right]
  have hO := fun x => (isIntegralMatrix_iff_mem_integralSubgroup (F := F) (m := m) x).1
  have hrO : r.val ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer (m + 1) := by
    rw [hr]
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (rankInclusion_mem_integralSubgroup (hO _ hk₀))
      (Subgroup.mul_mem _ hkO (Subgroup.inv_mem _ (rankInclusion_mem_integralSubgroup
        (hO _ hA))))) (Subgroup.inv_mem _ (rankInclusion_mem_integralSubgroup (hO _ hk₀)))
  refine ⟨u * r, k₀ * A, (isIntegralMatrix_iff_mem_integralSubgroup _).2
    (Subgroup.mul_mem _ (hO _ hk₀) (hO _ hA)), ?_, ?_⟩
  · rw [Subgroup.coe_mul, hr, map_mul]
    group
  · rw [map_mul θ, hθ r hrO, mul_one, map_mul determinant, map_mul χ, hdetA, hkχ, mul_one]

include hθ in
/-- The integral shell function is right invariant under integral mirabolic matrices `k`
with `χ(det k) = 1`. -/
theorem integralShellValue_mul_right {k : GeneralLinear (m + 1 + 1) F}
    (hkP : k ∈ mirabolic (m + 1) F)
    (hkO : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer (m + 1))
    (hkχ : χ (determinant k) = 1) (g : GeneralLinear (m + 1 + 1) F) :
    integralShellValue θ χ (g * k) = integralShellValue θ χ g := by
  by_cases hg : IsIntegralShell g
  · obtain ⟨u, k₀, hk₀, rfl⟩ := hg
    obtain ⟨u', k₁, hk₁, he, hv⟩ := integralShell_mul_right_aux hθ χ hkP hkO hkχ u k₀ hk₀
    rw [he, integralShellValue_mul hθ χ _ _ hk₁, integralShellValue_mul hθ χ _ _ hk₀, hv]
  · have hgk : ¬ IsIntegralShell (g * k) := by
      rintro ⟨u, k₀, hk₀, he⟩
      have hkχ' : χ (determinant k⁻¹) = 1 := by rw [map_inv, map_inv, hkχ, inv_one]
      obtain ⟨u', k₁, hk₁, he', -⟩ := integralShell_mul_right_aux hθ χ (inv_mem hkP)
        (inv_mem hkO) hkχ' u k₀ hk₀
      refine hg ⟨u', k₁, hk₁, ?_⟩
      rw [← he', ← he, mul_inv_cancel_right]
    rw [integralShellValue_of_not χ hgk, integralShellValue_of_not χ hg]

/-- From `diag(X, 1) = u · diag(k, 1)` with `k` integral, some upper unipotent `u₁` makes
`u₁ X` integral. -/
theorem exists_isIntegralMatrix_of_isIntegralShell {X : GeneralLinear (m + 1) F}
    (h : IsIntegralShell (rankInclusion 1 X)) :
    ∃ u₁ : upperUnipotent (m + 1) F, IsIntegralMatrix (u₁.val * X) := by
  obtain ⟨u, k, hk, he⟩ := h
  have hu : u.val = rankInclusion 1 (X * k⁻¹) := by
    rw [map_mul, map_inv, he, mul_inv_cancel_right]
  have hmem : X * k⁻¹ ∈ upperUnipotent (m + 1) F := by
    have hp := u.property
    rw [hu] at hp
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have := hp.1 (show id (Fin.castAdd 1 j) < id (Fin.castAdd 1 i) from hij)
      rwa [show (rankInclusion 1 (X * k⁻¹)).val (i.castAdd 1) (j.castAdd 1) = (X * k⁻¹) i j from
        blockSum_apply_left _ _ i j] at this
    · have := hp.2 (i.castAdd 1)
      rwa [show (rankInclusion 1 (X * k⁻¹)) (i.castAdd 1) (i.castAdd 1) = (X * k⁻¹) i i from
        blockSum_apply_left _ _ i i] at this
  refine ⟨(⟨X * k⁻¹, hmem⟩ : upperUnipotent (m + 1) F)⁻¹, ?_⟩
  rw [Subgroup.coe_inv, mul_inv_rev, inv_inv, inv_mul_cancel_right]
  exact hk

end Shell

/-! ### Smearing along a continuous map -/

section Smear

variable {H : Type*} [Group H] [TopologicalSpace H] [MeasurableSpace H] [OpensMeasurableSpace H]
  {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The integrand `x ↦ S(x) ρ(ι x) v` as a finite-image simple function. -/
def mapIntegrand (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (ι : H → G) (hι : Continuous ι)
    (S : H → ℂ) (hS : IsLocallyConstant S) (hSc : HasCompactSupport S) (v : V) :
    SimpleFunc H V :=
  compactlySupportedSimpleFunc (fun x => S x • ρ (ι x) v)
    (hS.comp₂ ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp_continuous hι) (· • ·))
    hSc.smul_right

/-- The smeared vector `∫ S(x) ρ(ι x) v dμ(x)`. -/
def mapSmear (μ : Measure H) (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (ι : H → G)
    (hι : Continuous ι) (S : H → ℂ) (hS : IsLocallyConstant S) (hSc : HasCompactSupport S)
    (v : V) : V :=
  AlgebraicIntegral.integral μ (mapIntegrand ρ hρ ι hι S hS hSc v)

omit [Group H] in
/-- Every linear functional evaluates the smeared vector as a scalar integral. -/
theorem mapSmear_dual (μ : Measure H) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (ι : H → G) (hι : Continuous ι)
    (S : H → ℂ) (hS : IsLocallyConstant S) (hSc : HasCompactSupport S) (v : V)
    (L : V →ₗ[ℂ] ℂ) :
    L (mapSmear μ ρ hρ ι hι S hS hSc v) = ∫ x, S x * L (ρ (ι x) v) ∂μ := by
  have hfin : (mapIntegrand ρ hρ ι hι S hS hSc v).FinMeasSupp μ :=
    compactlySupportedSimpleFunc_finMeasSupp μ _ _ _
  unfold mapSmear
  rw [← AlgebraicIntegral.integral_linearMap _ hfin L,
    AlgebraicIntegral.integral_eq_bochner _ (hfin.map L.map_zero)]
  congr 1
  funext x
  simp [mapIntegrand]

end Smear

/-! ### Scalars and the block `diag(I, d)` -/

section Scalars

variable {F : Type uF} [Field F] [ValuativeRel F] {m : ℕ}

/-- A scalar matrix with an integral unit entry is integral. -/
theorem isIntegralMatrix_scalar {e : Fˣ}
    (he : e ∈ integralUnits (ValuativeRel.valuation F).integer) :
    IsIntegralMatrix (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) e) := by
  rw [mem_integralUnits] at he
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change Matrix.scalar (Fin (m + 1)) (e : F) i j ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact he.1
    · exact Subring.zero_mem _
  · rw [← map_inv]
    change Matrix.scalar (Fin (m + 1)) ((e⁻¹ : Fˣ) : F) i j ∈ _
    rw [Matrix.scalar_apply, Matrix.diagonal_apply]
    split_ifs
    · exact he.2
    · exact Subring.zero_mem _

omit [ValuativeRel F] in
theorem rankInclusion_one_castAdd_castAdd (X : GeneralLinear (m + 1) F) (i j : Fin (m + 1)) :
    rankInclusion 1 X (i.castAdd 1) (j.castAdd 1) = X i j :=
  blockSum_apply_left X 1 i j

omit [ValuativeRel F] in
theorem rankInclusion_one_castAdd_natAdd (X : GeneralLinear (m + 1) F) (i : Fin (m + 1))
    (j : Fin 1) : rankInclusion 1 X (i.castAdd 1) (j.natAdd (m + 1)) = 0 :=
  blockSum_apply_left_right X 1 i j

omit [ValuativeRel F] in
theorem rankInclusion_one_natAdd_castAdd (X : GeneralLinear (m + 1) F) (i : Fin 1)
    (j : Fin (m + 1)) : rankInclusion 1 X (i.natAdd (m + 1)) (j.castAdd 1) = 0 :=
  blockSum_apply_right_left X 1 i j

omit [ValuativeRel F] in
theorem rankInclusion_one_natAdd_natAdd (X : GeneralLinear (m + 1) F) (i j : Fin 1) :
    rankInclusion 1 X (i.natAdd (m + 1)) (j.natAdd (m + 1)) = 1 := by
  rw [show rankInclusion 1 X (i.natAdd (m + 1)) (j.natAdd (m + 1)) =
    (1 : GeneralLinear 1 F) i j from blockSum_apply_right X 1 i j, Subsingleton.elim i j]
  simp

omit [ValuativeRel F] in
/-- `diag(I_(m+1), d) = d · diag(d⁻¹ I_(m+1), 1)` for the `1 × 1` block `c'` with
determinant `d`. -/
theorem lowerBlockPair_eq_scalar_mul (c' : lowerTriangularSubgroup 1 F) :
    lowerBlockPair (1 : GeneralLinear (m + 1) F) 0 c' =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 1)) (determinant c'.val) *
        rankInclusion 1
          (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (determinant c'.val)⁻¹) := by
  have hd : ((determinant c'.val : Fˣ) : F) = c'.val 0 0 := Matrix.det_unique _
  have hd0 : ((determinant c'.val : Fˣ) : F) ≠ 0 := Units.ne_zero _
  apply Units.ext
  ext i j
  rw [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_mul]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [lowerBlockPair_11, rankInclusion_one_castAdd_castAdd,
      Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply,
      Units.val_one, Matrix.one_apply]
    split_ifs
    · rw [Units.val_inv_eq_inv_val, mul_inv_cancel₀ hd0]
    · rw [mul_zero]
  · rw [lowerBlockPair_12, rankInclusion_one_castAdd_natAdd, mul_zero]
  · rw [lowerBlockPair_21, rankInclusion_one_natAdd_castAdd, mul_zero]
    rfl
  · rw [lowerBlockPair_22, rankInclusion_one_natAdd_natAdd, mul_one, hd, Subsingleton.elim i 0,
      Subsingleton.elim j 0]

end Scalars

/-! ### The construction over a p-adic field -/

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance kirillovShellFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance kirillovShellValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance kirillovShellLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance kirillovShellUnitsMeasurable : MeasurableSpace F.Carrierˣ := borel _
local instance kirillovShellUnitsBorel : BorelSpace F.Carrierˣ := ⟨rfl⟩

variable {m : ℕ}

/-- The kernel of `χ ∘ det` on `GL_(n+1)` as an open subgroup. -/
def determinantKernel (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ) (n : ℕ) :
    OpenSubgroup (GeneralLinear (n + 1) F.Carrier) where
  toSubgroup := (χ.comp determinant).ker
  isOpen' := (quasicharacter_isOpen_ker F.canonicalTopologicalData ⟨χ, hχ⟩).preimage
    (F.canonicalTopologicalData.generalLinearDeterminant (n + 1)).continuous

/-- The kernel of `χ` as an open subgroup of `F^×`. -/
def unitKernel (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ) : OpenSubgroup F.Carrierˣ where
  toSubgroup := χ.ker
  isOpen' := quasicharacter_isOpen_ker F.canonicalTopologicalData ⟨χ, hχ⟩

/-- The integral shell function is a mirabolic test function: it is right invariant under
`GL_(m+2)(O) ∩ ker(χ ∘ det)` on the mirabolic subgroup and supported on
`N · diag(GL_(m+1)(O), 1)`. -/
theorem isMirabolicTestFunction_integralShell (ψ' : UnitaryAdditiveCharacter F.Carrier)
    (hψ' : ∀ x ∈ (ValuativeRel.valuation F.Carrier).integer, ψ' x = 1)
    (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ) :
    IsMirabolicTestFunction ψ' (m + 1)
      (integralShell (isIntegrallyTrivial_standardCharacter hψ' (m + 1)) χ) := by
  refine ⟨⟨Conductor.levelOpenSubgroup F.Carrier (m + 1) 0 ⊓ determinantKernel F χ hχ (m + 1),
    fun q k _ hkP hk => ?_⟩,
    ⟨(rankInclusion 1) '' (Conductor.levelOpenSubgroup F.Carrier m 0 :
      Set (GeneralLinear (m + 1) F.Carrier)),
      (Conductor.isCompact_levelOpenSubgroup F.Carrier m 0).image
        (rankInclusionContinuous 1).continuous, fun q _ hq => ?_⟩⟩
  · have hkO : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer
        (m + 1) := by
      rw [← Conductor.levelSubgroup_zero]
      exact hk.1
    exact integralShellValue_mul_right (isIntegrallyTrivial_standardCharacter hψ' (m + 1)) χ
      hkP hkO (MonoidHom.mem_ker.1 hk.2) q
  · by_cases hs : IsIntegralShell q
    · obtain ⟨u, k, hk, rfl⟩ := hs
      exact ⟨u, rankInclusion 1 k, ⟨k, (isIntegralMatrix_iff_mem_level F k).1 hk, rfl⟩, rfl⟩
    · exact absurd (integralShellValue_of_not χ hs) hq

/-- The Kirillov lift of the integral shell function: a vector `v₀` with
`ℓ'(σ(q) v₀) = ψ⁻¹(u) χ(det k)⁻¹` at `q = u · diag(k, 1)` and `0` at other mirabolic `q`. -/
theorem exists_integralShell_vector (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear (m + 1 + 1) F.Carrier) W)
    (hσ : Whittaker.IsGeneric ψ (m + 1) σ) (ℓ' : glInverseFunctionals ψ (m + 1) σ)
    (hℓ' : ℓ'.val ≠ 0) (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ) :
    ∃ v₀ : W, ∀ q, q ∈ mirabolic (m + 1) F.Carrier →
      ℓ'.val (σ q v₀) = integralShellValue (standardCharacter (ψ.scale (-1)) (m + 1)) χ q := by
  have hint := (hasIntegerConductor_of_additiveConductor_eq_zero F ψ hψ).1
  have hψ' : ∀ x ∈ (ValuativeRel.valuation F.Carrier).integer, ψ.scale (-1) x = 1 := by
    intro x hx
    rw [UnitaryAdditiveCharacter.scale_apply]
    apply hint
    rw [Units.val_neg, Units.val_one, neg_one_mul]
    exact neg_mem hx
  have hθ : standardCharacter (ψ.scale (-1)) (m + 1) = inverseStandardCharacter ψ (m + 1) :=
    standardCharacter_scale_neg_one ψ (m + 1)
  let ℓneg : glFunctionals (ψ.scale (-1)) (m + 1) σ :=
    ⟨ℓ'.val, by simpa only [glFunctionals, hθ] using ℓ'.property⟩
  have hσneg : IsOfWhittakerType (m + 1) (standardCharacter (ψ.scale (-1)) (m + 1)) σ := by
    rw [hθ]
    exact isOfInverseWhittakerType_of_isGeneric F hσ
  obtain ⟨fneg, hfneg⟩ := Whittaker.modelKirillovTransfer whittakerTypeKirillov p inferInstance F
    F.canonicalTopologicalData (m + 1) W σ (ψ.scale (-1)) hσneg ℓneg hℓ' _
    (isMirabolicTestFunction_integralShell F (ψ.scale (-1)) hψ' χ hχ)
  obtain ⟨v₀, rfl⟩ := modelMap_surjective σ ℓneg fneg
  exact ⟨v₀, fun q hq => hfneg q hq⟩

/-- `d ↦ diag(d I_(m+1), 1)`. -/
def shellScalar (m : ℕ) : F.Carrierˣ →* GeneralLinear (m + 1 + 1) F.Carrier :=
  (rankInclusion 1).comp (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)))

theorem continuous_shellScalar : Continuous (shellScalar F m) :=
  (rankInclusionContinuous 1).continuous.comp scalarContinuous.continuous

/-- The weight `d ↦ χ(d)^(m+1)` on `O^×`, extended by `0`. -/
def shellWeight (χ : F.Carrierˣ →* ℂˣ) (m : ℕ) (d : F.Carrierˣ) : ℂ :=
  (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ).indicator
    (fun d => (χ d : ℂ) ^ (m + 1)) d

theorem shellWeight_mul (χ : F.Carrierˣ →* ℂˣ) {k : F.Carrierˣ}
    (hk : k ∈ integralUnits (ValuativeRel.valuation F.Carrier).integer) (d : F.Carrierˣ) :
    shellWeight F χ m (k * d) = (χ k : ℂ) ^ (m + 1) * shellWeight F χ m d := by
  unfold shellWeight
  by_cases hd : d ∈ integralUnits (ValuativeRel.valuation F.Carrier).integer
  · rw [Set.indicator_of_mem (show k * d ∈
        (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) from
        mul_mem hk hd),
      Set.indicator_of_mem (show d ∈
        (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) from hd),
      map_mul, Units.val_mul, mul_pow]
  · have hkd : k * d ∉ integralUnits (ValuativeRel.valuation F.Carrier).integer := fun h =>
      hd (by simpa using mul_mem (inv_mem hk) h)
    rw [Set.indicator_of_notMem hkd, Set.indicator_of_notMem hd, mul_zero]

theorem shellWeight_isLocallyConstant (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ) :
    IsLocallyConstant (shellWeight F χ m) := by
  let K₀ : OpenSubgroup F.Carrierˣ :=
    integralUnitsOpen _ (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)) ⊓
      unitKernel F χ hχ
  intro S
  refine isOpen_preimage_of_mul_invariant K₀ _ (fun d k hk => ?_) S
  rw [mul_comm, shellWeight_mul F χ hk.1, MonoidHom.mem_ker.1 hk.2, Units.val_one, one_pow,
    one_mul]

theorem shellWeight_hasCompactSupport (χ : F.Carrierˣ →* ℂˣ) :
    HasCompactSupport (shellWeight F χ m) := by
  have : T2Space F.Carrier := localField_t2 F.Carrier
  exact HasCompactSupport.intro' (integralUnits_isCompact _)
    (integralUnitsOpen _ (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier))).isClosed
    (fun d hd => Set.indicator_of_notMem hd _)

/-- The Kirillov shell vector, an internal substitute for the vector `W'` of Jacquet and
Shalika 1985, (4.4.16)–(4.4.17) (see `KirillovShell.md`, Provenance). For a generic `σ`
of rank `m + 2` with central character `ω_σ`, a nonzero functional `ℓ'` for the inverse
standard character, a continuous character `χ`, any `ϖ ∈ F^×` and `c : ℕ`, the model of
`(σ, ℓ')` contains `f'` with `f'(diag(B, 1)) ≠ 0` only if `u B ϖ^c` is integral for some upper
unipotent `u`, with `f'(diag(k ϖ^(-c), 1)) = χ(det k)⁻¹` for integral `k`, and with
`f'(g · diag(I, d)) = ω_σ(d) χ(d)^(m+1) f'(g)` for integral units `d`. -/
theorem exists_kirillovShell (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0)
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (σ : Representation ℂ (GeneralLinear (m + 1 + 1) F.Carrier) W)
    (hσ : Whittaker.IsGeneric ψ (m + 1) σ) (ωσ : F.Carrierˣ →* ℂˣ)
    (hωσ : Classification.HasGLCentralCharacter F.Carrier (m + 1 + 1) σ ωσ)
    (ℓ' : glInverseFunctionals ψ (m + 1) σ) (hℓ' : ℓ'.val ≠ 0)
    (χ : F.Carrierˣ →* ℂˣ) (hχ : Continuous χ) (ϖ : F.Carrierˣ) (c : ℕ) :
    ∃ (f' : (coefficientModel σ ℓ').toSubmodule) (κ₁ : ℂ), κ₁ ≠ 0 ∧
      (∀ B : GeneralLinear (m + 1) F.Carrier, f'.val.val (rankInclusion 1 B) ≠ 0 →
        ∃ u : upperUnipotent (m + 1) F.Carrier,
          IsIntegralMatrix (u.val * B * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c))) ∧
      (∀ k : GeneralLinear (m + 1) F.Carrier, IsIntegralMatrix k →
        f'.val.val (rankInclusion 1
          (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)) =
          κ₁ * ((χ (determinant k) : ℂ))⁻¹) ∧
      (∀ (g : GeneralLinear (m + 1 + 1) F.Carrier)
        (c' : lowerTriangularSubgroup 1 F.Carrier), IsIntegralUnit (c'.val 0 0) →
          f'.val.val (g * lowerBlockPair (1 : GeneralLinear (m + 1) F.Carrier) 0 c') =
            ((ωσ * χ ^ (m + 1)) (determinant c'.val) : ℂ) * f'.val.val g) := by
  have hθ := isIntegrallyTrivial_standardCharacter
    (fun x hx => by
      rw [UnitaryAdditiveCharacter.scale_apply]
      apply (hasIntegerConductor_of_additiveConductor_eq_zero F ψ hψ).1
      rw [Units.val_neg, Units.val_one, neg_one_mul]
      exact neg_mem hx : ∀ x ∈ (ValuativeRel.valuation F.Carrier).integer, ψ.scale (-1) x = 1)
    (m + 1)
  have hO := Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)
  obtain ⟨v₀, hv₀⟩ := exists_integralShell_vector F ψ hψ σ hσ ℓ' hℓ' χ hχ
  let v₁ : W := σ (rankInclusion 1 (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c))) v₀
  let μ := localMultiplicativeHaar F.Carrier
  let v₂ : W := mapSmear μ σ hσ.2.1.1 (shellScalar F m) (continuous_shellScalar F)
    (shellWeight F χ m) (shellWeight_isLocallyConstant F χ hχ) (shellWeight_hasCompactSupport F χ)
    v₁
  let f' : (coefficientModel σ ℓ').toSubmodule := ⟨coefficientMap σ ℓ' v₂, v₂, rfl⟩
  have hf' : ∀ g, f'.val.val g =
      ∫ e, shellWeight F χ m e * ℓ'.val (σ (g * shellScalar F m e) v₁) ∂μ := by
    intro g
    refine (mapSmear_dual μ σ hσ.2.1.1 (shellScalar F m) (continuous_shellScalar F) _
      (shellWeight_isLocallyConstant F χ hχ) (shellWeight_hasCompactSupport F χ) v₁
      (ℓ'.val ∘ₗ σ g)).trans ?_
    congr 1
    funext e
    rw [LinearMap.comp_apply, map_mul, Module.End.mul_apply]
  have hshell : ∀ (X : GeneralLinear (m + 1) F.Carrier) (e : F.Carrierˣ),
      ℓ'.val (σ (rankInclusion 1 X * shellScalar F m e) v₁) =
        integralShellValue (standardCharacter (ψ.scale (-1)) (m + 1)) χ
          (rankInclusion 1 (X * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) e *
            Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c))) := by
    intro X e
    rw [← hv₀ _ (rankInclusion_lastRow _)]
    have hm : rankInclusion 1 X * shellScalar F m e *
        rankInclusion 1 (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)) =
        rankInclusion 1 (X * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) e *
          Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)) := by
      rw [map_mul, map_mul]
      rfl
    rw [← hm, map_mul σ _ (rankInclusion 1 _)]
    rfl
  refine ⟨f', 1, one_ne_zero, fun B hB => ?_, fun k hk => ?_, fun g c' hc' => ?_⟩
  · -- the support condition
    rw [hf'] at hB
    obtain ⟨e, he⟩ : ∃ e, shellWeight F χ m e *
        ℓ'.val (σ (rankInclusion 1 B * shellScalar F m e) v₁) ≠ 0 := by
      by_contra hcon
      exact hB (integral_eq_zero_of_ae (Filter.Eventually.of_forall
        fun e => not_not.1 (not_exists.1 hcon e)))
    rw [hshell] at he
    have heO : e ∈ integralUnits (ValuativeRel.valuation F.Carrier).integer := by
      by_contra h
      exact left_ne_zero_of_mul he (Set.indicator_of_notMem h _)
    have hsh : IsIntegralShell (rankInclusion 1 (B * Matrix.GeneralLinearGroup.scalar
        (Fin (m + 1)) e * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c))) := by
      by_contra h
      exact right_ne_zero_of_mul he (integralShellValue_of_not χ h)
    obtain ⟨u₁, hu₁⟩ := exists_isIntegralMatrix_of_isIntegralShell hsh
    refine ⟨u₁, ?_⟩
    have h3 := mul_mem ((isIntegralMatrix_iff_mem_level F _).1 hu₁)
      ((isIntegralMatrix_iff_mem_level F _).1 (isIntegralMatrix_scalar (m := m) (inv_mem heO)))
    rw [isIntegralMatrix_iff_mem_level]
    convert h3 using 1
    simp only [mul_assoc, ← map_mul]
    rw [show e * (ϖ ^ c * e⁻¹) = ϖ ^ c by rw [mul_comm (ϖ ^ c), mul_inv_cancel_left]]
  · -- the values on the integral shell
    rw [hf']
    have hint : ∀ e, shellWeight F χ m e * ℓ'.val (σ (rankInclusion 1
        (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹) * shellScalar F m e) v₁) =
        (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ).indicator
          (fun _ => ((χ (determinant k) : ℂ))⁻¹) e := by
      intro e
      rw [hshell]
      have hX : k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹ *
          Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) e *
          Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c) =
          k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) e := by
        simp only [mul_assoc, ← map_mul]
        rw [show (ϖ ^ c)⁻¹ * (e * ϖ ^ c) = e by rw [mul_comm e, inv_mul_cancel_left]]
      rw [hX]
      unfold shellWeight
      by_cases he : e ∈ integralUnits (ValuativeRel.valuation F.Carrier).integer
      · have hke : IsIntegralMatrix (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) e) :=
          (isIntegralMatrix_iff_mem_level F _).2 (mul_mem ((isIntegralMatrix_iff_mem_level F _).1 hk)
            ((isIntegralMatrix_iff_mem_level F _).1 (isIntegralMatrix_scalar he)))
        rw [integralShellValue_rankInclusion hθ χ _ hke, Set.indicator_of_mem he,
          Set.indicator_of_mem he, map_mul determinant, determinant_scalar, map_mul χ, map_pow χ,
          Units.val_mul, Units.val_pow_eq_pow_val]
        have hb : ((χ e : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        have ha : ((χ (determinant k) : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
        field_simp
      · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem he, zero_mul]
    rw [integral_congr_ae (Filter.Eventually.of_forall hint),
      integral_indicator_const _ (integralUnits_isOpen _ hO).measurableSet, measureReal_def,
      localMultiplicativeHaar_integerUnits, ENNReal.toReal_one, one_smul, one_mul]
  · -- the equivariance under `diag(I, d)`
    have hd : ((determinant c'.val : F.Carrierˣ) : F.Carrier) = c'.val 0 0 :=
      Matrix.det_unique _
    have hdO : determinant c'.val ∈ integralUnits (ValuativeRel.valuation F.Carrier).integer := by
      rw [mem_integralUnits, Units.val_inv_eq_inv_val, hd]
      exact ⟨hc'.2.1, hc'.2.2⟩
    rw [lowerBlockPair_eq_scalar_mul, hf', hf']
    let d := determinant c'.val
    let Φ : F.Carrierˣ → ℂ := fun e => ℓ'.val (σ (g * shellScalar F m e) v₁)
    let G : F.Carrierˣ → ℂ := fun e => (ωσ d : ℂ) * (shellWeight F χ m (d * e) * Φ e)
    have hstep : ∀ e, ℓ'.val (σ (g * (Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 1)) d *
        rankInclusion 1 (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) d⁻¹)) *
          shellScalar F m e) v₁) = (ωσ d : ℂ) * Φ (d⁻¹ * e) := by
      intro e
      have hm : g * (Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 1)) d *
          rankInclusion 1 (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) d⁻¹)) *
            shellScalar F m e = Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 1)) d *
              (g * shellScalar F m (d⁻¹ * e)) := by
        calc _ = Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 1)) d * g *
              rankInclusion 1 (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) d⁻¹) *
                shellScalar F m e := by
              rw [← mul_assoc g, ← Matrix.GeneralLinearGroup.scalar_commute d g]
          _ = Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 1)) d *
              (g * (rankInclusion 1 (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) d⁻¹) *
                shellScalar F m e)) := by
              simp only [mul_assoc]
          _ = _ := by
              rw [map_mul (shellScalar F m)]
              rfl
      rw [hm, map_mul σ (Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 1)) d),
        Module.End.mul_apply, hωσ d, map_smul, smul_eq_mul]
    have h1 : ∀ e, shellWeight F χ m e * ℓ'.val (σ (g *
        (Matrix.GeneralLinearGroup.scalar (Fin (m + 1 + 1)) d *
          rankInclusion 1 (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) d⁻¹)) *
            shellScalar F m e) v₁) = G (d⁻¹ * e) := by
      intro e
      change _ = (ωσ d : ℂ) * (shellWeight F χ m (d * (d⁻¹ * e)) * Φ (d⁻¹ * e))
      rw [hstep, mul_inv_cancel_left, mul_left_comm]
    have h2 : ∀ e, G e = ((ωσ * χ ^ (m + 1)) d : ℂ) * (shellWeight F χ m e * Φ e) := by
      intro e
      change (ωσ d : ℂ) * (shellWeight F χ m (d * e) * Φ e) = _
      rw [shellWeight_mul F χ hdO, MonoidHom.mul_apply, Units.val_mul, MonoidHom.pow_apply,
        Units.val_pow_eq_pow_val]
      ring
    calc _ = ∫ e, G (d⁻¹ * e) ∂μ := integral_congr_ae (Filter.Eventually.of_forall h1)
      _ = ∫ e, G e ∂μ := integral_mul_left_eq_self G d⁻¹
      _ = ∫ e, ((ωσ * χ ^ (m + 1)) d : ℂ) * (shellWeight F χ m e * Φ e) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall h2)
      _ = _ := integral_const_mul _ _

end Padic

/-- The Kirillov shell input of the adjacent-rank step holds. -/
theorem kirillovShellInput : KirillovShellInput.{uF, uW} := by
  intro p _ F ψ hψ m W _ _ σ hσ ωσ hωσ ℓ' hℓ' χ ϖ c
  let := F.canonicalTopologicalData.topology
  exact exists_kirillovShell F ψ hψ σ hσ ωσ hωσ ℓ' hℓ' χ χ.continuous ϖ c

end Langlands.RankinSelberg.HighlyRamified
