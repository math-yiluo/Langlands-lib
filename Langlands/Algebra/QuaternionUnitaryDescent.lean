import Langlands.Algebra.QuaternionUnitaryInvolution
import Langlands.Algebra.ReducedCharpolyDivision
import Langlands.Algebra.DivisionReducedCharpoly

/-!
# Descent of a quaternion algebra with a unitary involution

Let `L/K` be a quadratic extension with nontrivial automorphism `σ`, and let `D` be a central
division `L`-algebra of reduced degree `2` with a unitary involution `τ` relative to `σ`. The
fixed points `D₀` of the `σ`-semilinear automorphism `β = τ ∘ γ` (with `γ` the canonical
involution) form a central division `K`-algebra of dimension `4`, and its reduced norm is the
restriction of that of `D`.
-/

noncomputable section

namespace Langlands.UnitaryInvolution

universe u

open Langlands.CentralDivision Langlands.CentralSimple _root_.Polynomial
open scoped TensorProduct

variable {K L D : Type u} [Field K] [Field L] [Algebra K L] [DivisionRing D] [Algebra L D]
  [FiniteDimensional L D] [Algebra.IsCentral L D] [Algebra K D] [IsScalarTower K L D]
  {σ : L →+* L} {τ : D → D}

section Fixed

variable (hd : reducedDegree L D = 2) (hτ : IsUnitaryInvolution (⇑σ) τ)
  (hσK : ∀ k : K, σ (algebraMap K L k) = algebraMap K L k)
include hd hτ hσK

theorem beta_algebraMap_base (k : K) : beta L τ (algebraMap K D k) = algebraMap K D k := by
  rw [IsScalarTower.algebraMap_apply K L D, beta_algebraMap hd hτ, hσK]

/-- The fixed subalgebra `D₀` of `β = τ ∘ γ`. -/
def fixedSubalgebra : Subalgebra K D where
  carrier := {x | beta L τ x = x}
  mul_mem' {x y} hx hy := by
    change beta L τ (x * y) = x * y
    rw [beta_mul hd hτ, hx, hy]
  add_mem' {x y} hx hy := by
    change beta L τ (x + y) = x + y
    rw [← beta_add hτ, hx, hy]
  algebraMap_mem' k := beta_algebraMap_base hd hτ hσK k

theorem mem_fixedSubalgebra {x : D} :
    x ∈ fixedSubalgebra hd hτ hσK ↔ beta L τ x = x := Iff.rfl


theorem beta_smul_base (k : K) (y : D) : beta L τ (k • y) = k • beta L τ y := by
  rw [Algebra.smul_def, beta_mul hd hτ, beta_algebraMap_base hd hτ hσK, ← Algebra.smul_def]

/-- `β` as a `K`-linear map. -/
def betaLinear : D →ₗ[K] D where
  toFun := beta L τ
  map_add' x y := (beta_add hτ x y).symm
  map_smul' k y := beta_smul_base hd hτ hσK k y

@[simp] theorem betaLinear_apply (y : D) : betaLinear hd hτ hσK y = beta L τ y := rfl

omit [Algebra K D] [IsScalarTower K L D] hσK in
theorem beta_mul_algebraMap (c : L) (y : D) :
    beta L τ (algebraMap L D c * y) = algebraMap L D (σ c) * beta L τ y := by
  rw [beta_mul hd hτ, beta_algebraMap hd hτ]

theorem add_beta_mem (y : D) : y + beta L τ y ∈ fixedSubalgebra hd hτ hσK := by
  change beta L τ (y + beta L τ y) = y + beta L τ y
  rw [← beta_add hτ, beta_beta hd hτ, add_comm]

theorem twisted_add_beta_mem (c : L) (y : D) :
    algebraMap L D c * y + beta L τ (algebraMap L D c * y) ∈ fixedSubalgebra hd hτ hσK :=
  add_beta_mem hd hτ hσK _

variable {θ : L} (hθ : σ θ ≠ θ)
include hθ

omit [Algebra K D] [IsScalarTower K L D] hσK hθ in
/-- Galois descent: every element is an `L`-combination of two fixed elements. -/
theorem descent_eq (y : D) :
    algebraMap L D (σ θ - θ) * y =
      algebraMap L D (σ θ) * (y + beta L τ y) -
        (algebraMap L D θ * y + beta L τ (algebraMap L D θ * y)) := by
  rw [beta_mul_algebraMap hd hτ, map_sub, sub_mul, mul_add]
  abel

omit [FiniteDimensional L D] [Algebra.IsCentral L D] [Algebra K D] [IsScalarTower K L D] hd hτ
  hσK in
theorem algebraMap_sub_ne_zero : algebraMap L D (σ θ - θ) ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap L D).injective).mpr (sub_ne_zero.mpr hθ)

/-- An element commuting with all fixed elements commutes with everything. -/
theorem commute_of_commute_fixed {z : D}
    (hz : ∀ a ∈ fixedSubalgebra hd hτ hσK, z * a = a * z) (y : D) : z * y = y * z := by
  have hu := algebraMap_sub_ne_zero (D := D) hθ
  have h1 := hz _ (add_beta_mem hd hτ hσK y)
  have h2 := hz _ (twisted_add_beta_mem hd hτ hσK θ y)
  have key : algebraMap L D (σ θ - θ) * (z * y) = algebraMap L D (σ θ - θ) * (y * z) := by
    calc algebraMap L D (σ θ - θ) * (z * y) = z * (algebraMap L D (σ θ - θ) * y) := by
          rw [← mul_assoc, Algebra.commutes, mul_assoc]
      _ = z * (algebraMap L D (σ θ) * (y + beta L τ y) -
            (algebraMap L D θ * y + beta L τ (algebraMap L D θ * y))) := by
          rw [descent_eq hd hτ]
      _ = algebraMap L D (σ θ) * (z * (y + beta L τ y)) -
            z * (algebraMap L D θ * y + beta L τ (algebraMap L D θ * y)) := by
          rw [mul_sub, ← mul_assoc, ← Algebra.commutes, mul_assoc]
      _ = algebraMap L D (σ θ) * ((y + beta L τ y) * z) -
            (algebraMap L D θ * y + beta L τ (algebraMap L D θ * y)) * z := by
          rw [h1, h2]
      _ = (algebraMap L D (σ θ) * (y + beta L τ y) -
            (algebraMap L D θ * y + beta L τ (algebraMap L D θ * y))) * z := by
          rw [sub_mul, mul_assoc]
      _ = algebraMap L D (σ θ - θ) * (y * z) := by
          rw [← descent_eq hd hτ, mul_assoc]
  exact mul_left_cancel₀ hu key

omit [Algebra K D] [IsScalarTower K L D] hσK hθ in
theorem beta_zero : beta L τ (0 : D) = 0 := by
  simpa using beta_algebraMap hd hτ (D := D) 0

/-- The dimension count `[D : K] = 2 [D₀ : K]` from Galois descent. -/
theorem two_mul_finrank_fixed [FiniteDimensional K L] :
    2 * Module.finrank K (Subalgebra.toSubmodule (fixedSubalgebra hd hτ hσK)) =
      Module.finrank K D := by
  have : FiniteDimensional K D := Module.Finite.trans L D
  let V := Subalgebra.toSubmodule (fixedSubalgebra hd hτ hσK)
  let mθ : D →ₗ[K] D := LinearMap.mulLeft K (algebraMap L D θ)
  let Φ : V × V →ₗ[K] D := V.subtype.coprod (mθ.comp V.subtype)
  let P : D →ₗ[K] D := LinearMap.id + betaLinear hd hτ hσK
  have hP : ∀ y, P y ∈ V := fun y => add_beta_mem hd hτ hσK y
  let Ψ : D →ₗ[K] V × V :=
    (LinearMap.codRestrict V P hP).prod (LinearMap.codRestrict V (P.comp mθ) (fun y => hP _))
  have hΦ : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨a, b⟩ h
    have ha : beta L τ (a : D) = a := a.prop
    have hb : beta L τ (b : D) = b := b.prop
    change (a : D) + algebraMap L D θ * (b : D) = 0 at h
    have h' := congrArg (beta L τ) h
    rw [← beta_add hτ, beta_mul_algebraMap hd hτ, ha, hb, beta_zero hd hτ] at h'
    have hb0 : algebraMap L D (σ θ - θ) * (b : D) = 0 := by
      rw [map_sub, sub_mul, ← sub_eq_zero.mpr (h'.trans h.symm)]
      abel
    have hb0' : (b : D) = 0 :=
      (mul_eq_zero.mp hb0).resolve_left (algebraMap_sub_ne_zero (D := D) hθ)
    have ha0 : (a : D) = 0 := by rw [hb0', mul_zero, add_zero] at h; exact h
    ext <;> simp [ha0, hb0']
  have hΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y h
    have h1 : y + beta L τ y = 0 := congrArg (fun p : V × V => ((p.1 : V) : D)) h
    have h2 : algebraMap L D θ * y + beta L τ (algebraMap L D θ * y) = 0 :=
      congrArg (fun p : V × V => ((p.2 : V) : D)) h
    have h3 := descent_eq hd hτ (θ := θ) y
    rw [h1, h2, mul_zero, sub_zero] at h3
    exact (mul_eq_zero.mp h3).resolve_left (algebraMap_sub_ne_zero (D := D) hθ)
  have e1 := LinearMap.finrank_le_finrank_of_injective hΦ
  have e2 := LinearMap.finrank_le_finrank_of_injective hΨ
  rw [Module.finrank_prod] at e1 e2
  show 2 * Module.finrank K V = Module.finrank K D
  omega

end Fixed

section FixedAlgebra

variable [FiniteDimensional K L] (hd : reducedDegree L D = 2) (hτ : IsUnitaryInvolution (⇑σ) τ)
  (hσK : ∀ k : K, σ (algebraMap K L k) = algebraMap K L k)

theorem fixed_finiteDimensional : FiniteDimensional K (fixedSubalgebra hd hτ hσK) := by
  have : FiniteDimensional K D := Module.Finite.trans L D
  exact Module.Finite.of_injective (fixedSubalgebra hd hτ hσK).val.toLinearMap
    Subtype.val_injective

/-- The division-ring structure on the finite-dimensional domain `D₀`. -/
@[instance_reducible]
def fixedDivisionRing : DivisionRing (fixedSubalgebra hd hτ hσK) :=
  letI := fixed_finiteDimensional hd hτ hσK
  divisionRingOfFiniteDimensional K _

variable {θ : L} (hθ : σ θ ≠ θ)
include hθ

theorem finrank_fixed (hrank : Module.finrank K L = 2) :
    Module.finrank K (fixedSubalgebra hd hτ hσK) = 4 := by
  have h := two_mul_finrank_fixed hd hτ hσK hθ
  rw [Subalgebra.finrank_toSubmodule, ← Module.finrank_mul_finrank K L D, hrank,
    (reducedNorm_degree_spec L D).2, hd] at h
  omega

variable (hfix : ∀ ℓ : L, σ ℓ = ℓ → ∃ k : K, algebraMap K L k = ℓ)
include hfix

omit [FiniteDimensional K L] in
theorem fixed_isCentral : Algebra.IsCentral K (fixedSubalgebra hd hτ hσK) := by
  constructor
  intro z hz
  rw [Subalgebra.mem_center_iff] at hz
  have hcomm : ∀ y : D, (z : D) * y = y * z := by
    apply commute_of_commute_fixed hd hτ hσK hθ
    intro a ha
    exact (congrArg Subtype.val (hz ⟨a, ha⟩)).symm
  have hzc : (z : D) ∈ Subalgebra.center L D := by
    rw [Subalgebra.mem_center_iff]
    intro y
    exact (hcomm y).symm
  obtain ⟨ℓ, hℓ⟩ := (Algebra.IsCentral.mem_center_iff L).mp hzc
  have hβ : beta L τ (z : D) = z := z.prop
  rw [hℓ, beta_algebraMap hd hτ] at hβ
  obtain ⟨k, hk⟩ := hfix ℓ ((algebraMap L D).injective hβ)
  rw [Algebra.mem_bot]
  refine ⟨k, Subtype.ext ?_⟩
  rw [hℓ, ← hk, ← IsScalarTower.algebraMap_apply]
  rfl

omit hfix in
theorem reducedDegree_fixed (hrank : Module.finrank K L = 2) :
    reducedDegree K (fixedSubalgebra hd hτ hσK) = 2 := by
  rw [reducedDegree, finrank_fixed hd hτ hσK hθ hrank]
  exact Nat.sqrt_eq 2

/-- The reduced norm of `D` restricts on `D₀` to the reduced norm of `D₀`. -/
theorem nrd_fixed (hrank : Module.finrank K L = 2) (y : fixedSubalgebra hd hτ hσK) :
    letI := fixedDivisionRing hd hτ hσK
    letI := fixed_finiteDimensional hd hτ hσK
    letI := fixed_isCentral hd hτ hσK hθ hfix
    nrd L (y : D) = algebraMap K L (nrd K y) := by
  let := fixedDivisionRing hd hτ hσK
  let := fixed_finiteDimensional hd hτ hσK
  let := fixed_isCentral hd hτ hσK hθ hfix
  have hd0 := reducedDegree_fixed hd hτ hσK hθ hrank
  have hβ : beta L τ (y : D) = y := y.prop
  by_cases hy : (y : D) ∈ Set.range (algebraMap L D)
  · obtain ⟨ℓ, hℓ⟩ := hy
    rw [← hℓ, beta_algebraMap hd hτ] at hβ
    obtain ⟨k, hk⟩ := hfix ℓ ((algebraMap L D).injective hβ)
    have hyk : y = algebraMap K (fixedSubalgebra hd hτ hσK) k := by
      apply Subtype.ext
      rw [← hℓ, ← hk, ← IsScalarTower.algebraMap_apply]
      rfl
    rw [← hℓ, nrd_algebraMap, hd, hyk, nrd_algebraMap, hd0, ← hk, map_pow]
  · have hyK : y ∉ Set.range (algebraMap K (fixedSubalgebra hd hτ hσK)) := by
      rintro ⟨k, hk⟩
      apply hy
      refine ⟨algebraMap K L k, ?_⟩
      rw [← IsScalarTower.algebraMap_apply, ← hk]
      rfl
    have hintL : IsIntegral L (y : D) := Algebra.IsIntegral.isIntegral _
    have hintK : IsIntegral K y := Algebra.IsIntegral.isIntegral _
    have hL : minpoly L (y : D) = reducedCharpoly L D (y : D) := by
      refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintL)
        (reducedCharpoly_monic L D _) (minpoly_dvd_reducedCharpoly L D _) ?_).symm
      rw [reducedCharpoly_natDegree, hd]
      exact (minpoly.two_le_natDegree_iff hintL).mpr hy
    have hK : minpoly K y = reducedCharpoly K (fixedSubalgebra hd hτ hσK) y := by
      refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintK)
        (reducedCharpoly_monic K _ _) (minpoly_dvd_reducedCharpoly K _ _) ?_).symm
      rw [reducedCharpoly_natDegree, hd0]
      exact (minpoly.two_le_natDegree_iff hintK).mpr hyK
    have hKD : minpoly K (y : D) = minpoly K y :=
      minpoly.algHom_eq (fixedSubalgebra hd hτ hσK).val Subtype.val_injective y
    have hmap : minpoly L (y : D) = (minpoly K y).map (algebraMap K L) := by
      have hdvd := minpoly.dvd_map_of_isScalarTower K L (y : D)
      rw [hKD] at hdvd
      refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hintL)
        ((minpoly.monic hintK).map _) hdvd ?_).symm
      rw [natDegree_map, hK, reducedCharpoly_natDegree, hd0, hL, reducedCharpoly_natDegree, hd]
    have h1 := reducedCharpoly_coeff_zero_two L D hd (y : D)
    have h2 := reducedCharpoly_coeff_zero_two K (fixedSubalgebra hd hτ hσK) hd0 y
    rw [nrd, nrd, ← h1, ← h2, ← hL, ← hK, hmap, coeff_map]

end FixedAlgebra

end Langlands.UnitaryInvolution
