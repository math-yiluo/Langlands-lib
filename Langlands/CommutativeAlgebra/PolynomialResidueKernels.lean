import Langlands.CommutativeAlgebra.ValuationKernelProjection
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nakayama

/-! # Residue reduction on polynomial vectors and kernel lifting -/

universe u v w z

namespace Langlands.CommutativeAlgebra

open Module

section KernelLifting

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
variable {N : Type w} [AddCommGroup N] [Module R N] [Module.IsTorsionFree R N]
variable {P : Type z} [AddCommGroup P] [Module R P]

/-- A finite valuation kernel is determined by its image under a reduction map
whose kernel is an ideal multiple of the source. -/
theorem valuationKernel_le_of_reduction_image_le (f : M →ₗ[R] N) (g : M →ₗ[R] P)
    (I : Ideal R) (hI : I ≤ Ideal.jacobson ⊥)
    (hg : LinearMap.ker g = I • (⊤ : Submodule R M))
    (L : Submodule R M) (hL : L ≤ LinearMap.ker f)
    (himage : (LinearMap.ker f).map g ≤ L.map g) : LinearMap.ker f ≤ L := by
  have := finite_kernel_of_valuationRing f
  have hfg : (LinearMap.ker f).FG := by
    simpa using (Module.Finite.fg_top (R := R) (M := LinearMap.ker f)).map
      (LinearMap.ker f).subtype
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hfg hI
  intro x hx
  obtain ⟨y, hy, hyx⟩ := himage (Submodule.mem_map_of_mem (f := g) hx)
  have hxy : x - y ∈ LinearMap.ker f ⊓ I • (⊤ : Submodule R M) := by
    refine ⟨(LinearMap.ker f).sub_mem hx (hL hy), ?_⟩
    rw [← hg]
    change g (x - y) = 0
    rw [map_sub, hyx, sub_self]
  rw [kernel_inf_ideal_smul_of_valuationRing f I] at hxy
  exact Submodule.mem_sup.2 ⟨y, hy, x - y, hxy, by abel⟩

end KernelLifting

section PolynomialReduction

variable {R : Type u} [CommRing R] {σ : Type v}

/-- Coefficient reduction modulo an ideal, as a linear map over the original ring. -/
noncomputable def polynomialCoefficientReduction (I : Ideal R) :
    MvPolynomial σ R →ₗ[R] MvPolynomial σ (R ⧸ I) :=
  (MvPolynomial.mapAlgHom (Ideal.Quotient.mkₐ R I)).toLinearMap

@[simp]
theorem polynomialCoefficientReduction_apply (I : Ideal R) (p : MvPolynomial σ R) :
    polynomialCoefficientReduction (σ := σ) I p = MvPolynomial.map (Ideal.Quotient.mk I) p :=
  rfl

theorem polynomialCoefficientReduction_ker (I : Ideal R) :
    LinearMap.ker (polynomialCoefficientReduction (σ := σ) I) =
      I • (⊤ : Submodule R (MvPolynomial σ R)) := by
  classical
  apply le_antisymm
  · intro p hp
    have hc (d : σ →₀ ℕ) : p.coeff d ∈ I := by
      have h := congrArg (fun p : MvPolynomial σ (R ⧸ I) => p.coeff d) hp
      apply Ideal.Quotient.eq_zero_iff_mem.1
      simpa [MvPolynomial.coeff_map] using h
    rw [MvPolynomial.as_sum p]
    apply Submodule.sum_mem
    intro d hd
    have hmem := Submodule.smul_mem_smul (hc d)
      (Submodule.mem_top : MvPolynomial.monomial d (1 : R) ∈
        (⊤ : Submodule R (MvPolynomial σ R)))
    simpa [MvPolynomial.smul_monomial] using hmem
  · apply Submodule.smul_le.2
    intro r hr p _
    change polynomialCoefficientReduction I (r • p) = 0
    rw [map_smul]
    change (Ideal.Quotient.mk I r) • polynomialCoefficientReduction I p = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, zero_smul]

/-- Coefficient reduction on an actual finite vector of polynomials. -/
noncomputable def polynomialVectorReduction (I : Ideal R) (n : ℕ) :
    (Fin n → MvPolynomial σ R) →ₗ[R] (Fin n → MvPolynomial σ (R ⧸ I)) :=
  (polynomialCoefficientReduction I).compLeft (Fin n)

@[simp]
theorem polynomialVectorReduction_apply (I : Ideal R) (n : ℕ)
    (x : Fin n → MvPolynomial σ R) (i : Fin n) :
    polynomialVectorReduction I n x i = MvPolynomial.map (Ideal.Quotient.mk I) (x i) := rfl

theorem polynomialVectorReduction_ker (I : Ideal R) (n : ℕ) :
    LinearMap.ker (polynomialVectorReduction (σ := σ) I n) =
      I • (⊤ : Submodule R (Fin n → MvPolynomial σ R)) := by
  classical
  apply le_antisymm
  · intro x hx
    have hi (i : Fin n) : x i ∈ I • (⊤ : Submodule R (MvPolynomial σ R)) := by
      rw [← polynomialCoefficientReduction_ker I]
      exact congrFun hx i
    rw [← Finset.univ_sum_single x]
    apply Submodule.sum_mem
    intro i _
    have hmem := Submodule.mem_map_of_mem
      (f := LinearMap.single R (fun _ : Fin n => MvPolynomial σ R) i) (hi i)
    rw [Submodule.map_smul''] at hmem
    have hle : I • Submodule.map
        (LinearMap.single R (fun _ : Fin n => MvPolynomial σ R) i) ⊤ ≤
        I • (⊤ : Submodule R (Fin n → MvPolynomial σ R)) := smul_mono_right I le_top
    exact hle hmem
  · apply Submodule.smul_le.2
    intro r hr x _
    funext i
    change polynomialCoefficientReduction I (r • x i) = 0
    have hmem : r • x i ∈ I • (⊤ : Submodule R (MvPolynomial σ R)) :=
      Submodule.smul_mem_smul hr Submodule.mem_top
    rw [← polynomialCoefficientReduction_ker I] at hmem
    exact hmem

/-- The degree projection on finite polynomial vectors. -/
noncomputable def homogeneousPolynomialVectorComponent (n d : ℕ) :
    (Fin n → MvPolynomial σ R) →ₗ[R] (Fin n → MvPolynomial σ R) :=
  (MvPolynomial.homogeneousComponent d).compLeft (Fin n)

@[simp]
theorem homogeneousPolynomialVectorComponent_apply (n d : ℕ)
    (x : Fin n → MvPolynomial σ R) (i : Fin n) :
    homogeneousPolynomialVectorComponent n d x i = MvPolynomial.homogeneousComponent d (x i) := rfl

theorem homogeneousPolynomialVectorComponent_mem (n d : ℕ)
    (x : Fin n → MvPolynomial σ R) :
    homogeneousPolynomialVectorComponent n d x ∈ homogeneousPolynomialVectors R σ n d := by
  intro i _
  exact MvPolynomial.homogeneousComponent_mem _ _

theorem homogeneousPolynomialVectorComponent_eq_self (n d : ℕ)
    (x : Fin n → MvPolynomial σ R) (hx : x ∈ homogeneousPolynomialVectors R σ n d) :
    homogeneousPolynomialVectorComponent n d x = x := by
  funext i
  exact MvPolynomial.homogeneousComponent_eq_self (hx i trivial)

theorem homogeneousPolynomialVectorComponent_range (n d : ℕ) :
    LinearMap.range (homogeneousPolynomialVectorComponent (R := R) (σ := σ) n d) =
      homogeneousPolynomialVectors R σ n d := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact homogeneousPolynomialVectorComponent_mem _ _ _
  · intro x hx
    exact ⟨x, homogeneousPolynomialVectorComponent_eq_self _ _ _ hx⟩

theorem homogeneousPolynomialVectors_inf_ideal_smul (I : Ideal R) (n d : ℕ) :
    homogeneousPolynomialVectors R σ n d ⊓ I • (⊤ : Submodule R (Fin n → MvPolynomial σ R)) =
      I • homogeneousPolynomialVectors R σ n d := by
  apply le_antisymm
  · intro x hx
    have hm := Submodule.mem_map_of_mem
      (f := homogeneousPolynomialVectorComponent n d) hx.2
    simpa only [Submodule.map_smul'', Submodule.map_top,
      homogeneousPolynomialVectorComponent_range,
      homogeneousPolynomialVectorComponent_eq_self n d x hx.1] using hm
  · exact le_inf Submodule.smul_le_right (smul_mono_right I le_top)

/-- Residue reduction restricted to homogeneous vectors, with the full vector target. -/
noncomputable def homogeneousPolynomialVectorReduction (I : Ideal R) (n d : ℕ) :
    homogeneousPolynomialVectors R σ n d →ₗ[R] (Fin n → MvPolynomial σ (R ⧸ I)) :=
  (polynomialVectorReduction I n).comp (homogeneousPolynomialVectors R σ n d).subtype

theorem homogeneousPolynomialVectorReduction_ker (I : Ideal R) (n d : ℕ) :
    LinearMap.ker (homogeneousPolynomialVectorReduction (σ := σ) I n d) =
      I • (⊤ : Submodule R (homogeneousPolynomialVectors R σ n d)) := by
  apply Submodule.map_injective_of_injective
    (homogeneousPolynomialVectors R σ n d).injective_subtype
  rw [homogeneousPolynomialVectorReduction, LinearMap.ker_comp,
    Submodule.map_comap_subtype, polynomialVectorReduction_ker,
    homogeneousPolynomialVectors_inf_ideal_smul, Submodule.map_smul'',
    Submodule.map_subtype_top]

end PolynomialReduction

end Langlands.CommutativeAlgebra
