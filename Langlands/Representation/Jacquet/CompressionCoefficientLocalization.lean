import Langlands.Representation.Jacquet.CompressionLocalization
import Langlands.Algebra.RenardLocalizationStabilityProof
import Langlands.LinearAlgebra.StableEndomorphismStatements

/-! # Compact compression over a Noetherian coefficient ring -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Jacquet

universe uR uG uV uW

namespace CompressionCoefficients

section Maps

variable (R : Type uR) [CommRing R]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W] [Module R W]

/-- Retain an actual complex-linear map as an `R`-linear map once its
compatibility with the given `R`-actions has been established. -/
def map (f : V →ₗ[ℂ] W) (hf : ∀ (r : R) (x : V), f (r • x) = r • f x) :
    V →ₗ[R] W where
  toFun := f
  map_add' := map_add f
  map_smul' := hf

@[simp]
theorem map_apply (f : V →ₗ[ℂ] W)
    (hf : ∀ (r : R) (x : V), f (r • x) = r • f x) (x : V) :
    map R f hf x = f x := rfl

@[simp]
theorem map_pow_apply (f : Module.End ℂ V)
    (hf : ∀ (r : R) (x : V), f (r • x) = r • f x) (n : ℕ) (x : V) :
    (map R f hf ^ n) x = (f ^ n) x := by
  simp only [Module.End.pow_apply]
  rfl

/-- Retain the actual bijection as an `R`-linear equivalence; its inverse is
`R`-linear because the forward map is a compatible bijection. -/
def equiv (e : V ≃ₗ[ℂ] W) (he : ∀ (r : R) (x : V), e (r • x) = r • e x) :
    V ≃ₗ[R] W :=
  LinearEquiv.ofBijective (map R e.toLinearMap he) e.bijective

@[simp]
theorem equiv_apply (e : V ≃ₗ[ℂ] W)
    (he : ∀ (r : R) (x : V), e (r • x) = r • e x) (x : V) :
    equiv R e he x = e x := rfl

@[simp]
theorem equiv_pow_apply (e : V ≃ₗ[ℂ] V)
    (he : ∀ (r : R) (x : V), e (r • x) = r • e x) (n : ℕ) (x : V) :
    (equiv R e he ^ n) x = (e ^ n) x := by
  simp only [LinearEquiv.pow_apply]
  rfl

end Maps

end CompressionCoefficients

section Localization

open Renard.EndomorphismLocalization
open LinearAlgebra.StableEndomorphism

variable (R : Type uR) [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
variable {N M Nbar : Subgroup G} {g : G}
variable (h : IsIwahoriContraction K N M Nbar g) (hMN : M ≤ Subgroup.normalizer N)
variable (hcentral : ∀ m ∈ M, m * g = g * m)
variable [Module R (fixedVectors ρ K.toSubgroup)]
variable [Module R (fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))]
variable
  (hC : ∀ (r : R) (x : fixedVectors ρ K.toSubgroup),
    compressedAction ρ hρ K hK g (r • x) = r • compressedAction ρ hρ K hK g x)
  (hj : ∀ (r : R) (x : fixedVectors ρ K.toSubgroup),
    fixedJacquetMap ρ N M hMN K.toSubgroup (r • x) =
      r • fixedJacquetMap ρ N M hMN K.toSubgroup x)
  (hβ : ∀ (r : R)
    (y : fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype)),
    fixedJacquetCentralEquiv ρ h hMN hcentral (r • y) =
      r • fixedJacquetCentralEquiv ρ h hMN hcentral y)

/-- The actual `R`-localization of the coefficient-linear compressed action is
the actual Jacquet fixed-vector module with its given compatible `R`-action. -/
def coefficientCompressionJacquetLocalizationEquiv :
    Localized (CompressionCoefficients.map R (compressedAction ρ hρ K hK g) hC) ≃ₗ[R]
      fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype) :=
  localizationEquivOfKernelExhaustion
    (CompressionCoefficients.map R (compressedAction ρ hρ K hK g) hC)
    (CompressionCoefficients.equiv R (fixedJacquetCentralEquiv ρ h hMN hcentral) hβ)
    (CompressionCoefficients.map R (fixedJacquetMap ρ N M hMN K.toSubgroup) hj)
    (fixedJacquetMap_intertwines_centralEquiv ρ hρ hK h hMN hcentral)
    (by
      intro x hx
      obtain ⟨n, hn⟩ := fixedJacquetMap_kernel_locally_nilpotent ρ hρ hK h hMN x hx
      exact ⟨n, by simpa only [CompressionCoefficients.map_pow_apply] using hn⟩)
    (by
      intro y
      obtain ⟨n, x, hx⟩ := fixedJacquetCentralEquiv_power_exhaustion ρ hρ hK h hMN hcentral y
      exact ⟨n, x, by simpa only [CompressionCoefficients.equiv_pow_apply,
        CompressionCoefficients.map_apply] using hx⟩)

@[simp]
theorem coefficientCompressionJacquetLocalizationEquiv_iota (x : fixedVectors ρ K.toSubgroup) :
    coefficientCompressionJacquetLocalizationEquiv R ρ hρ K hK h hMN hcentral hC hj hβ
        (iota (CompressionCoefficients.map R (compressedAction ρ hρ K hK g) hC) x) =
      fixedJacquetMap ρ N M hMN K.toSubgroup x :=
  localizationEquivOfKernelExhaustion_iota _ _ _ _ _ _ x

theorem coefficientCompressionJacquetLocalizationEquiv_intertwines
    (z : Localized (CompressionCoefficients.map R (compressedAction ρ hρ K hK g) hC)) :
    coefficientCompressionJacquetLocalizationEquiv R ρ hρ K hK h hMN hcentral hC hj hβ
        (localizedEnd (CompressionCoefficients.map R (compressedAction ρ hρ K hK g) hC) z) =
      fixedJacquetCentralEquiv ρ h hMN hcentral
        (coefficientCompressionJacquetLocalizationEquiv R ρ hρ K hK h hMN hcentral hC hj hβ z) :=
  localizationEquivOfKernelExhaustion_intertwines _ _ _ _ _ _ z

include h hcentral hC hj hβ in
/-- The two coefficient-finiteness inputs of VI.9.2 suffice for actual quotient
surjectivity and a positive stable power of complex compact compression. -/
theorem fixedJacquetMap_surjective_and_eventuallyStable_of_finite_coefficients
    [IsNoetherianRing R]
    [Module.Finite R (fixedVectors ρ K.toSubgroup)]
    [Module.Finite R (fixedVectors (action ρ N M hMN) (K.toSubgroup.comap M.subtype))] :
    Function.Surjective (fixedJacquetMap ρ N M hMN K.toSubgroup) ∧
      EventuallyStable (compressedAction ρ hρ K hK g) := by
  let a := CompressionCoefficients.map R (compressedAction ρ hρ K hK g) hC
  let e := coefficientCompressionJacquetLocalizationEquiv R ρ hρ K hK h hMN hcentral hC hj hβ
  let : Module.Finite R (Localized a) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  obtain ⟨hsurj, ⟨n, hn, _, hk, hr⟩, _⟩ :=
    finiteActualLocalizationStatement R (fixedVectors ρ K.toSubgroup) a
      inferInstance inferInstance inferInstance
  constructor
  · intro y
    obtain ⟨x, hx⟩ := hsurj (e.symm y)
    refine ⟨x, ?_⟩
    calc
      fixedJacquetMap ρ N M hMN K.toSubgroup x = e (iota a x) :=
        (coefficientCompressionJacquetLocalizationEquiv_iota
          R ρ hρ K hK h hMN hcentral hC hj hβ x).symm
      _ = y := by rw [hx, e.apply_symm_apply]
  · refine ⟨n, hn, ?_, ?_⟩
    · ext x
      have hx : x ∈ LinearMap.ker (a ^ n) ↔ x ∈ LinearMap.ker ((a ^ n) ^ 2) := by rw [hk]
      simpa only [a, LinearMap.mem_ker, pow_two, Module.End.mul_apply,
        CompressionCoefficients.map_pow_apply] using hx
    · ext x
      have hx : x ∈ LinearMap.range (a ^ n) ↔ x ∈ LinearMap.range ((a ^ n) ^ 2) := by rw [hr]
      simpa only [a, LinearMap.mem_range, pow_two, Module.End.mul_apply,
        CompressionCoefficients.map_pow_apply] using hx

end Localization

end Langlands.Jacquet
