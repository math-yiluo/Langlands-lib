import Langlands.Automorphic.CuspidalAdmissible.PolynomialRayleigh
import Langlands.Representation.Unitary.CountableDualAdmissible
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-! Orthogonality in a finite Casimir window detects orthogonality in the whole subspace. -/

noncomputable section
set_option autoImplicit false

open Polynomial

namespace Langlands.Automorphic.CuspidalAdmissible

section Symmetric

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

private theorem starProjection_commute_of_symmetric (T : Module.End ℂ V) (hT : T.IsSymmetric)
    (Z : Submodule ℂ V) [Z.HasOrthogonalProjection] (hZ : ∀ z ∈ Z, T z ∈ Z) (x : V) :
    Z.starProjection (T x) = T (Z.starProjection x) := by
  apply Z.eq_starProjection_of_mem_of_inner_eq_zero
    (hZ _ (Z.orthogonalProjectionOnto x).property)
  intro z hz
  rw [← map_sub, hT]
  exact (Z.mem_orthogonal' _).mp (Z.sub_starProjection_mem_orthogonal x) (T z) (hZ z hz)

/-- For a locally finite symmetric operator, vectors in a polynomial kernel
test orthogonality to an invariant subspace on its intersection with that kernel. -/
theorem mem_orthogonal_of_inf_aeval_ker
    (T : Module.End ℂ V) (hT : T.IsSymmetric)
    (hfinite : ∀ x, ∃ q : ℂ[X], q ≠ 0 ∧ aeval T q x = 0)
    (U : Submodule ℂ V) (hU : ∀ u ∈ U, T u ∈ U)
    (p : ℂ[X]) {v : V} (hv : aeval T p v = 0)
    (horth : v ∈ (U ⊓ LinearMap.ker (aeval T p))ᗮ) : v ∈ Uᗮ := by
  apply (U.mem_orthogonal' _).mpr
  intro u hu
  obtain ⟨q, hq, hqu⟩ := hfinite u
  let q₀ := C q.leadingCoeff⁻¹ * q
  have hq₀ : q₀.Monic :=
    monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ (leadingCoeff_ne_zero.mpr hq))
  have hq₀u : aeval T q₀ u = 0 := by
    dsimp only [q₀]
    rw [map_mul, Module.End.mul_apply, hqu, map_zero]
  let Z := cyclicSpan T u q₀.natDegree
  have hZU : Z ≤ U := by
    rintro _ ⟨r, _, rfl⟩
    exact aeval_mem_of_stable T hU r hu
  have hZ : ∀ z ∈ Z, T z ∈ Z := fun _ hz => apply_mem_cyclicSpan T hq₀ hq₀u hz
  have huZ : u ∈ Z := mem_cyclicSpan_self T hq₀ hq₀u
  have hproj : aeval T p (Z.starProjection v) = 0 := by
    have h := aeval_apply_commute (B := Z.starProjection.toLinearMap)
      (starProjection_commute_of_symmetric T hT Z hZ) p v
    rw [hv, map_zero] at h
    exact h.symm
  have hvZ : Z.starProjection v ∈ Z := (Z.orthogonalProjectionOnto v).property
  have hin := ((U ⊓ LinearMap.ker (aeval T p)).mem_orthogonal' _).mp horth
    (Z.starProjection v) ⟨hZU hvZ, hproj⟩
  have hminus := (Z.mem_orthogonal' _).mp (Z.sub_starProjection_mem_orthogonal v)
  have hself := hminus (Z.starProjection v) hvZ
  rw [inner_sub_left, hin, zero_sub, neg_eq_zero] at hself
  have hz : Z.starProjection v = 0 := inner_self_eq_zero.mp hself
  simpa only [hz, sub_zero] using hminus u huZ

end Symmetric

section FixedVectors

variable {G V : Type*} [Group G] [TopologicalSpace G] [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ G V) (A B : Module.End ℂ V)

/-- Vectors fixed by the level subgroup and killed by both specified polynomials. -/
def fixedPolynomialKernels (L : OpenSubgroup G) (q p : ℂ[X]) : Submodule ℂ V :=
  (fixedVectors ρ L.toSubgroup ⊓ LinearMap.ker (aeval A q)) ⊓ LinearMap.ker (aeval B p)

end FixedVectors

section OrthogonalSplitting

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  (ρ : Representation ℂ G V) (A B : Module.End ℂ V)

/-- Finite-dimensional simultaneous fixed spaces in polynomial kernels give
orthogonal complements to the subspaces stable under the group and both operators. -/
theorem isCompl_orthogonal_of_finite_fixedPolynomialKernels
    (hρ : IsSmooth ρ) (b : InvariantPositiveForm ρ)
    (hinner : ∀ v w, inner ℂ v w = b.inner v w)
    (hlevels : ∀ v, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧
      v ∈ fixedVectors ρ L.toSubgroup)
    (hA : A.IsSymmetric) (hB : B.IsSymmetric)
    (hAf : ∀ v, ∃ q : ℂ[X], q ≠ 0 ∧ aeval A q v = 0)
    (hBf : ∀ v, ∃ p : ℂ[X], p ≠ 0 ∧ aeval B p v = 0)
    (hAρ : ∀ g v, ρ g (A v) = A (ρ g v))
    (hBρ : ∀ g v, ρ g (B v) = B (ρ g v))
    (hAB : ∀ v, B (A v) = A (B v))
    (hfinite : ∀ L q p, q ≠ 0 → p ≠ 0 → FiniteDimensional ℂ (fixedPolynomialKernels ρ A B L q p))
    (U : Submodule ℂ V) (hUρ : ∀ g v, v ∈ U → ρ g v ∈ U)
    (hUA : ∀ v ∈ U, A v ∈ U) (hUB : ∀ v ∈ U, B v ∈ U) :
    IsCompl U Uᗮ := by
  refine IsCompl.of_eq U.inf_orthogonal_eq_bot (eq_top_iff.mpr fun v _ => ?_)
  obtain ⟨L, hLc, hvL⟩ := hlevels v
  obtain ⟨q, hq, hqv⟩ := hAf v
  obtain ⟨p, hp, hpv⟩ := hBf v
  let E := fixedPolynomialKernels ρ A B L q p
  let U₀ := U ⊓ fixedVectors ρ L.toSubgroup
  let U₁ := U₀ ⊓ LinearMap.ker (aeval A q)
  let U₂ := U₁ ⊓ LinearMap.ker (aeval B p)
  have hE : FiniteDimensional ℂ E := hfinite L q p hq hp
  have hle : U₂ ≤ E := fun _ hx => ⟨⟨hx.1.1.2, hx.1.2⟩, hx.2⟩
  have : FiniteDimensional ℂ U₂ :=
    FiniteDimensional.of_injective (Submodule.inclusion hle) (Submodule.inclusion_injective hle)
  let u := U₂.starProjection v
  have hu : u ∈ U₂ := (U₂.orthogonalProjectionOnto v).property
  let w := v - u
  have hwE : w ∈ E := E.sub_mem ⟨⟨hvL, hqv⟩, hpv⟩ (hle hu)
  have hw₂ : w ∈ U₂ᗮ := U₂.sub_starProjection_mem_orthogonal v
  have hlevelStable (T : Module.End ℂ V) (hTU : ∀ x ∈ U, T x ∈ U)
      (hTρ : ∀ g x, ρ g (T x) = T (ρ g x)) : ∀ x ∈ U₀, T x ∈ U₀ := by
    intro x hx
    exact ⟨hTU x hx.1, fun l => (hTρ l.val x).trans (congrArg T (hx.2 l))⟩
  have hU₁B : ∀ x ∈ U₁, B x ∈ U₁ := by
    intro x hx
    refine ⟨hlevelStable B hUB hBρ x hx.1, ?_⟩
    change aeval A q (B x) = 0
    rw [← aeval_apply_commute hAB, LinearMap.mem_ker.mp hx.2, map_zero]
  have hw₁ : w ∈ U₁ᗮ :=
    mem_orthogonal_of_inf_aeval_ker B hB hBf U₁ hU₁B p hwE.2 hw₂
  have hw₀ : w ∈ U₀ᗮ :=
    mem_orthogonal_of_inf_aeval_ker A hA hAf U₀ (hlevelStable A hUA hAρ) q hwE.1.2 hw₁
  have hwU : w ∈ Uᗮ := by
    apply (U.mem_orthogonal' _).mpr
    intro x hx
    have hx₀ : Compact.averageMap ρ hρ L hLc x ∈ U₀ :=
      ⟨CountableDual.averageMap_mem ρ hρ U hUρ L hLc hx,
        Compact.averageMap_mem_fixedVectors ρ hρ L hLc x⟩
    have hzero := (U₀.mem_orthogonal' _).mp hw₀ _ hx₀
    rw [hinner, CountableDual.inner_averageMap ρ hρ b L hLc w hwE.1.1, ← hinner] at hzero
    exact hzero
  exact Submodule.mem_sup.mpr ⟨u, hu.1.1.1, w, hwU, by dsimp [w]; abel⟩

end OrthogonalSplitting

end Langlands.Automorphic.CuspidalAdmissible
