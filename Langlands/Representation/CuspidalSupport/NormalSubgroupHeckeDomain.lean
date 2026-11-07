import Langlands.Representation.CuspidalSupport.NormalSubgroupHecke
import Mathlib.Algebra.Group.UniqueProds.Basic

/-!
# The Hecke algebra of an open normal subgroup is a domain

Let `H` be an open normal subgroup of a topological group `G` such that `G ⧸ H` has unique
products (for instance a subgroup of a free abelian group), and let `ρ` be an irreducible
smooth complex representation of `H`. Then `End (ind_H^G ρ)` is a domain: the convolution of
two nonzero Hecke functions is nonzero at a product of unique-product cosets.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (H : Subgroup G) (ρ : SmoothRep.{0, uG, uV} ℂ H) [hN : H.Normal]

omit [IsTopologicalGroup G] hN in
/-- A Hecke function which is nonzero at `g` is nonzero on the whole coset `g H`. -/
theorem hecke_ne_zero_of_mk_eq {φ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ)
    {g g' : G} (hg : φ g ≠ 0) (h : (g : G ⧸ H) = g') : φ g' ≠ 0 := by
  intro h0
  apply hg
  have hk : g⁻¹ * g' ∈ H := QuotientGroup.eq.mp h
  have e : g = g' * (((⟨g⁻¹ * g', hk⟩ : H)⁻¹ : H) : G) := by
    change g = g' * (g⁻¹ * g')⁻¹
    group
  rw [e, hecke_mul_right H ρ hφ, h0, zero_mul]

omit [IsTopologicalGroup G] in
/-- A nonzero value of a Hecke function is injective: it intertwines `ρ` with its conjugate
`k ↦ ρ(g k g⁻¹)`, so its kernel is a subrepresentation. -/
theorem hecke_injective [ρ.representation.IsIrreducible] {φ : G → Module.End ℂ ρ}
    (hφ : φ ∈ heckeSubmodule H ρ) {g : G} (hg : φ g ≠ 0) : Function.Injective (φ g) := by
  refine injective_of_twisted ρ.representation (φ g)
    (fun k => ⟨g * k * g⁻¹, hN.conj_mem _ k.2 g⟩) (fun k v => ?_) hg
  have e : g * (k : G) = ((⟨g * k * g⁻¹, hN.conj_mem _ k.2 g⟩ : H) : G) * g := by
    change g * (k : G) = g * k * g⁻¹ * g
    group
  calc φ g (ρ.representation k v) = φ (g * k) v := by
        rw [← Module.End.mul_apply, ← hecke_mul_right H ρ hφ]
    _ = φ (((⟨g * k * g⁻¹, hN.conj_mem _ k.2 g⟩ : H) : G) * g) v :=
        congrArg (fun z => φ z v) e
    _ = _ := by rw [hecke_mul_left H ρ hφ, Module.End.mul_apply]

omit [IsTopologicalGroup G] in
/-- The convolution of two nonzero Hecke functions is nonzero, when `G ⧸ H` has unique
products. At `x = g y`, where `g H` and `y H` form a unique product of the coset supports,
only the coset `g H` contributes, and it contributes the composite of an injective value with
a nonzero value. -/
theorem heckeConvolution_ne_zero [UniqueProds (G ⧸ H)] [ρ.representation.IsIrreducible]
    {φ ψ : G → Module.End ℂ ρ} (hφ : φ ∈ heckeSubmodule H ρ) (hψ : ψ ∈ heckeSubmodule H ρ)
    (hφ0 : φ ≠ 0) (hψ0 : ψ ≠ 0) : heckeConvolution H ρ φ ψ ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ0 (funext h)
  obtain ⟨y₀, hy₀⟩ : ∃ g, ψ g ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ0 (funext h)
  let S := hφ.2.toFinset
  let T := hψ.2.toFinset
  have hS : S.Nonempty := ⟨g₀, hφ.2.mem_toFinset.mpr ⟨g₀, hg₀, rfl⟩⟩
  have hT : T.Nonempty := ⟨y₀, hψ.2.mem_toFinset.mpr ⟨y₀, hy₀, rfl⟩⟩
  obtain ⟨a, ha, b, hb, hu⟩ := UniqueProds.uniqueMul_of_nonempty hS hT
  obtain ⟨g, hg, rfl⟩ := hφ.2.mem_toFinset.mp ha
  obtain ⟨y, hy, rfl⟩ := hψ.2.mem_toFinset.mp hb
  have hsum : heckeConvolution H ρ φ ψ (g * y) =
      φ (g : G ⧸ H).out * ψ ((g : G ⧸ H).out⁻¹ * (g * y)) := by
    refine finsum_eq_single _ (g : G ⧸ H) fun q hq => ?_
    by_contra hne
    apply hq
    have h1 : φ q.out ≠ 0 := fun h => hne (by rw [h, zero_mul])
    have h2 : ψ (q.out⁻¹ * (g * y)) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hmem1 : q ∈ S := hφ.2.mem_toFinset.mpr ⟨q.out, h1, QuotientGroup.out_eq' q⟩
    have hmem2 : ((q.out⁻¹ * (g * y) : G) : G ⧸ H) ∈ T :=
      hψ.2.mem_toFinset.mpr ⟨_, h2, rfl⟩
    refine (hu hmem1 hmem2 ?_).1
    rw [QuotientGroup.mk_mul (N := H) (a := q.out⁻¹) (b := g * y), QuotientGroup.mk_inv,
      QuotientGroup.out_eq', mul_inv_cancel_left, QuotientGroup.mk_mul]
  have hA : φ (g : G ⧸ H).out ≠ 0 :=
    hecke_ne_zero_of_mk_eq H ρ hφ hg (QuotientGroup.out_eq' _).symm
  have hB : ψ ((g : G ⧸ H).out⁻¹ * (g * y)) ≠ 0 := by
    refine hecke_ne_zero_of_mk_eq H ρ hψ hy ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq', QuotientGroup.mk_mul,
      inv_mul_cancel_left]
  obtain ⟨w, hw⟩ : ∃ w, ψ ((g : G ⧸ H).out⁻¹ * (g * y)) w ≠ 0 := by
    by_contra h
    push Not at h
    exact hB (LinearMap.ext h)
  intro h0
  have hx := congrFun h0 (g * y)
  rw [hsum] at hx
  refine hecke_injective H ρ hφ hA |>.ne hw ?_
  rw [map_zero]
  exact LinearMap.congr_fun hx w

variable (hH : IsOpen (H : Set G))
include hH

/-- `End (ind_H^G ρ)` has no zero divisors, when `G ⧸ H` has unique products. -/
theorem noZeroDivisors [UniqueProds (G ⧸ H)] [ρ.representation.IsIrreducible] :
    NoZeroDivisors (End (inducedRep H ρ)) := by
  refine ⟨fun {α β} h => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨hα, hβ⟩ := hne
  have hne : ∀ γ : End (inducedRep H ρ), γ ≠ 0 →
      (heckeEquiv H ρ hH γ : G → Module.End ℂ ρ) ≠ 0 := by
    intro γ hγ h0
    apply hγ
    apply (heckeEquiv H ρ hH).injective
    rw [map_zero]
    exact Subtype.ext h0
  apply heckeConvolution_ne_zero H ρ (heckeEquiv H ρ hH α).2 (heckeEquiv H ρ hH β).2
    (hne α hα) (hne β hβ)
  rw [← heckeEquiv_mul, h, map_zero]
  rfl

/-- `End (ind_H^G ρ)` is nontrivial: the identity does not kill `f_{w₀}` for `w₀ ≠ 0`. -/
theorem nontrivial [ρ.representation.IsIrreducible] : Nontrivial (End (inducedRep H ρ)) := by
  obtain ⟨w₀, hw₀⟩ := exists_ne_zero_of_isIrreducible ρ.representation
  refine ⟨⟨1, 0, fun h => hw₀ ?_⟩⟩
  have h1 : (heckeEquiv H ρ hH 1 : G → Module.End ℂ ρ) 1 w₀ = w₀ := by
    rw [heckeEquiv_apply]
    exact eval_unitFunction_one H hH ρ.representation ρ.isSmooth w₀
  rw [h, map_zero] at h1
  exact h1.symm

/-- `End (ind_H^G ρ)` is a domain, when `G ⧸ H` has unique products. -/
theorem isDomain [UniqueProds (G ⧸ H)] [ρ.representation.IsIrreducible] :
    IsDomain (End (inducedRep H ρ)) :=
  haveI := noZeroDivisors H ρ hH
  haveI := nontrivial H ρ hH
  NoZeroDivisors.to_isDomain _

end Langlands.CuspidalSupport.NormalHecke
