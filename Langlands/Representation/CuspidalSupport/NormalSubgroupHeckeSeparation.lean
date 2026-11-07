import Langlands.Representation.CuspidalSupport.NormalSubgroupHeckeDomain
import Langlands.Algebra.UnitalSeparationProof

/-!
# Simple right modules separate the Hecke algebra of an open normal subgroup

Let `H` be an open normal subgroup of a topological group `G` such that `G ⧸ H` is countable
and has unique products, and let `ρ` be an irreducible smooth complex representation of `H`
of countable dimension. Then `R = End (ind_H^G ρ)` has countable dimension, and an element
of `R` acting as zero on every simple right `R`-module is zero: it is not nilpotent unless
it is zero, because `R` is a domain, and the published separation lemma of Renard B.III
applies to `Rᵐᵒᵖ`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.CuspidalSupport.NormalHecke

universe uG uV

open Induction

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- An open subgroup of a separable topological group has countably many cosets: every
coset is open and nonempty, so it meets a fixed countable dense set. -/
theorem countable_quotient_of_isOpen [TopologicalSpace.SeparableSpace G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) : Countable (G ⧸ H) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense G
  have : Countable D := hDc.to_subtype
  refine Function.Surjective.countable (f := fun d : D => ((d : G) : G ⧸ H)) fun q => ?_
  have hU : IsOpen ((fun x => q.out⁻¹ * x) ⁻¹' (H : Set G)) :=
    hH.preimage (continuous_const_mul _)
  obtain ⟨d, hd, hdU⟩ := hDd.exists_mem_open hU ⟨q.out, by simp⟩
  refine ⟨⟨d, hd⟩, ?_⟩
  have e : ((q.out : G) : G ⧸ H) = d := QuotientGroup.eq.mpr hdU
  rw [QuotientGroup.out_eq'] at e
  exact e.symm

variable (H : Subgroup G) (ρ : SmoothRep.{0, uG, uV} ℂ H) [hN : H.Normal]

omit [IsTopologicalGroup G] hN in
/-- The values `φ(q.out) w₀` at the chosen coset representatives, for a fixed vector `w₀`;
only finitely many are nonzero. -/
def heckeSample (w₀ : ρ) : heckeSubmodule H ρ →ₗ[ℂ] (G ⧸ H →₀ ρ) where
  toFun φ := Finsupp.ofSupportFinite (fun q => (φ : G → Module.End ℂ ρ) q.out w₀) (by
    refine φ.2.2.subset ?_
    intro q hq
    refine ⟨q.out, fun h0 => hq ?_, QuotientGroup.out_eq' q⟩
    simp [h0])
  map_add' φ ψ := by
    ext q
    simp [Finsupp.ofSupportFinite_coe]
  map_smul' c φ := by
    ext q
    simp [Finsupp.ofSupportFinite_coe]

omit [IsTopologicalGroup G] in
/-- For `w₀ ≠ 0`, a Hecke function is determined by the vectors `φ(q.out) w₀`: a nonzero value
of `φ` is injective, and `φ` vanishes on a coset as soon as it vanishes at its representative. -/
theorem heckeSample_injective [ρ.representation.IsIrreducible] {w₀ : ρ} (hw₀ : w₀ ≠ 0) :
    Function.Injective (heckeSample H ρ w₀) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro φ hφ
  rw [LinearMap.mem_ker] at hφ
  refine Subtype.ext (funext fun g => ?_)
  rw [Submodule.coe_zero, Pi.zero_apply]
  by_contra hg
  have hA : (φ : G → Module.End ℂ ρ) (g : G ⧸ H).out ≠ 0 :=
    hecke_ne_zero_of_mk_eq H ρ φ.2 hg (QuotientGroup.out_eq' _).symm
  have h2 : (φ : G → Module.End ℂ ρ) (g : G ⧸ H).out w₀ = 0 := by
    have := DFunLike.congr_fun hφ (g : G ⧸ H)
    simpa [heckeSample, Finsupp.ofSupportFinite_coe] using this
  exact hw₀ (hecke_injective H ρ φ.2 hA (by rw [h2, map_zero]))

omit [IsTopologicalGroup G] in
/-- The Hecke space has countable dimension when `G ⧸ H` is countable and `ρ` has countable
dimension. -/
theorem rank_heckeSubmodule_le [ρ.representation.IsIrreducible] [Countable (G ⧸ H)]
    (hρ : Module.rank ℂ ρ ≤ Cardinal.aleph0) :
    Module.rank ℂ (heckeSubmodule H ρ) ≤ Cardinal.aleph0 := by
  obtain ⟨w₀, hw₀⟩ := exists_ne_zero_of_isIrreducible ρ.representation
  calc Module.rank ℂ (heckeSubmodule H ρ) ≤ Module.rank ℂ (G ⧸ H →₀ ρ) :=
        LinearMap.rank_le_of_injective _ (heckeSample_injective H ρ hw₀)
    _ = Cardinal.lift.{uV} (Cardinal.mk (G ⧸ H)) * Cardinal.lift.{uG} (Module.rank ℂ ρ) :=
        rank_finsupp ℂ ρ (G ⧸ H)
    _ ≤ Cardinal.aleph0 * Cardinal.aleph0 :=
        mul_le_mul' (Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0)
          (Cardinal.lift_le_aleph0.mpr hρ)
    _ = Cardinal.aleph0 := Cardinal.aleph0_mul_aleph0

variable (hH : IsOpen (H : Set G))
include hH

/-- `End (ind_H^G ρ)` has countable dimension, through the Hecke equivalence. -/
theorem rank_end_le [ρ.representation.IsIrreducible] [Countable (G ⧸ H)]
    (hρ : Module.rank ℂ ρ ≤ Cardinal.aleph0) :
    Module.rank ℂ (End (inducedRep H ρ)) ≤ Cardinal.aleph0 := by
  rw [(heckeEquiv H ρ hH).rank_eq]
  exact rank_heckeSubmodule_le H ρ hρ

/-- Simple right modules separate `End (ind_H^G ρ)`, when `G ⧸ H` is countable with unique
products and `ρ` has countable dimension. -/
theorem separation [UniqueProds (G ⧸ H)] [Countable (G ⧸ H)] [ρ.representation.IsIrreducible]
    (hρ : Module.rank ℂ ρ ≤ Cardinal.aleph0) (α : End (inducedRep H ρ))
    (hα : ∀ (M : Type (max uG uV)) [AddCommGroup M] [Module (End (inducedRep H ρ))ᵐᵒᵖ M],
      IsSimpleModule (End (inducedRep H ρ))ᵐᵒᵖ M → ∀ m : M, MulOpposite.op α • m = 0) :
    α = 0 := by
  have := isDomain H ρ hH
  by_contra hne
  have hnil : ¬ IsNilpotent (MulOpposite.op α) := by
    rintro ⟨n, hn⟩
    apply hne
    refine IsNilpotent.eq_zero ⟨n, ?_⟩
    have := congrArg MulOpposite.unop hn
    rwa [MulOpposite.unop_pow, MulOpposite.unop_op, MulOpposite.unop_zero] at this
  have hrank : Module.rank ℂ (End (inducedRep H ρ))ᵐᵒᵖ ≤ Cardinal.aleph0 := by
    rw [← (MulOpposite.opLinearEquiv ℂ).rank_eq]
    exact rank_end_le H ρ hH hρ
  obtain ⟨I, -, hsimple, hsep⟩ := Langlands.Renard.unitalSeparation _ hrank _ hnil
  exact hsep (hα _ hsimple _)

end Langlands.CuspidalSupport.NormalHecke
