import Langlands.BushnellKutzko.RepresentationIntertwining
import Langlands.LinearAlgebra.IrreducibleRepresentationSpan
import Mathlib.RepresentationTheory.Character

/-! # The trace of a scalar extension of square degree -/

noncomputable section
open scoped MonoidAlgebra

namespace Langlands.BushnellKutzko

universe uG uV uW

section Trace

variable {G : Type uG} [Group G] {W : Type uW} [AddCommGroup W] [Module ℂ W]
  [FiniteDimensional ℂ W]

private theorem trace_postcompose (g : Module.End ℂ W) :
    LinearMap.trace ℂ (Module.End ℂ W) (g.compRight ℂ) =
      (Module.finrank ℂ W : ℂ) * LinearMap.trace ℂ W g := by
  let e := dualTensorHomEquiv ℂ W W
  have h : e.conj (g.lTensor (Module.Dual ℂ W)) = g.compRight ℂ := by
    apply LinearMap.ext
    intro f
    have he := LinearMap.congr_fun (dualTensorHom_comp_lTensor (M := W) g) (e.symm f)
    change e (g.lTensor (Module.Dual ℂ W) (e.symm f)) = g.compRight ℂ (e (e.symm f)) at he
    rw [e.apply_symm_apply] at he
    exact he
  rw [← h, LinearMap.trace_conj']
  change LinearMap.trace ℂ _ (TensorProduct.map LinearMap.id g) = _
  rw [LinearMap.trace_tensorProduct', LinearMap.trace_id, Module.finrank_linearMap_self]

/-- An irreducible representation acting by scalars on a normal subgroup of
index equal to the square of its degree has trace zero outside that subgroup. -/
theorem character_eq_zero_of_scalar_index (ρ : Representation ℂ G W) [ρ.IsIrreducible]
    (N : Subgroup G) [N.Normal] (θ : N →* ℂˣ)
    (hscalar : ∀ n : N, ρ n = (θ n : ℂ) • LinearMap.id)
    (hdim : Module.finrank ℂ W ^ 2 = N.index) (g : G) (hg : g ∉ N) : ρ.character g = 0 := by
  classical
  have : Nontrivial W := IsSimpleModule.nontrivial ℂ[G] ρ.asModule
  have hdim_pos : 0 < Module.finrank ℂ W := Module.finrank_pos
  have : N.FiniteIndex := ⟨hdim ▸ pow_ne_zero 2 hdim_pos.ne'⟩
  let Q := G ⧸ N
  let π := QuotientGroup.mk' N
  let : Fintype Q := Fintype.ofFinite Q
  let f : Q → Module.End ℂ W := fun x => ρ x.out
  have hmultiple (x : G) : ∃ c : ℂ, ρ x = c • f (π x) := by
    obtain ⟨n, hn⟩ := QuotientGroup.mk_out_eq_mul N x
    have heq : (π x).out * (n⁻¹ : N) = x := by
      change (QuotientGroup.mk x : Q).out * (n⁻¹ : N) = x
      rw [hn, Subgroup.coe_inv, mul_inv_cancel_right]
    refine ⟨(θ n⁻¹ : ℂ), ?_⟩
    have h := congrArg ρ heq
    rw [map_mul, hscalar n⁻¹, mul_smul_comm, ← Module.End.one_eq_id, mul_one] at h
    exact h.symm
  have hspan : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    rw [← Langlands.LinearAlgebra.irreducibleRepresentationSpan_proof ℂ G W ρ inferInstance]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    obtain ⟨c, hc⟩ := hmultiple x
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨π x, rfl⟩)
  have hcard : Fintype.card Q = Module.finrank ℂ (Module.End ℂ W) := by
    rw [Fintype.card_eq_nat_card, Module.finrank_linearMap, ← pow_two, hdim]
    rfl
  let b := basisOfTopLeSpanOfCardEqFinrank f hspan hcard
  have hb : ⇑b = f := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  have htrace : LinearMap.trace ℂ (Module.End ℂ W) ((ρ g).compRight ℂ) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace]
    apply Finset.sum_eq_zero
    intro q _
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    change b.repr (ρ g * b q) q = 0
    rw [show b q = ρ q.out from congrFun hb q, ← map_mul]
    obtain ⟨c, hc⟩ := hmultiple (g * q.out)
    have hneq : π (g * q.out) ≠ q := by
      rw [map_mul, show π q.out = q from QuotientGroup.out_eq' q]
      intro heq
      exact hg ((QuotientGroup.eq_one_iff g).mp (mul_right_cancel (heq.trans (one_mul q).symm)))
    rw [hc, ← hb, map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_of_ne hneq.symm,
      smul_zero]
  rw [trace_postcompose] at htrace
  have hcast : (Module.finrank ℂ W : ℂ) ≠ 0 := by exact_mod_cast hdim_pos.ne'
  exact (mul_eq_zero.mp htrace).resolve_left hcast

end Trace

section Average

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

/-- If the representation on linear maps is trivial on a normal subgroup and
has trace zero off it, the dimension of the intertwining maps is the full
linear-map dimension divided by the subgroup index. -/
theorem finrank_intertwiningMap_mul_index_of_trace_support
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (D : Subgroup G)
    [D.Normal] [D.FiniteIndex] (htriv : ∀ g ∈ D, Representation.linHom ρ σ g = 1)
    (hzero : ∀ g ∉ D, (Representation.linHom ρ σ).character g = 0) :
    Module.finrank ℂ (ρ.IntertwiningMap σ) * D.index =
      Module.finrank ℂ (V →ₗ[ℂ] W) := by
  classical
  let τ := Representation.linHom ρ σ
  let Q := G ⧸ D
  let π := QuotientGroup.mk' D
  let : Representation.IsTrivial (τ.comp D.subtype) := ⟨fun g => htriv g g.property⟩
  let τQ := τ.ofQuotient D
  let : Fintype Q := Fintype.ofFinite Q
  have hcard : (Nat.card Q : ℂ) ≠ 0 := by exact_mod_cast D.index_ne_zero_of_finite
  let : Invertible (Nat.card Q : ℂ) := invertibleOfNonzero hcard
  have hchar : ∑ q : Q, τQ.character q = (Module.finrank ℂ (V →ₗ[ℂ] W) : ℂ) := by
    rw [← Representation.char_one τQ]
    refine Finset.sum_eq_single 1 (fun q _ hq => ?_) (fun he => (he (Finset.mem_univ 1)).elim)
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
    change τ.character g = 0
    exact hzero g fun hg => hq ((QuotientGroup.eq_one_iff g).mpr hg)
  have hfixed : τQ.invariants = τ.invariants := by
    ext f
    rw [Representation.mem_invariants, Representation.mem_invariants]
    constructor
    · intro hf g
      exact hf (π g)
    · intro hf q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D q
      exact hf g
  have h := Representation.card_inv_mul_sum_char_eq_finrank τQ
  rw [hchar, hfixed, (Representation.invariantsEquivIntertwiningMap ρ σ).finrank_eq] at h
  have hmul := ((inv_mul_eq_iff_eq_mul₀ hcard).mp h).symm
  rw [mul_comm] at hmul
  exact_mod_cast hmul

end Average

end Langlands.BushnellKutzko
