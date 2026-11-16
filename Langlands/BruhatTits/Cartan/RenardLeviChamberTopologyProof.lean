import Langlands.BruhatTits.Cartan.RenardLeviChamberTopologyStatement
import Langlands.GroupScheme.Rational.StandardLeviCentralDirectionsProof
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Mathlib.Topology.Algebra.Module.Basic

/-! # Topology of the actual standard-Levi chamber -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Filter Topology
open scoped TensorProduct
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.BruhatTits.Cartan.RenardLeviCones

private theorem finite_halfspace_topology {E I : Type*} [AddCommGroup E] [Module ℝ E]
    (S : Set I) (hS : S.Finite) (q : I → E →ₗ[ℝ] ℝ)
    (hne : {x : E | ∀ a ∈ S, 0 < q a x}.Nonempty) :
    letI : TopologicalSpace E := moduleTopology ℝ E
    IsOpen {x : E | ∀ a ∈ S, 0 < q a x} ∧
    IsClosed {x : E | ∀ a ∈ S, 0 ≤ q a x} ∧
    closure {x : E | ∀ a ∈ S, 0 < q a x} = {x : E | ∀ a ∈ S, 0 ≤ q a x} := by
  let : TopologicalSpace E := moduleTopology ℝ E
  let : ContinuousAdd E := IsModuleTopology.toContinuousAdd ℝ E
  have hq (a : I) : Continuous (q a) := IsModuleTopology.continuous_of_linearMap (q a)
  have hopen : IsOpen {x : E | ∀ a ∈ S, 0 < q a x} := by
    have heq : {x : E | ∀ a ∈ S, 0 < q a x} = ⋂ a ∈ S, {x : E | 0 < q a x} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [heq]
    exact hS.isOpen_biInter fun a _ => isOpen_lt continuous_const (hq a)
  have hclosed : IsClosed {x : E | ∀ a ∈ S, 0 ≤ q a x} := by
    have heq : {x : E | ∀ a ∈ S, 0 ≤ q a x} = ⋂ a ∈ S, {x : E | 0 ≤ q a x} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [heq]
    exact isClosed_biInter fun a _ => isClosed_le continuous_const (hq a)
  refine ⟨hopen, hclosed, Set.Subset.antisymm ?_ ?_⟩
  · exact closure_minimal (fun x hx a ha => (hx a ha).le) hclosed
  · intro x hx
    obtain ⟨y, hy⟩ := hne
    have hmem : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        x + t • y ∈ {z : E | ∀ a ∈ S, 0 < q a z} := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      intro a ha
      rw [map_add, map_smul, smul_eq_mul]
      exact add_pos_of_nonneg_of_pos (hx a ha) (mul_pos ht (hy a ha))
    have hlim : Tendsto (fun t : ℝ => x + t • y) (𝓝[>] 0) (𝓝 x) := by
      simpa using (tendsto_const_nhds.add (tendsto_id.smul_const y)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)
    exact mem_closure_of_tendsto hlim hmem

/-- The actual standard-Levi chamber is nonempty, open, and has the nonstrict
chamber as its closure in the canonical real module topology. -/
theorem leviChamberTopology : LeviChamberTopologyStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro ν hν J hJ L j hj hL A a ha f hf
  obtain ⟨ζ, hζ⟩ := (standardCocharacter k G hG T i hi ν hν J hJ).1
  obtain ⟨_, hA⟩ := standardLeviCentralDirections.2 k G hG T i hi ν hν J hJ L j hj hL
  obtain ⟨_, g, hg, _, _, hgrange, _⟩ := hA A a ha
  have hgf : g = f := eq_of_groupHom_comp_eq i j hg hf
  subst g
  have hζmem : (1 : ℝ) ⊗ₜ[ℤ] ζ ∈ rootAnnihilator T J := by
    rw [mem_rootAnnihilator]
    intro α hα
    simp only [eval_tmul, hζ.2.1 α hα, Int.cast_zero, mul_zero]
  rw [← hgrange] at hζmem
  obtain ⟨y, hy⟩ := hζmem
  have hchamber : y ∈ chamber i ν J f := by
    rintro β ⟨α, ⟨hα, hαJ⟩, rfl⟩
    rw [pair_restrictedRootVector, hy, eval_tmul, one_mul]
    exact_mod_cast hζ.2.2 α hα hαJ
  have hne : (chamber i ν J f).Nonempty := ⟨y, hchamber⟩
  have hfin : (simpleRelativeRoots i ν).Finite := by
    have h := (standardLeviCentralDirections.1 k G hG T i hi ν hν
      (simpleRelativeRoots i ν) Set.Subset.rfl).1
    exact Set.finite_coe_iff.mp h
  exact ⟨hne, finite_halfspace_topology (restrictedSimpleRoots i ν J f)
    (finite_restrictedSimpleRoots i ν J f hfin) (pair A) hne⟩

end Langlands.BruhatTits.Cartan.RenardLeviCones
