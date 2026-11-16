import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Instances.Rat
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Analysis.Convex.Cone.Dual
import Mathlib.Tactic

/-! # Rational functionals preserving finite strict positivity -/

noncomputable section

namespace Langlands.LinearAlgebra

variable {V I : Type*} [AddCommGroup V] [Module ℚ V] [Finite I]

/-- A real-valued rational-linear functional positive on a finite family can
be replaced by a rational-valued one positive on that family. -/
theorem exists_rat_dual_positive (v : I → V) (f : V →ₗ[ℚ] ℝ)
    (hf : ∀ i, 0 < f (v i)) :
    ∃ g : V →ₗ[ℚ] ℚ, ∀ i, 0 < g (v i) := by
  classical
  let b := Module.Basis.ofVectorSpace ℚ V
  let U : Set ((Module.Basis.ofVectorSpaceIndex ℚ V) → ℝ) :=
    {r | ∀ i, 0 < (b.constr ℚ r) (v i)}
  have hcont (i : I) : Continuous
      (fun r : Module.Basis.ofVectorSpaceIndex ℚ V → ℝ => (b.constr ℚ r) (v i)) := by
    simp only [Module.Basis.constr_apply, Finsupp.sum]
    fun_prop
  have hopen : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (hcont i)
  have hbf : b.constr ℚ (fun j => f (b j)) = f := by
    apply b.ext
    intro j
    simp
  have hnonempty : U.Nonempty := ⟨fun j => f (b j), by simpa [U, hbf] using hf⟩
  have hdense : DenseRange
      (fun q : Module.Basis.ofVectorSpaceIndex ℚ V → ℚ => fun j => (q j : ℝ)) :=
    DenseRange.piMap fun _ => Rat.isDenseEmbedding_coe_real.dense
  obtain ⟨q, hq⟩ := hdense.exists_mem_open hopen hnonempty
  refine ⟨b.constr ℚ q, fun i => ?_⟩
  have h := hq i
  have he : ((b.constr ℚ q) (v i) : ℝ) =
      (b.constr ℚ (fun j => (q j : ℝ))) (v i) := by
    simp [Module.Basis.constr_apply, Finsupp.sum, Algebra.smul_def]
  rw [← he] at h
  exact_mod_cast h

/-- Finite strict positivity can be rationalized while retaining exact
vanishing on a prescribed rational subspace. -/
theorem exists_rat_dual_positive_annihilating (W : Submodule ℚ V)
    (v : I → V) (f : V →ₗ[ℚ] ℝ) (hW : W ≤ f.ker)
    (hf : ∀ i, 0 < f (v i)) :
    ∃ g : V →ₗ[ℚ] ℚ, W ≤ g.ker ∧ ∀ i, 0 < g (v i) := by
  obtain ⟨g, hg⟩ := exists_rat_dual_positive (fun i => W.mkQ (v i))
    (W.liftQ f hW) hf
  refine ⟨g.comp W.mkQ, ?_, hg⟩
  intro x hx
  change g (Submodule.Quotient.mk x) = 0
  rw [(Submodule.Quotient.mk_eq_zero W).mpr hx, map_zero]

/-- Finitely many directions in a closed cone, whose negatives are outside
the cone, admit a common strictly positive supporting functional. -/
theorem exists_real_dual_nonneg_positive
    {E J : Type*} [AddCommGroup E] [Module ℝ E] [Module.Finite ℝ E] [Finite J]
    (C : PointedCone ℝ E)
    (hC : @IsClosed _ (moduleTopology ℝ E) (C : Set E))
    (v : J → E) (hv : ∀ j, v j ∈ C) (hneg : ∀ j, -v j ∉ C) :
    ∃ f : E →ₗ[ℝ] ℝ, (∀ x ∈ C, 0 ≤ f x) ∧ ∀ j, 0 < f (v j) := by
  classical
  let := moduleTopology ℝ E
  let := IsModuleTopology.toContinuousAdd ℝ E
  let e := (Module.finBasis ℝ E).equivFun
  let D : ProperCone ℝ (Fin (Module.finrank ℝ E) → ℝ) :=
    { toSubmodule := C.map e.toLinearMap
      isClosed' := by
        change IsClosed (e.toEquiv '' (C : Set E))
        rw [e.toEquiv.image_eq_preimage_symm]
        exact hC.preimage (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap) }
  have hsep (j : J) : ∃ f : E →ₗ[ℝ] ℝ,
      (∀ x ∈ C, 0 ≤ f x) ∧ 0 < f (v j) := by
    have hout : e (-v j) ∉ D := by
      rintro ⟨x, hx, he⟩
      exact hneg j (e.injective he ▸ hx)
    obtain ⟨f, hf, hfj⟩ := D.hyperplane_separation_point hout
    refine ⟨f.toLinearMap.comp e.toLinearMap,
      fun x hx => hf (e x) ⟨x, hx, rfl⟩, ?_⟩
    simpa only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      LinearEquiv.coe_coe, map_neg, neg_lt_zero] using hfj
  choose f hf hpos using hsep
  let := Fintype.ofFinite J
  refine ⟨∑ j, f j, ?_, ?_⟩
  · intro x hx
    simp only [LinearMap.sum_apply]
    exact Finset.sum_nonneg fun j _ => hf j x hx
  · intro j
    simp only [LinearMap.sum_apply]
    exact Finset.sum_pos' (fun a _ => hf a (v j) (hv j))
      ⟨j, Finset.mem_univ j, hpos j⟩

end Langlands.LinearAlgebra
