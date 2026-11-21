import Langlands.Automorphic.JointCompactProjection
import Langlands.Global.EisensteinOperatorCoefficients
import Langlands.Representation.Families.FiniteHolomorphicSections

/-! # Compact-projected lifts on a free module of Eisenstein seeds -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.EisensteinJet

open Langlands.Automorphic

variable {A I V : Type*} [Ring A] [Algebra ℂ A] [AddCommGroup V] [Module ℂ V]

/-- Specialization of seed combinations on the inverse image of the prescribed
numerator submodule. -/
def operatorSeedSpecialization (a : A →ₐ[ℂ] Module.End ℂ V) (v : I → V) :
    letI := Module.compHom V a.toRingHom
    ∀ N : Submodule A V, N.comap (operatorLinearCombination a v) →ₗ[A] N := by
  let := Module.compHom V a.toRingHom
  intro N
  exact (operatorLinearCombination a v).restrict fun _ h => h

@[simp]
theorem operatorSeedSpecialization_apply (a : A →ₐ[ℂ] Module.End ℂ V) (v : I → V) :
    letI := Module.compHom V a.toRingHom
    ∀ (N : Submodule A V) (w : N.comap (operatorLinearCombination a v)),
      (operatorSeedSpecialization a v N w : V) = operatorLinearCombination a v w.val := by
  let := Module.compHom V a.toRingHom
  intro N w
  rfl

/-- If the seed space contains one numerator vector with nonzero image in a
simple quotient, the induced specialization map to that quotient is onto. -/
theorem surjective_comp_operatorSeedSpecialization
    (a : A →ₐ[ℂ] Module.End ℂ V) {B : Submodule ℂ V} (e : Module.Basis I ℂ B)
    {W : Type*} [AddCommGroup W] [Module A W] [IsSimpleModule A W] :
    letI := Module.compHom V a.toRingHom
    ∀ (N : Submodule A V) (q : N →ₗ[A] W) (x : N),
      x.val ∈ B → q x ≠ 0 →
      Function.Surjective (q.comp (operatorSeedSpecialization a (fun i => (e i).val) N)) := by
  let := Module.compHom V a.toRingHom
  intro N q x hx hqx
  let v (i : I) : V := (e i).val
  let c := e.repr ⟨x.val, hx⟩
  let w : I →₀ A := c.mapRange (algebraMap ℂ A) (map_zero _)
  have hw : operatorLinearCombination a v w = x.val := by
    rw [operatorLinearCombination_apply, Finsupp.sum_mapRange_index]
    · have he := congrArg B.subtype (e.linearCombination_repr (⟨x.val, hx⟩ : B))
      simpa only [AlgHom.commutes, Module.algebraMap_end_apply, c, v, Finsupp.linearCombination_apply,
        Finsupp.sum, map_sum, map_smul, Submodule.subtype_apply] using he
    · intro i
      simp
  let u : N.comap (operatorLinearCombination a v) := ⟨w, by
    change operatorLinearCombination a v w ∈ N
    rw [hw]
    exact x.property⟩
  have hspec : operatorSeedSpecialization a v N u = x := Subtype.ext hw
  intro y
  obtain ⟨b, hb⟩ := IsSimpleModule.toSpanSingleton_surjective A hqx y
  refine ⟨b • u, ?_⟩
  rw [LinearMap.map_smul, LinearMap.comp_apply, hspec]
  exact hb

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  (a : E → A →ₐ[ℂ] Module.End ℂ V) (v : I → V)

/-- Apply the compact projection to a word family and take values in the
projection's range. -/
def projectedOperatorSection (P : Module.End ℂ V) (w : I →₀ A) (t : E) : P.range :=
  P.rangeRestrict (operatorLinearCombination (a t) v w)

theorem projectedOperatorSection_mem (P : Module.End ℂ V) (w : I →₀ A)
    (hw : (fun t => operatorLinearCombination (a t) v w) ∈ finiteHolomorphicSections E V) :
    projectedOperatorSection a v P w ∈ finiteHolomorphicSections E P.range :=
  FiniteHolomorphicSections.map_mem P.rangeRestrict hw

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type*} [Group K] {d : ℕ} (τ : Representation ℂ K (Fin d → ℂ)) [τ.IsIrreducible]
  (ρ : Representation ℂ G V) (κ : Representation ℂ K V)
  [IsSemisimpleModule (MonoidAlgebra ℂ K) κ.asModule]
  (hρ : Langlands.IsSmooth ρ) (L : OpenSubgroup G) (hL : IsCompact (L : Set G))

/-- On the finite-dimensional range of one holomorphic word family the joint
projection can be applied by one fixed algebra element at every parameter. -/
theorem exists_smul_eq_projectedOperatorSection
    (fin : L → A) (inf : K → A)
    (hfin : ∀ t g, a t (fin g) = ρ g.val) (hinf : ∀ t k, a t (inf k) = κ k)
    (w : I →₀ A)
    (hw : (fun t => operatorLinearCombination (a t) v w) ∈ finiteHolomorphicSections E V) :
    ∃ b : A, ∀ t, operatorLinearCombination (a t) v (b • w) =
      (projectedOperatorSection a v (jointCompactProjection τ ρ κ hρ L hL) w t : V) := by
  obtain ⟨S, hS, hmem⟩ := FiniteHolomorphicSections.exists_finiteDimensional_range hw
  let := hS
  obtain ⟨b, hb⟩ :=
    exists_jointCompactProjection_operator τ ρ κ hρ L hL a fin inf hfin hinf S
  refine ⟨b, fun t => ?_⟩
  let := Module.compHom V (a t).toRingHom
  have he := (operatorLinearCombination (a t) v).map_smul b w
  change operatorLinearCombination (a t) v (b • w) =
    a t b (operatorLinearCombination (a t) v w) at he
  exact he.trans (hb t _ (hmem t))

end Langlands.Global.EisensteinJet
