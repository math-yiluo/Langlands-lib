import Langlands.Weil.Representation.Operations
import Langlands.Weil.Representation.Determinant

/-! # Invariance under actual representation isomorphisms -/

noncomputable section

namespace Langlands.Weil

universe uG uV uU

namespace IsomorphismInvariance

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {U : Type uU} [AddCommGroup U] [Module ℂ U]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G U}

/-- Conjugation by an intertwining equivalence reflects the identity action. -/
theorem action_eq_one_iff (e : ρ.Equiv σ) (g : G) : ρ g = 1 ↔ σ g = 1 := by
  rw [← e.conj_apply_self g]
  exact (map_eq_one_iff e.toLinearEquiv.conjRingEquiv
    e.toLinearEquiv.conjRingEquiv.injective).symm

/-- The full group kernels coincide. -/
theorem ker_eq (e : ρ.Equiv σ) : ρ.ker = σ.ker := by
  ext g
  exact action_eq_one_iff e g

/-- The same equality holds on every subgroup, with no normality assumption. -/
theorem restricted_ker_eq (e : ρ.Equiv σ) (I : Subgroup G) :
    (ρ.comp I.subtype).ker = (σ.comp I.subtype).ker := by
  ext i
  exact action_eq_one_iff e i

/-- Finiteness of the image is invariant even after any parametrization of the group. -/
theorem finite_range_comp_iff {X : Type*} (e : ρ.Equiv σ) (f : X → G) :
    (Set.range (fun x => ρ (f x))).Finite ↔
      (Set.range (fun x => σ (f x))).Finite := by
  have h : Set.range (fun x => σ (f x)) =
      e.toLinearEquiv.conj '' Set.range (fun x => ρ (f x)) := by
    rw [← Set.range_comp]
    congr 1
    funext x
    exact (e.conj_apply_self (f x)).symm
  rw [h, Set.finite_image_iff e.toLinearEquiv.conj.injective.injOn]

/-- Irreducibility transports along the bijective map of group-algebra modules. -/
theorem irreducible_iff (e : ρ.Equiv σ) :
    Representation.IsIrreducible ρ ↔ Representation.IsIrreducible σ := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule,
    Representation.irreducible_iff_isSimpleModule_asModule]
  exact (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
    e.toIntertwiningMap).isSimpleModule_iff_of_bijective e.bijective

/-- Semisimplicity transports along the same actual module isomorphism. -/
theorem semisimple_iff (e : ρ.Equiv σ) :
    Representation.IsSemisimpleRepresentation ρ ↔
      Representation.IsSemisimpleRepresentation σ := by
  rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
    Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  exact (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ
    e.toIntertwiningMap).isSemisimpleModule_iff_of_bijective e.bijective

section Topology

variable [TopologicalSpace G]

local instance endTopology (W : Type*) [AddCommGroup W] [Module ℂ W] :
    TopologicalSpace (Module.End ℂ W) := moduleTopology ℂ (Module.End ℂ W)

/-- Linear conjugation is continuous for the canonical module topologies. -/
theorem continuous_of_equiv (e : ρ.Equiv σ) (hρ : Continuous ρ) : Continuous σ := by
  have := IsModuleTopology.toContinuousAdd ℂ (Module.End ℂ U)
  have hc := (IsModuleTopology.continuous_of_linearMap
    e.toLinearEquiv.conj.toLinearMap).comp hρ
  exact hc.congr fun g => e.conj_apply_self g

/-- No compatibility between the group topology and multiplication is needed. -/
theorem continuous_iff (e : ρ.Equiv σ) : Continuous ρ ↔ Continuous σ :=
  ⟨continuous_of_equiv e, continuous_of_equiv e.symm⟩

end Topology

end IsomorphismInvariance

/-- Every predicate and numerical invariant in the published target is preserved. -/
theorem representationIsomorphismInvariance :
    RepresentationIsomorphismInvariance.{uG, uV, uU} := by
  intro G _ _ I V _ _ _ U _ _ _ ρ σ ⟨e⟩
  refine ⟨IsomorphismInvariance.ker_eq e, IsomorphismInvariance.restricted_ker_eq e I,
    IsomorphismInvariance.continuous_iff e, ?_,
    IsomorphismInvariance.finite_range_comp_iff e id,
    IsomorphismInvariance.finite_range_comp_iff e I.subtype, ?_,
    IsomorphismInvariance.irreducible_iff e, IsomorphismInvariance.semisimple_iff e,
    FiniteRepresentation.rank_eq_of_equiv (A := FiniteRepresentation.of ρ)
      (B := FiniteRepresentation.of σ) e, ?_⟩
  · rw [IsomorphismInvariance.restricted_ker_eq e I]
  · exact forall_congr' fun i => IsomorphismInvariance.action_eq_one_iff e i
  · intro g
    exact congrArg (fun χ : G →* ℂˣ => (χ g : ℂ))
      (FiniteRepresentation.determinantCharacter_eq
        (A := FiniteRepresentation.of ρ) (B := FiniteRepresentation.of σ) e)

end Langlands.Weil
