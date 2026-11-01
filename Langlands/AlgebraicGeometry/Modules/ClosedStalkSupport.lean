import Langlands.AlgebraicGeometry.Modules.ClosedSupportTopology
import Langlands.AlgebraicGeometry.Modules.CoherentGraph
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof

/-! # The closure of actual stalk support -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Order

namespace Langlands.AlgebraicGeometry.Modules

variable {X : Scheme.{u}}

/-- The least closed subset containing the points with nonzero module stalk. -/
def closedStalkSupport (M : X.Modules) : Closeds X :=
  ⟨closure (stalkSupport M), isClosed_closure⟩

@[simp]
theorem coe_closedStalkSupport (M : X.Modules) :
    (closedStalkSupport M : Set X) = closure (stalkSupport M) := rfl

/-- The actual stalk support lies in its closed support. -/
theorem stalkSupport_subset_closedStalkSupport (M : X.Modules) :
    stalkSupport M ⊆ closedStalkSupport M := subset_closure

/-- Containment of closed stalk support is precisely vanishing off the closed set. -/
theorem closedStalkSupport_le_iff (M : X.Modules) (Z : Closeds X) :
    closedStalkSupport M ≤ Z ↔ QuasicoherentLocal.VanishesOn M Z.compl := by
  constructor
  · intro h
    apply QuasicoherentLocal.VanishesOn.of_stalkSupport_subset_compl
    intro x hx hxZ
    exact hxZ (h (subset_closure hx))
  · intro h
    apply closure_minimal _ Z.isClosed
    simpa only [Closeds.coe_compl, compl_compl] using h.stalkSupport_subset_compl

/-- Every module vanishes outside its closed stalk support. -/
theorem vanishesOn_compl_closedStalkSupport (M : X.Modules) :
    QuasicoherentLocal.VanishesOn M (closedStalkSupport M).compl :=
  (closedStalkSupport_le_iff M _).mp le_rfl

/-- A module has empty closed stalk support exactly when it is zero. -/
theorem closedStalkSupport_eq_bot_iff (M : X.Modules) :
    closedStalkSupport M = ⊥ ↔ IsZero M := by
  rw [← stalkSupport_eq_empty_iff]
  constructor
  · intro h
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have := stalkSupport_subset_closedStalkSupport M hx
    simp only [h, Closeds.coe_bot, Set.mem_empty_iff_false] at this
  · intro h
    apply Closeds.ext
    simp [h]

/-- Isomorphisms preserve the closed support. -/
theorem closedStalkSupport_eq_of_iso {M N : X.Modules} (e : M ≅ N) :
    closedStalkSupport M = closedStalkSupport N := by
  apply Closeds.ext
  simp only [coe_closedStalkSupport, stalkSupport_eq_of_iso e]

/-- The existing support-height predicate is a bound on the actual closed support. -/
theorem hasSupportDimensionLT_iff_closedStalkSupport (M : X.Modules) (e : ℕ) :
    HasSupportDimensionLT M e ↔
      ∀ T : IrreducibleCloseds X, (T : Set X) ⊆ closedStalkSupport M → height T < e := by
  constructor
  · rintro ⟨Z, hM, hZ⟩ T hT
    exact hZ T (hT.trans ((closedStalkSupport_le_iff M Z).mpr hM))
  · intro h
    exact ⟨closedStalkSupport M, vanishesOn_compl_closedStalkSupport M, h⟩

/-- Support-height bounds are exactly dimension bounds for the closed stalk support. -/
theorem hasSupportDimensionLT_iff_topologicalKrullDim_closedStalkSupport
    (M : X.Modules) (e : ℕ) :
    HasSupportDimensionLT M e ↔
      topologicalKrullDim (closedStalkSupport M : Set X) < (e : WithBot ℕ∞) := by
  rw [hasSupportDimensionLT_iff_closedStalkSupport,
    ClosedSupportTopology.topologicalKrullDim_lt_iff]

/-- A short exact sequence has middle stalk support equal to the union of the outer supports. -/
theorem stalkSupport_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    stalkSupport S.X₂ = stalkSupport S.X₁ ∪ stalkSupport S.X₃ := by
  ext x
  let F := PushforwardInjectiveAcyclic.toAbSheaf X ⋙
    (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
  have h := hS.map_of_exact F
  have : Mono (F.map S.f) := h.mono_f
  have : Epi (F.map S.g) := h.epi_g
  change ¬ IsZero (F.obj S.X₂) ↔ ¬ IsZero (F.obj S.X₁) ∨ ¬ IsZero (F.obj S.X₃)
  constructor
  · intro h₂
    by_contra hn
    push Not at hn
    exact h₂ (h.exact.isZero_of_both_isZero hn.1 hn.2)
  · rintro (h₁ | h₃) h₂
    · exact h₁ (IsZero.of_mono (F.map S.f) h₂)
    · exact h₃ (IsZero.of_epi (F.map S.g) h₂)

/-- Closed stalk supports also form a union in a short exact sequence. -/
theorem closedStalkSupport_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    closedStalkSupport S.X₂ = closedStalkSupport S.X₁ ⊔ closedStalkSupport S.X₃ := by
  apply Closeds.ext
  simp only [coe_closedStalkSupport, stalkSupport_shortExact S hS,
    closure_union, Closeds.coe_sup]

end Langlands.AlgebraicGeometry.Modules
