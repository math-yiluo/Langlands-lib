import Langlands.Representation.CompactSchurAveragingProof
import Langlands.Representation.Category.FiniteIndexRestriction
import Mathlib.Analysis.Convex.Integral
import Mathlib.LinearAlgebra.Projection

/-! # Complete reducibility of finite continuous compact representations -/

noncomputable section
universe uG
set_option autoImplicit false

namespace Langlands.Representation.CompactFinite

open MeasureTheory
open scoped MonoidAlgebra

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable {d : ℕ} (ρ : _root_.Representation ℂ G (Fin d → ℂ))
  (hρ : Continuous (fun p : G × (Fin d → ℂ) => ρ p.1 p.2))
  (ν : Measure G) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant]

include hρ ν

/-- Averaging an algebraic projection gives an equivariant projection onto
any invariant subspace of the actual finite-dimensional continuous source. -/
theorem exists_equivariant_projection (S : Subrepresentation ρ) :
    ∃ P : ρ.IntertwiningMap ρ,
      (∀ v, P v ∈ S) ∧ (∀ v ∈ S, P v = v) := by
  obtain ⟨Q, hQ⟩ := exists_isCompl S.toSubmodule
  let T : Module.End ℂ (Fin d → ℂ) :=
    S.toSubmodule.subtype.comp (S.toSubmodule.projectionOnto Q hQ)
  refine ⟨CompactSchur.averageIntertwiner ρ hρ ν T, ?_, ?_⟩
  · intro v
    change (∫ k : G, ρ k (T (ρ k⁻¹ v)) ∂ν) ∈ S.toSubmodule
    exact (S.toSubmodule.restrictScalars ℝ).convex.integral_mem
      S.toSubmodule.closed_of_finiteDimensional
      (Filter.Eventually.of_forall fun k =>
        S.apply_mem_toSubmodule k (S.toSubmodule.projectionOnto Q hQ (ρ k⁻¹ v)).property)
      (CompactSchur.integrable_conjugate ρ hρ ν T v)
  · intro v hv
    change (∫ k : G, ρ k (T (ρ k⁻¹ v)) ∂ν) = v
    have ht (k : G) : ρ k (T (ρ k⁻¹ v)) = v := by
      have hkv := S.apply_mem_toSubmodule k⁻¹ hv
      change ρ k (S.toSubmodule.projectionOnto Q hQ (ρ k⁻¹ v)) = v
      rw [Submodule.projectionOnto_apply_of_mem_left hQ hkv]
      exact _root_.Representation.self_inv_apply ρ k v
    simp only [ht, integral_const, probReal_univ, one_smul]

/-- A chosen equivariant projection obtained by averaging an algebraic
projection onto the invariant subspace. -/
def equivariantProjection (S : Subrepresentation ρ) : ρ.IntertwiningMap ρ :=
  (exists_equivariant_projection ρ hρ ν S).choose

theorem equivariantProjection_mem (S : Subrepresentation ρ) (v : Fin d → ℂ) :
    equivariantProjection ρ hρ ν S v ∈ S :=
  (exists_equivariant_projection ρ hρ ν S).choose_spec.1 v

theorem equivariantProjection_eq_self (S : Subrepresentation ρ)
    (v : Fin d → ℂ) (hv : v ∈ S) :
    equivariantProjection ρ hρ ν S v = v :=
  (exists_equivariant_projection ρ hρ ν S).choose_spec.2 v hv

/-- Every finite-dimensional continuous complex representation of a compact
 group is algebraically semisimple. -/
theorem isSemisimple : ρ.IsSemisimpleRepresentation := by
  constructor
  intro S
  let P := equivariantProjection ρ hρ ν S
  have hP := equivariantProjection_mem ρ hρ ν S
  have hfix := equivariantProjection_eq_self ρ hρ ν S
  let p : (Fin d → ℂ) →ₗ[ℂ] S.toSubmodule :=
    P.toLinearMap.codRestrict S.toSubmodule hP
  have hp : ∀ v : S.toSubmodule, p v = v := by
    intro v
    apply Subtype.ext
    exact hfix v v.property
  have hcompl : IsCompl S.toSubmodule (LinearMap.ker P.toLinearMap) :=
    by simpa only [p, LinearMap.ker_codRestrict] using LinearMap.isCompl_of_proj hp
  refine ⟨P.ker, ?_, ?_⟩
  · apply disjoint_iff.mpr
    apply Subrepresentation.toSubmodule_injective
    exact hcompl.inf_eq_bot
  · apply codisjoint_iff.mpr
    apply Subrepresentation.toSubmodule_injective
    exact hcompl.sup_eq_top

/-- A finite continuous compact source is covered by finitely many algebraic
irreducible subrepresentations. -/
theorem exists_finite_atoms :
    ∃ (m : ℕ) (S : Fin m → Subrepresentation ρ),
      (∀ i, IsAtom (S i)) ∧ (⨆ i, (S i).toSubmodule) = ⊤ := by
  classical
  have : Module.Finite ℂ ρ.asModule := Module.Finite.equiv ρ.asModuleEquiv.symm
  have hfin : Module.Finite ℂ[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite ℂ ℂ[G] ρ.asModule
  have : IsSemisimpleModule ℂ[G] ρ.asModule :=
    (_root_.Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp
      (isSemisimple ρ hρ ν)
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
  have hc : IsCompactElement (⊤ : Submodule ℂ[G] ρ.asModule) :=
    (Submodule.fg_iff_compact ⊤).mp hfin.fg_top
  let ι := {a : Submodule ℂ[G] ρ.asModule // IsSimpleModule ℂ[G] a}
  obtain ⟨t, ht⟩ := hc.exists_finset_of_le_iSup (fun a : ι => a.val) (by
    rw [← IsSemisimpleModule.sSup_simples_eq_top]
    exact sSup_le fun a ha => le_iSup_of_le (⟨a, ha⟩ : ι) le_rfl)
  let a : Fin t.card → ι := fun i => (t.equivFin.symm i).val
  refine ⟨t.card, fun i => e.symm (a i).val, fun i => ?_, ?_⟩
  · exact (e.symm.isAtom_iff _).mpr (isSimpleModule_iff_isAtom.mp (a i).property)
  · have hsup : (⨆ i, (a i).val) = ⊤ := by
      apply top_unique
      refine ht.trans (iSup₂_le fun b hb => ?_)
      exact le_iSup_of_le (t.equivFin ⟨b, hb⟩) (by simp [a])
    rw [← Langlands.Subrepresentation.toSubmodule_iSup, ← e.symm.map_iSup,
      hsup, e.symm.map_top]
    rfl

end Langlands.Representation.CompactFinite
