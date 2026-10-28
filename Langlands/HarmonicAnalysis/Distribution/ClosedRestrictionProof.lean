import Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionStatement
import Langlands.HarmonicAnalysis.AlgebraicIntegrand
import Langlands.HarmonicAnalysis.RowTensorDecompositionProof
import Langlands.Representation.Hecke.TestFunction
import Mathlib.Topology.Separation.Profinite

/-!
# Surjectivity of restriction to a closed subset

Lift each compact-open nonzero fiber of a test function to a compact-open
ambient set and sum its weighted indicator. The lifts can overlap away from
the subset.
-/

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

open Hecke.TestFunction

universe u

variable {X : Type u} [TopologicalSpace X] [T2Space X]
  [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

private theorem exists_compact_clopen_between {K V : Set X}
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ U : Set X, IsCompact U ∧ IsClopen U ∧ K ⊆ U ∧ U ⊆ V := by
  choose U hUc hUo hxU hUV using
    fun x : V => Langlands.HarmonicAnalysis.exists_compact_clopen (hV.mem_nhds x.property)
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover U (fun x => (hUo x).isOpen)
    (fun x hx => Set.mem_iUnion.mpr ⟨⟨x, hKV hx⟩, hxU _⟩)
  refine ⟨⋃ x ∈ s, U x, s.isCompact_biUnion (fun x _ => hUc x),
    s.finite_toSet.isClopen_biUnion (fun x _ => hUo x), hs, ?_⟩
  exact Set.iUnion₂_subset fun x _ => hUV x

private theorem exists_compact_clopen_trace {Z : Set X} {K : Set Z}
    (hKc : IsCompact K) (hKo : IsOpen K) :
    ∃ U : Set X, IsCompact U ∧ IsClopen U ∧ Subtype.val ⁻¹' U = K := by
  obtain ⟨V, hV, hVK⟩ := isOpen_induced_iff.mp hKo
  have hKV : Subtype.val '' K ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    change z ∈ Subtype.val ⁻¹' V
    rwa [hVK]
  obtain ⟨U, hUc, hUo, hKU, hUV⟩ :=
    exists_compact_clopen_between (hKc.image continuous_subtype_val) hV hKV
  refine ⟨U, hUc, hUo, ?_⟩
  apply Set.Subset.antisymm
  · intro z hz
    rw [← hVK]
    exact hUV hz
  · intro z hz
    exact hKU ⟨z, hz, rfl⟩

/-- Every Schwartz–Bruhat function on a closed subset extends to an ambient
Schwartz–Bruhat function, in every universe and without nonemptiness assumptions. -/
theorem closedRestrictionSurjective : ClosedRestrictionSurjectiveStatement.{u} := by
  classical
  intro X _ _ _ _ Z hZ f
  let S : Set ℂ := {c | c ∈ Set.range f ∧ c ≠ 0}
  have hS : S.Finite :=
    (finite_range_of_locallyConstant_of_hasCompactSupport
      f.locallyConstant f.hasCompactSupport).subset (fun _ hc => hc.1)
  let : Fintype S := hS.fintype
  have hlift (c : S) : ∃ U : Set X, IsCompact U ∧ IsClopen U ∧
      Subtype.val ⁻¹' U = {z : Z | f z = c.val} :=
    exists_compact_clopen_trace (isCompact_fiber f c.property.2)
      (f.locallyConstant.isOpen_fiber c.val)
  choose U hUc hUo hU using hlift
  let φ : S → SchwartzBruhat X := fun c => characteristic (hUo c) (hUc c)
  refine ⟨∑ c : S, c.val • φ c, ?_⟩
  apply Hecke.TestFunction.ext
  intro z
  rw [restrictClosed_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  have htrace (c : S) : z.val ∈ U c ↔ f z = c.val := by
    change z ∈ Subtype.val ⁻¹' U c ↔ _
    rw [hU c]
    rfl
  by_cases hz : f z = 0
  · have hne (c : S) : z.val ∉ U c := by
      rw [htrace c, hz]
      exact Ne.symm c.property.2
    simp [φ, characteristic_apply, hne, hz]
  · let c : S := ⟨f z, ⟨⟨z, rfl⟩, hz⟩⟩
    rw [Finset.sum_eq_single c]
    · have hmem : z.val ∈ U c := (htrace c).mpr rfl
      simp [φ, characteristic_apply, Set.indicator_of_mem hmem, c]
    · intro b _ hbc
      have hnot : z.val ∉ U b := by
        intro h
        exact hbc (Subtype.ext ((htrace b).mp h).symm)
      simp [φ, characteristic_apply, Set.indicator_of_notMem hnot]
    · simp

end Langlands.HarmonicAnalysis.SchwartzBruhat
