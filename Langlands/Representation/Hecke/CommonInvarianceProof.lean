import Langlands.Representation.Hecke.CommonInvarianceStatement
import Mathlib.Topology.Separation.Profinite

open Topology Filter Set

universe u

namespace Langlands.Hecke.TestFunction

open Langlands.HarmonicAnalysis (SchwartzBruhat)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def leftStabilizer (f : SchwartzBruhat G) : Subgroup G where
  carrier := {g | ∀ x, f (g * x) = f x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro g h hg hh x
    rw [mul_assoc, hg, hh]
  inv_mem' := by
    intro g hg x
    simpa using (hg (g⁻¹ * x)).symm

private theorem left_invariant_near_one (f : SchwartzBruhat G) :
    ∀ᶠ g in 𝓝 (1 : G), ∀ x, f (g * x) = f x := by
  have h : ∀ᶠ g in 𝓝 (1 : G), ∀ x ∈ Function.support f, f (g * x) = f x := by
    apply (isCompact_support f).eventually_forall_of_forall_eventually
    intro x _
    have hm := (f.locallyConstant.comp_continuous
      (continuous_fst.mul continuous_snd)).eventually_eq (1, x)
    have hx := (f.locallyConstant.comp_continuous continuous_snd).eventually_eq ((1 : G), x)
    filter_upwards [hm, hx] with p hp hpx
    simp only [Function.comp_apply, Pi.mul_apply, one_mul] at hp hpx
    exact hp.trans hpx.symm
  have hi : ∀ᶠ g in 𝓝 (1 : G), ∀ x ∈ Function.support f, f (g⁻¹ * x) = f x := by
    exact (continuous_inv.tendsto (1 : G)).eventually (by simpa using h)
  filter_upwards [h, hi] with g hg hgi
  intro x
  by_cases hx : x ∈ Function.support f
  · exact hg x hx
  · by_cases hy : g * x ∈ Function.support f
    · simpa using (hgi (g * x) hy).symm
    · simp only [Function.mem_support, not_not] at hx hy
      exact hy.trans hx.symm

private def leftOpenStabilizer (f : SchwartzBruhat G) : OpenSubgroup G :=
  ⟨leftStabilizer f, (leftStabilizer f).isOpen_of_mem_nhds (left_invariant_near_one f)⟩

private def biOpenStabilizer (f : SchwartzBruhat G) : OpenSubgroup G :=
  leftOpenStabilizer f ⊓ leftOpenStabilizer (inversion f)

private theorem mem_biOpenStabilizer (f : SchwartzBruhat G) :
    f ∈ biInvariant (biOpenStabilizer f).toSubgroup (biOpenStabilizer f).toSubgroup := by
  constructor
  · intro g x
    exact g.property.1 x
  · intro g x
    have h := (show ∀ y, inversion f ((g : G)⁻¹ * y) = inversion f y from
      ((biOpenStabilizer f).inv_mem g.property).2) x⁻¹
    simpa using h

private theorem exists_compactOpen_inside [T2Space G] [LocallyCompactSpace G]
    [TotallyDisconnectedSpace G] (U : OpenSubgroup G) :
    ∃ K : OpenSubgroup G, K ≤ U ∧ IsCompact (K : Set G) := by
  classical
  obtain ⟨C, hCc, hCn⟩ := exists_compact_mem_nhds (1 : G)
  obtain ⟨V, hVcl, hV1, hVsub⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp
      (inter_mem U.mem_nhds_one hCn)
  have hVc : IsCompact V := hCc.of_isClosed_subset hVcl.isClosed
    (fun x hx => (hVsub hx).2)
  let f : SchwartzBruhat G := characteristic hVcl hVc
  let K := leftOpenStabilizer f
  have hKV : (K : Set G) ⊆ V := by
    intro g hg
    have hfg : f g = f 1 := by simpa using hg 1
    have hf1 : f 1 = 1 := by simp [f, characteristic_apply, hV1]
    by_contra hgv
    have hfg0 : f g = 0 := by simp [f, characteristic_apply, hgv]
    exact zero_ne_one (hfg0.symm.trans (hfg.trans hf1))
  exact ⟨K, fun x hx => (hVsub (hKV hx)).1,
    hVc.of_isClosed_subset K.isClosed hKV⟩

/-- Finite families of actual test functions have common compact-open bi-invariance,
with refinement inside any prescribed open subgroup. -/
theorem commonCompactOpenBiInvariance : CommonCompactOpenBiInvarianceStatement.{u} := by
  classical
  intro G _ _ _ _ _ _ s
  induction s using Finset.induction_on with
  | empty =>
    intro U
    obtain ⟨K, hKU, hKc⟩ := exists_compactOpen_inside U
    exact ⟨K, hKU, hKc, by simp⟩
  | @insert f s hf ih =>
    intro U
    obtain ⟨K, hKU, hKc, hKs⟩ := ih U
    let L := K ⊓ biOpenStabilizer f
    refine ⟨L, inf_le_left.trans hKU,
      hKc.of_isClosed_subset L.isClosed inf_le_left, ?_⟩
    intro g hg
    rcases Finset.mem_insert.mp hg with hgf | hg
    · subst g
      exact biInvariant_antitone
        (show L.toSubgroup ≤ (biOpenStabilizer f).toSubgroup from inf_le_right)
        (show L.toSubgroup ≤ (biOpenStabilizer f).toSubgroup from inf_le_right)
        (mem_biOpenStabilizer f)
    · exact biInvariant_antitone
        (show L.toSubgroup ≤ K.toSubgroup from inf_le_left)
        (show L.toSubgroup ≤ K.toSubgroup from inf_le_left) (hKs g hg)

end Langlands.Hecke.TestFunction
