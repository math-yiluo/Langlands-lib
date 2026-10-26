import Langlands.HarmonicAnalysis.Distribution.LocalizationStatement
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Localization of equivariant algebraic distributions -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open Hecke.TestFunction
open scoped Classical

universe uX uY uI

variable {X : Type uX} {Y : Type uY} [TopologicalSpace X] [TopologicalSpace Y]

/-- Cut a test function by the inverse image of a clopen subset of the base. -/
private def cutoff (q : X → Y) (hq : Continuous q) {V : Set Y} (hV : IsClopen V) :
    SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X where
  toFun f := ⟨fun x => LocallyConstant.charFn ℂ hV (q x) * f x,
    ((LocallyConstant.charFn ℂ hV).isLocallyConstant.comp_continuous hq).comp₂
      f.locallyConstant (· * ·), f.hasCompactSupport.mul_left⟩
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' c f := by ext x; exact mul_left_comm _ _ _

private theorem cutoff_apply (q : X → Y) (hq : Continuous q) {V : Set Y}
    (hV : IsClopen V) (f : SchwartzBruhat X) (x : X) :
    cutoff q hq hV f x = if q x ∈ V then f x else 0 := by
  classical
  change V.indicator (fun _ => (1 : ℂ)) (q x) * f x = _
  by_cases hx : q x ∈ V <;> simp [hx]

private theorem cutoff_union_mem (q : X → Y) (hq : Continuous q)
    (N : Submodule ℂ (SchwartzBruhat X))
    (hN : ∀ (V : Set Y) (hV : IsClopen V) (f : SchwartzBruhat X),
      f ∈ N → cutoff q hq hV f ∈ N)
    {U V : Set Y} (hU : IsClopen U) (hV : IsClopen V) (f : SchwartzBruhat X)
    (hfU : cutoff q hq hU f ∈ N) (hfV : cutoff q hq hV f ∈ N) :
    cutoff q hq (hU.union hV) f ∈ N := by
  have heq : cutoff q hq (hU.union hV) f =
      cutoff q hq hU f + cutoff q hq hV f - cutoff q hq hU (cutoff q hq hV f) := by
    ext x
    change cutoff q hq (hU.union hV) f x =
      cutoff q hq hU f x + cutoff q hq hV f x - cutoff q hq hU (cutoff q hq hV f) x
    by_cases hxU : q x ∈ U <;> by_cases hxV : q x ∈ V <;>
      simp [cutoff_apply, hxU, hxV]
  rw [heq]
  exact N.sub_mem (N.add_mem hfU hfV) (hN U hU _ hfV)

/-- Membership in a cutoff-stable subspace can be checked near every point of the base. -/
private theorem mem_of_local_cutoffs (q : X → Y) (hq : Continuous q)
    (N : Submodule ℂ (SchwartzBruhat X))
    (hN : ∀ (V : Set Y) (hV : IsClopen V) (f : SchwartzBruhat X),
      f ∈ N → cutoff q hq hV f ∈ N)
    (f : SchwartzBruhat X)
    (hloc : ∀ y : Y, ∃ (V : Set Y) (hV : IsClopen V),
      y ∈ V ∧ cutoff q hq hV f ∈ N) : f ∈ N := by
  classical
  choose V hV hyV hfV using hloc
  obtain ⟨s, hs⟩ := ((isCompact_support f).image hq).elim_finite_subcover V
    (fun y => (hV y).isOpen) (by intro y _; exact Set.mem_iUnion.mpr ⟨y, hyV y⟩)
  have hcl (t : Finset Y) : IsClopen (⋃ y ∈ t, V y) :=
    isClopen_biUnion_finset (fun y _ => hV y)
  have hmem (t : Finset Y) : cutoff q hq (hcl t) f ∈ N := by
    induction t using Finset.induction_on with
    | empty =>
      have heq : cutoff q hq (hcl ∅) f = 0 := by
        ext x
        simp [cutoff_apply]
      rw [heq]
      exact N.zero_mem
    | @insert y t hyt ih =>
      have heq : cutoff q hq (hcl (insert y t)) f =
          cutoff q hq ((hV y).union (hcl t)) f := by
        ext x
        simp [cutoff_apply]
      rw [heq]
      exact cutoff_union_mem q hq N hN (hV y) (hcl t) f (hfV y) ih
  have heq : cutoff q hq (hcl s) f = f := by
    ext x
    rw [cutoff_apply]
    by_cases hx : f x = 0
    · simp [hx]
    · exact ite_eq_left (hs ⟨x, hx, rfl⟩)
  rw [← heq]
  exact hmem s

/-- Localization along an invariant continuous map, with the exact published telescope. -/
theorem equivariantLocalization : EquivariantLocalizationStatement.{uX, uY, uI} := by
  classical
  intro X _ Y _ _ _ _ q hq ι h χ hinv hfibre D hD
  let relations : Set (SchwartzBruhat X) :=
    {f | ∃ (i : ι) (g : SchwartzBruhat X), f = pullback (h i) g - χ i • g}
  let N : Submodule ℂ (SchwartzBruhat X) := Submodule.span ℂ relations
  have hgen (i : ι) (g : SchwartzBruhat X) : pullback (h i) g - χ i • g ∈ N :=
    Submodule.subset_span ⟨i, g, rfl⟩
  have hstable (V : Set Y) (hV : IsClopen V) (f : SchwartzBruhat X)
      (hf : f ∈ N) : cutoff q hq hV f ∈ N := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨i, g, rfl⟩ := hf
      have heq : cutoff q hq hV (pullback (h i) g - χ i • g) =
          pullback (h i) (cutoff q hq hV g) - χ i • cutoff q hq hV g := by
        ext x
        change cutoff q hq hV (pullback (h i) g - χ i • g) x =
          cutoff q hq hV g (h i x) - χ i * cutoff q hq hV g x
        rw [cutoff_apply, cutoff_apply, cutoff_apply, hinv]
        by_cases hx : q x ∈ V <;> simp [hx, pullback_apply]
      rw [heq]
      exact hgen i _
    | zero => simp
    | add f g hf hg ihf ihg => simpa only [map_add] using N.add_mem ihf ihg
    | smul c f hf ih => simpa only [map_smul] using N.smul_mem c ih
  have hlocal (f : SchwartzBruhat X) (y : Y) :
      ∃ (V : Set Y) (hV : IsClopen V), y ∈ V ∧ cutoff q hq hV f ∈ N := by
    let I : Submodule ℂ (SchwartzBruhat X) :=
      { carrier := {g | ∀ x, q x = y → g x = 0}
        zero_mem' := by intro x hx; rfl
        add_mem' := by intro g k hg hk x hx; change g x + k x = 0; rw [hg x hx, hk x hx, add_zero]
        smul_mem' := by intro c g hg x hx; change c * g x = 0; rw [hg x hx, mul_zero] }
    have hfull : f ∈ N ⊔ I := by
      by_contra hf
      obtain ⟨T, hTf, hT⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hf inferInstance
      have hkill (g : SchwartzBruhat X) (hg : g ∈ N ⊔ I) : T g = 0 := by
        have : T g ∈ (N ⊔ I).map T := Submodule.mem_map_of_mem hg
        rwa [hT, Submodule.mem_bot] at this
      have hzero : T = 0 := hfibre y T
        (fun g hg => hkill g (Submodule.mem_sup_right hg)) (by
          intro i
          ext g
          change T (pullback (h i) g) = χ i * T g
          have hz := hkill _ (Submodule.mem_sup_left (hgen i g))
          simpa only [map_sub, map_smul, smul_eq_mul, sub_eq_zero] using hz)
      exact hTf (by rw [hzero]; rfl)
    obtain ⟨n, hn, e, he, hne⟩ := Submodule.mem_sup.mp hfull
    have hy : y ∈ (q '' Function.support e)ᶜ := by
      rintro ⟨x, hx, hxy⟩
      exact hx (he x hxy)
    obtain ⟨V, hV, hyV, hsub⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp
        (((isCompact_support e).image hq).isClosed.isOpen_compl.mem_nhds hy)
    have hezero : cutoff q hq hV e = 0 := by
      ext x
      rw [cutoff_apply]
      by_cases hx : q x ∈ V
      · simp only [hx, ite_true]
        by_contra hex
        exact hsub hx ⟨x, hex, rfl⟩
      · simp [hx]
    refine ⟨V, hV, hyV, ?_⟩
    rw [← hne, map_add, hezero, add_zero]
    exact hstable V hV n hn
  have hkill : N ≤ LinearMap.ker D := by
    apply Submodule.span_le.mpr
    rintro f ⟨i, g, rfl⟩
    change D (pullback (h i) g - χ i • g) = 0
    have hi := congrArg (fun T : Distribution X => T g) (hD i)
    change D (pullback (h i) g) = χ i * D g at hi
    simp only [map_sub, map_smul, smul_eq_mul, hi, sub_self]
  ext f
  exact hkill (mem_of_local_cutoffs q hq N hstable f (hlocal f))

end Langlands.HarmonicAnalysis.Distribution
