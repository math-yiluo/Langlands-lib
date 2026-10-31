import Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityStatement
import Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof

/-! # Local open-restriction criterion for support of algebraic distributions -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open Hecke.TestFunction
open scoped Classical

universe u

namespace OpenRestrictionLocalityProof

variable {X : Type u} [TopologicalSpace X] [T2Space X]

/-- Multiply a test function by the characteristic function of a clopen set. -/
private def cutoff {V : Set X} (hV : IsClopen V) :
    SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat X where
  toFun f := ⟨fun x => LocallyConstant.charFn ℂ hV x * f x,
    (LocallyConstant.charFn ℂ hV).isLocallyConstant.comp₂
      f.locallyConstant (· * ·), f.hasCompactSupport.mul_left⟩
  map_add' f g := by ext x; exact mul_add _ _ _
  map_smul' c f := by ext x; exact mul_left_comm _ _ _

omit [T2Space X] in
private theorem cutoff_apply {V : Set X} (hV : IsClopen V)
    (f : SchwartzBruhat X) (x : X) :
    cutoff hV f x = if x ∈ V then f x else 0 := by
  classical
  change V.indicator (fun _ => (1 : ℂ)) x * f x = _
  by_cases hx : x ∈ V <;> simp [hx]

/-- A distribution with zero restriction to `U` kills every test function
vanishing outside `U`, since such a function is an extension by zero. -/
private theorem kill_of_restrictOpen_zero {U : Set X} (hU : IsOpen U)
    (D : Distribution X) (hD : restrictOpen hU D = 0)
    (f : SchwartzBruhat X) (hf : ∀ x, x ∉ U → f x = 0) :
    D f = 0 := by
  obtain ⟨φ, hφ⟩ := FiniteOrbitVanishingProof.exists_extension_eq
    (SchwartzBruhat.extendZero hU)
    (SchwartzBruhat.extendZero_apply_subtype hU)
    (fun φ x hx => SchwartzBruhat.extendZero_apply_of_not_mem hU φ hx) f hf
  rw [← hφ]
  exact congrArg (fun T : Distribution U => T φ) hD

private theorem kill_cutoff {U V : Set X} (hU : IsOpen U)
    (D : Distribution X) (hD : restrictOpen hU D = 0)
    (hV : IsClopen V) (hVU : V ⊆ U) (f : SchwartzBruhat X) :
    D (cutoff hV f) = 0 := by
  apply kill_of_restrictOpen_zero hU D hD
  intro x hx
  rw [cutoff_apply, ite_eq_right (fun hxV => hx (hVU hxV))]

end OpenRestrictionLocalityProof

open OpenRestrictionLocalityProof in
/-- A finite clopen cover of each test support reduces locality to finite linearity. -/
theorem openRestrictionLocality : OpenRestrictionLocalityStatement.{u} := by
  classical
  intro X _ _ _ _ Z D hlocal f hf
  have hneighborhood (x : Function.support (f : X → ℂ)) :
      ∃ (V : Set X) (hV : IsClopen V),
        x.val ∈ V ∧ ∀ g : SchwartzBruhat X, D (cutoff hV g) = 0 := by
    have hxZ : x.val ∉ Z := fun hx => x.property (hf x.val hx)
    obtain ⟨U, hU, hxU, hDU⟩ := hlocal x.val hxZ
    obtain ⟨V, hV, hxV, hVU⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp (hU.mem_nhds hxU)
    exact ⟨V, hV, hxV, kill_cutoff hU D hDU hV hVU⟩
  choose V hV hxV hkill using hneighborhood
  obtain ⟨s, hs⟩ := (isCompact_support f).elim_finite_subcover V
    (fun x => (hV x).isOpen) (by
      intro x hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩)
  have hcl (t : Finset (Function.support (f : X → ℂ))) :
      IsClopen (⋃ x ∈ t, V x) :=
    isClopen_biUnion_finset (fun x _ => hV x)
  have hzero (t : Finset (Function.support (f : X → ℂ))) :
      D (cutoff (hcl t) f) = 0 := by
    induction t using Finset.induction_on with
    | empty =>
      have heq : cutoff (hcl ∅) f = 0 := by
        ext x
        simp [cutoff_apply]
      rw [heq, map_zero]
    | @insert x t hxt ih =>
      have heq : cutoff (hcl (insert x t)) f =
          cutoff (hV x) f + cutoff (hcl t) f -
            cutoff (hV x) (cutoff (hcl t) f) := by
        ext y
        change cutoff (hcl (insert x t)) f y =
          cutoff (hV x) f y + cutoff (hcl t) f y -
            cutoff (hV x) (cutoff (hcl t) f) y
        by_cases hy : y ∈ V x <;>
          simp [cutoff_apply, hy]
      rw [heq, map_sub, map_add, hkill, ih, hkill, add_zero, sub_self]
  have heq : cutoff (hcl s) f = f := by
    ext x
    rw [cutoff_apply]
    by_cases hx : f x = 0
    · simp [hx]
    · exact ite_eq_left (hs hx)
  rw [← heq]
  exact hzero s

end Langlands.HarmonicAnalysis.Distribution
