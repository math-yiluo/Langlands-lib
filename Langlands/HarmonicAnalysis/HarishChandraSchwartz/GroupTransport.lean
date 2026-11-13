import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Harish-Chandra Schwartz spaces under topological group isomorphisms

Precomposition along a topological group isomorphism matching the two weights preserves
all Schwartz seminorms, carries compact-open levels to their preimage levels, and defines a
continuous complex-linear equivalence of the locally convex inductive limits.
-/

noncomputable section

namespace Langlands.HarishChandraSchwartz

universe uG uH

section Seminorms

variable {G : Type uG} {H : Type uH}
  {ΞG σG : G → ℝ} {ΞH σH : H → ℝ}

/-- Reindexing the defining supremum preserves every Schwartz seminorm when the weights
correspond under the same equivalence. -/
theorem nu_comp_equiv (e : H ≃ G)
    (hΞ : ∀ h, ΞH h = ΞG (e h)) (hσ : ∀ h, σH h = σG (e h))
    (r : ℝ) (f : G → ℂ) :
    nu ΞH σH r (f ∘ e) = nu ΞG σG r f := by
  simpa only [nu, weight, Function.comp_apply, hΞ, hσ] using
    (e.iSup_comp (g := fun g : G => ‖f g‖ₑ * weight ΞG σG r g))

end Seminorms

section Groups

variable {G : Type uG} [Group G] {H : Type uH} [Group H]

/-- Precomposition carries bi-invariance to the preimage subgroup. -/
theorem IsBiInvariant.comp_monoidHom {K : Subgroup G} {f : G → ℂ}
    (hf : IsBiInvariant K f) (e : H →* G) :
    IsBiInvariant (K.comap e) (f ∘ e) := by
  intro a ha b hb g
  simpa only [Function.comp_apply, map_mul] using hf (e a) ha (e b) hb (e g)

variable [TopologicalSpace G] [TopologicalSpace H]

/-- The compact open preimage of a compact open subgroup under a topological group
isomorphism. -/
def CompactOpenSubgroup.comap (K : CompactOpenSubgroup G) (e : H ≃ₜ* G) :
    CompactOpenSubgroup H :=
  ⟨K.1.comap e.toMonoidHom e.continuous,
    e.toHomeomorph.isCompact_preimage.mpr K.2⟩

@[simp] theorem CompactOpenSubgroup.comap_toSubgroup
    (K : CompactOpenSubgroup G) (e : H ≃ₜ* G) :
    (K.comap e).toSubgroup = K.toSubgroup.comap e.toMonoidHom := rfl

@[simp] theorem CompactOpenSubgroup.mem_comap
    (K : CompactOpenSubgroup G) (e : H ≃ₜ* G) (h : H) :
    h ∈ (K.comap e).toSubgroup ↔ e h ∈ K.toSubgroup := Iff.rfl

variable {ΞG σG : G → ℝ} {ΞH σH : H → ℝ}
  (e : H ≃ₜ* G) (hΞ : ∀ h, ΞH h = ΞG (e h)) (hσ : ∀ h, σH h = σG (e h))

/-- Precomposition between corresponding compact-open Schwartz levels. -/
def Level.comapLinear (K : CompactOpenSubgroup G) :
    Level ΞG σG K →ₗ[ℂ] Level ΞH σH (K.comap e) where
  toFun f := ⟨f ∘ e, (f.isBiInvariant.comp_monoidHom e.toMonoidHom),
    fun r => by
      exact (nu_comp_equiv e.toEquiv hΞ hσ r f).trans_lt (f.nu_lt_top r)⟩
  map_add' _ _ := Level.ext fun _ => rfl
  map_smul' _ _ := Level.ext fun _ => rfl

@[simp] theorem Level.comapLinear_apply (K : CompactOpenSubgroup G)
    (f : Level ΞG σG K) (h : H) :
    comapLinear e hΞ hσ K f h = f (e h) := rfl

/-- Every seminorm has exactly the same value after precomposition. -/
@[simp] theorem Level.seminorm_comapLinear (K : CompactOpenSubgroup G)
    (r : ℝ) (f : Level ΞG σG K) :
    seminorm (K.comap e) r (comapLinear e hΞ hσ K f) = seminorm K r f := by
  exact congrArg ENNReal.toReal (nu_comp_equiv e.toEquiv hΞ hσ r f)

/-- Precomposition is continuous on every compact-open Schwartz level. -/
def Level.comap (K : CompactOpenSubgroup G) :
    Level ΞG σG K →L[ℂ] Level ΞH σH (K.comap e) where
  toLinearMap := comapLinear e hΞ hσ K
  cont := by
    refine WithSeminorms.continuous_of_continuous_comp (withSeminorms (K.comap e))
      (comapLinear e hΞ hσ K) fun r => ?_
    have heq : (seminormFamily (Ξ := ΞH) (σ := σH) (K.comap e) r).comp
        (comapLinear e hΞ hσ K) = seminorm K r := by
      ext f
      exact seminorm_comapLinear e hΞ hσ K r f
    rw [heq]
    exact continuous_seminorm K r

@[simp] theorem Level.comap_apply (K : CompactOpenSubgroup G)
    (f : Level ΞG σG K) (h : H) :
    comap e hΞ hσ K f h = f (e h) := rfl

/-- The complex-linear pullback of Harish-Chandra Schwartz functions. -/
def Space.comapLinear : Space ΞG σG →ₗ[ℂ] Space ΞH σH := by
  let T : (G → ℂ) →ₗ[ℂ] (H → ℂ) :=
    { toFun := fun f => f ∘ e
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hT : schwartzSubmodule ΞG σG ≤ (schwartzSubmodule ΞH σH).comap T := by
    refine iSup_le fun K => ?_
    intro f hf
    exact levelSubmodule_le_schwartzSubmodule ΞH σH (K.comap e)
      ⟨hf.1.comp_monoidHom e.toMonoidHom, fun r =>
        (nu_comp_equiv e.toEquiv hΞ hσ r f).trans_lt (hf.2 r)⟩
  exact
    { toFun := fun f => ⟨T f, hT f.coe_mem⟩
      map_add' := fun _ _ => Space.ext fun _ => rfl
      map_smul' := fun _ _ => Space.ext fun _ => rfl }

@[simp] theorem Space.comapLinear_apply (f : Space ΞG σG) (h : H) :
    comapLinear e hΞ hσ f h = f (e h) := rfl

/-- Pullback is continuous for the locally convex inductive-limit topology, by its
continuous restrictions to the compact-open levels. -/
def Space.comap : Space ΞG σG →L[ℂ] Space ΞH σH :=
  mkCLM (comapLinear e hΞ hσ) fun K => by
    have heq : comapLinear e hΞ hσ ∘ ofLevel K =
        ofLevelCLM (K.comap e) ∘ Level.comap e hΞ hσ K := rfl
    rw [heq]
    exact (ofLevelCLM (K.comap e)).continuous.comp (Level.comap e hΞ hσ K).continuous

@[simp] theorem Space.comap_apply (f : Space ΞG σG) (h : H) :
    comap e hΞ hσ f h = f (e h) := rfl

/-- A topological group isomorphism matching the weights induces a continuous
complex-linear equivalence of the Harish-Chandra Schwartz spaces. -/
def Space.comapEquiv : Space ΞG σG ≃L[ℂ] Space ΞH σH where
  toLinearEquiv :=
    { toLinearMap := (comap e hΞ hσ).toLinearMap
      invFun := comap e.symm
        (fun g => by simpa only [e.apply_symm_apply] using (hΞ (e.symm g)).symm)
        (fun g => by simpa only [e.apply_symm_apply] using (hσ (e.symm g)).symm)
      left_inv f := Space.ext fun g => by simp
      right_inv f := Space.ext fun h => by simp }
  continuous_toFun := (comap e hΞ hσ).continuous
  continuous_invFun := (comap e.symm
    (fun g => by simpa only [e.apply_symm_apply] using (hΞ (e.symm g)).symm)
    (fun g => by simpa only [e.apply_symm_apply] using (hσ (e.symm g)).symm)).continuous

@[simp] theorem Space.comapEquiv_apply (f : Space ΞG σG) (h : H) :
    comapEquiv e hΞ hσ f h = f (e h) := rfl

@[simp] theorem Space.comapEquiv_symm_apply (f : Space ΞH σH) (g : G) :
    (comapEquiv e hΞ hσ).symm f g = f (e.symm g) := rfl

/-- All the defining extended-real seminorms are preserved on the full Schwartz space. -/
theorem Space.nu_comapEquiv (r : ℝ) (f : Space ΞG σG) :
    nu ΞH σH r (comapEquiv e hΞ hσ f) = nu ΞG σG r f :=
  nu_comp_equiv e.toEquiv hΞ hσ r f

end Groups

end Langlands.HarishChandraSchwartz
