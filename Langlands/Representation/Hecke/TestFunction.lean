import Langlands.HarmonicAnalysis.Basic
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.ContinuousMap.CompactlySupported

/-! # Actual Hecke test functions and subgroup invariance -/

noncomputable section

namespace Langlands.Hecke

universe u v

open HarmonicAnalysis (SchwartzBruhat)

namespace TestFunction

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

@[ext] theorem ext {f g : SchwartzBruhat X} (h : ∀ x, f x = g x) : f = g :=
  Subtype.ext (funext h)

/-- The faithful inclusion into compactly supported continuous functions. -/
def toCompactlySupported (f : SchwartzBruhat X) : CompactlySupportedContinuousMap X ℂ where
  toFun := f
  continuous_toFun := f.continuous
  hasCompactSupport' := f.hasCompactSupport

@[simp] theorem toCompactlySupported_apply (f : SchwartzBruhat X) (x : X) :
    toCompactlySupported f x = f x := rfl

theorem isClopen_support (f : SchwartzBruhat X) : IsClopen (Function.support f) :=
  (f.locallyConstant.isClopen_fiber 0).compl

theorem tsupport_eq_support (f : SchwartzBruhat X) :
    tsupport (f : X → ℂ) = Function.support f :=
  (isClopen_support f).isClosed.closure_eq

theorem isCompact_support (f : SchwartzBruhat X) : IsCompact (Function.support f) := by
  rw [← tsupport_eq_support f]
  exact f.hasCompactSupport

theorem isCompact_fiber (f : SchwartzBruhat X) {c : ℂ} (hc : c ≠ 0) :
    IsCompact {x | f x = c} :=
  (isCompact_support f).of_isClosed_subset (f.locallyConstant.isClosed_fiber c)
    (fun x hx => by
      change f x ≠ 0
      exact hx ▸ hc)

/-- Pullback along a homeomorphism, with inverse given by pullback along its inverse. -/
def pullback (e : X ≃ₜ Y) : SchwartzBruhat Y ≃ₗ[ℂ] SchwartzBruhat X where
  toFun f := ⟨f ∘ e, f.locallyConstant.comp_continuous e.continuous,
    f.hasCompactSupport.comp_homeomorph e⟩
  invFun f := ⟨f ∘ e.symm, f.locallyConstant.comp_continuous e.symm.continuous,
    f.hasCompactSupport.comp_homeomorph e.symm⟩
  left_inv f := by ext x; exact congrArg f (e.apply_symm_apply x)
  right_inv f := by ext x; exact congrArg f (e.symm_apply_apply x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem pullback_apply (e : X ≃ₜ Y) (f : SchwartzBruhat Y) (x : X) :
    pullback e f x = f (e x) := rfl

/-- The actual characteristic function of a compact clopen set. -/
def characteristic {s : Set X} (hs : IsClopen s) (hc : IsCompact s) : SchwartzBruhat X :=
  ⟨LocallyConstant.charFn ℂ hs, (LocallyConstant.charFn ℂ hs).isLocallyConstant,
    HasCompactSupport.intro' hc hs.isClosed
      (fun x hx => (LocallyConstant.charFn_eq_zero ℂ x hs).mpr hx)⟩

@[simp] theorem characteristic_apply {s : Set X} (hs : IsClopen s) (hc : IsCompact s)
    (x : X) : characteristic hs hc x = s.indicator (fun _ => (1 : ℂ)) x := rfl

theorem support_characteristic {s : Set X} (hs : IsClopen s) (hc : IsCompact s) :
    Function.support (characteristic hs hc : X → ℂ) = s := by
  ext x
  simp only [Function.mem_support]
  exact not_congr (LocallyConstant.charFn_eq_zero ℂ x hs) |>.trans (not_not)

section Group

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Left translation uses `(L_g f)(x) = f(g⁻¹ x)`. -/
def leftTranslate (g : G) : SchwartzBruhat G ≃ₗ[ℂ] SchwartzBruhat G :=
  pullback (Homeomorph.mulLeft g⁻¹)

/-- Right translation uses `(R_g f)(x) = f(x g)`. -/
def rightTranslate (g : G) : SchwartzBruhat G ≃ₗ[ℂ] SchwartzBruhat G :=
  pullback (Homeomorph.mulRight g)

@[simp] theorem leftTranslate_apply (g : G) (f : SchwartzBruhat G) (x : G) :
    leftTranslate g f x = f (g⁻¹ * x) := rfl

@[simp] theorem rightTranslate_apply (g : G) (f : SchwartzBruhat G) (x : G) :
    rightTranslate g f x = f (x * g) := rfl

@[simp] theorem leftTranslate_one (f : SchwartzBruhat G) : leftTranslate 1 f = f := by
  ext x; simp

@[simp] theorem rightTranslate_one (f : SchwartzBruhat G) : rightTranslate 1 f = f := by
  ext x; simp

theorem leftTranslate_mul (g h : G) (f : SchwartzBruhat G) :
    leftTranslate (g * h) f = leftTranslate g (leftTranslate h f) := by
  ext x; simp [mul_assoc]

theorem rightTranslate_mul (g h : G) (f : SchwartzBruhat G) :
    rightTranslate (g * h) f = rightTranslate g (rightTranslate h f) := by
  ext x; simp [mul_assoc]

theorem leftTranslate_rightTranslate (g h : G) (f : SchwartzBruhat G) :
    leftTranslate g (rightTranslate h f) = rightTranslate h (leftTranslate g f) := by
  ext x; simp [mul_assoc]

/-- Inversion on actual test functions; this has no Haar modular factor. -/
def inversion : SchwartzBruhat G ≃ₗ[ℂ] SchwartzBruhat G :=
  pullback (Homeomorph.inv G)

@[simp] theorem inversion_apply (f : SchwartzBruhat G) (x : G) :
    inversion f x = f x⁻¹ := rfl

@[simp] theorem inversion_inversion (f : SchwartzBruhat G) : inversion (inversion f) = f := by
  ext x; simp

/-- The vector subspace of actual functions invariant under both indicated subgroups. -/
def biInvariant (K L : Subgroup G) : Submodule ℂ (SchwartzBruhat G) where
  carrier := {f | (∀ k : K, ∀ x, f ((k : G) * x) = f x) ∧
    (∀ l : L, ∀ x, f (x * (l : G)) = f x)}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => rfl⟩
  add_mem' {f g} hf hg := ⟨fun k x => by
    change f ((k : G) * x) + g ((k : G) * x) = f x + g x
    rw [hf.1, hg.1], fun l x => by
    change f (x * (l : G)) + g (x * (l : G)) = f x + g x
    rw [hf.2, hg.2]⟩
  smul_mem' c f hf := ⟨fun k x => by
    change c • f ((k : G) * x) = c • f x
    rw [hf.1], fun l x => by
    change c • f (x * (l : G)) = c • f x
    rw [hf.2]⟩

theorem mem_biInvariant_iff (K L : Subgroup G) (f : SchwartzBruhat G) :
    f ∈ biInvariant K L ↔
      (∀ k : K, leftTranslate (k : G) f = f) ∧
      (∀ l : L, rightTranslate (l : G) f = f) := by
  constructor
  · intro hf
    exact ⟨fun k => ext (hf.1 k⁻¹), fun l => ext (hf.2 l)⟩
  · rintro ⟨hl, hr⟩
    exact ⟨fun k x => by simpa using congrArg (fun f : SchwartzBruhat G => f x) (hl k⁻¹),
      fun l x => congrArg (fun f : SchwartzBruhat G => f x) (hr l)⟩

omit [IsTopologicalGroup G] in
theorem biInvariant_antitone {K K' L L' : Subgroup G}
    (hK : K' ≤ K) (hL : L' ≤ L) : biInvariant K L ≤ biInvariant K' L' := by
  intro f hf
  exact ⟨fun k => hf.1 ⟨k, hK k.property⟩, fun l => hf.2 ⟨l, hL l.property⟩⟩

theorem inversion_mem_biInvariant {K L : Subgroup G} {f : SchwartzBruhat G}
    (hf : f ∈ biInvariant K L) : inversion f ∈ biInvariant L K := by
  constructor
  · intro l x
    simpa using hf.2 l⁻¹ x⁻¹
  · intro k x
    simpa using hf.1 k⁻¹ x⁻¹

/-- The unnormalized compact-open subgroup indicator. -/
def subgroupIndicator (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    SchwartzBruhat G :=
  characteristic K.isClopen hK

@[simp] theorem subgroupIndicator_apply (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (x : G) : subgroupIndicator K hK x = (K : Set G).indicator (fun _ => (1 : ℂ)) x := rfl

theorem subgroupIndicator_mem (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    subgroupIndicator K hK ∈ biInvariant K.toSubgroup K.toSubgroup := by
  classical
  constructor
  · intro k x
    simp only [subgroupIndicator_apply, Set.indicator_apply]
    congr 1
    exact propext (K.toSubgroup.mul_mem_cancel_left k.property)
  · intro k x
    simp only [subgroupIndicator_apply, Set.indicator_apply]
    congr 1
    exact propext (K.toSubgroup.mul_mem_cancel_right k.property)

end Group

end TestFunction

end Langlands.Hecke
