import Langlands.HarmonicAnalysis.Distribution.Basic

/-! # Subspace maps on test functions and algebraic distributions -/

noncomputable section

namespace Langlands.HarmonicAnalysis

universe u

variable {X : Type u} [TopologicalSpace X]

namespace SchwartzBruhat

/-- Restriction to a closed subspace, with its induced topology. -/
def restrictClosed {Z : Set X} (hZ : IsClosed Z) :
    SchwartzBruhat X →ₗ[ℂ] SchwartzBruhat Z where
  toFun f := ⟨(f : X → ℂ) ∘ Subtype.val,
    f.locallyConstant.comp_continuous continuous_subtype_val,
    f.hasCompactSupport.comp_isClosedEmbedding hZ.isClosedEmbedding_subtypeVal⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem restrictClosed_apply {Z : Set X} (hZ : IsClosed Z)
    (f : SchwartzBruhat X) (z : Z) :
    restrictClosed hZ f z = f z.val := rfl

section Open

variable [T2Space X] {U : Set X}

/-- Compact support makes zero extension locally constant even at the boundary.
Continuity into the discrete codomain is equivalent to local constancy. -/
theorem locallyConstant_extendZero (hU : IsOpen U) (f : SchwartzBruhat U) :
    IsLocallyConstant (Subtype.val.extend (f : U → ℂ) 0) := by
  let : TopologicalSpace ℂ := ⊥
  let : DiscreteTopology ℂ := ⟨rfl⟩
  exact (IsLocallyConstant.iff_continuous _).mpr
    (HasCompactSupport.continuous_extend_zero hU
      f.locallyConstant.continuous f.hasCompactSupport)

/-- Extension by zero from an open subspace; the subset need not be closed. -/
def extendZero (hU : IsOpen U) : SchwartzBruhat U →ₗ[ℂ] SchwartzBruhat X where
  toFun f := ⟨Subtype.val.extend (f : U → ℂ) 0,
    locallyConstant_extendZero hU f,
    f.hasCompactSupport.extend_zero continuous_subtype_val⟩
  map_add' f g := by
    ext x
    by_cases hx : x ∈ U
    · obtain ⟨x, rfl⟩ := (show ∃ z : U, z.val = x from ⟨⟨x, hx⟩, rfl⟩)
      simp only [Submodule.coe_add, Pi.add_apply, Function.Injective.extend_apply
        Subtype.val_injective]
    · have hn : ¬ ∃ z : U, z.val = x := by
        rintro ⟨z, rfl⟩
        exact hx z.property
      simp [Function.extend_apply', hn]
  map_smul' c f := by
    ext x
    by_cases hx : x ∈ U
    · obtain ⟨x, rfl⟩ := (show ∃ z : U, z.val = x from ⟨⟨x, hx⟩, rfl⟩)
      simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply,
        Function.Injective.extend_apply Subtype.val_injective]
    · have hn : ¬ ∃ z : U, z.val = x := by
        rintro ⟨z, rfl⟩
        exact hx z.property
      simp [Function.extend_apply', hn]

@[simp]
theorem extendZero_apply_subtype (hU : IsOpen U) (f : SchwartzBruhat U) (u : U) :
    extendZero hU f u.val = f u :=
  Subtype.val_injective.extend_apply _ _ _

theorem extendZero_apply_of_mem (hU : IsOpen U) (f : SchwartzBruhat U)
    {x : X} (hx : x ∈ U) :
    extendZero hU f x = f ⟨x, hx⟩ :=
  extendZero_apply_subtype hU f ⟨x, hx⟩

@[simp]
theorem extendZero_apply_of_not_mem (hU : IsOpen U) (f : SchwartzBruhat U)
    {x : X} (hx : x ∉ U) :
    extendZero hU f x = 0 := by
  apply Function.extend_apply'
  rintro ⟨z, rfl⟩
  exact hx z.property

theorem extendZero_injective (hU : IsOpen U) : Function.Injective (extendZero hU) := by
  intro f g h
  ext u
  simpa only [extendZero_apply_subtype] using
    congrArg (fun k : SchwartzBruhat X => k u.val) h

theorem support_extendZero_subset (hU : IsOpen U) (f : SchwartzBruhat U) :
    Function.support (extendZero hU f : X → ℂ) ⊆ U := by
  intro x hx
  by_contra h
  exact hx (extendZero_apply_of_not_mem hU f h)

/-- The ambient topological support is exactly the compact image of the support
in the open subspace. -/
theorem tsupport_extendZero (hU : IsOpen U) (f : SchwartzBruhat U) :
    tsupport (extendZero hU f : X → ℂ) =
      Subtype.val '' tsupport (f : U → ℂ) :=
  f.hasCompactSupport.tsupport_extend_zero continuous_subtype_val Subtype.val_injective

theorem tsupport_extendZero_subset (hU : IsOpen U) (f : SchwartzBruhat U) :
    tsupport (extendZero hU f : X → ℂ) ⊆ U := by
  rw [tsupport_extendZero]
  rintro _ ⟨u, _, rfl⟩
  exact u.property

end Open
end SchwartzBruhat

namespace Distribution

/-- Distributions annihilating every test function that vanishes pointwise on Z.
The subset need not be closed. -/
def supportedOn (Z : Set X) : Submodule ℂ (Distribution X) where
  carrier := {D | ∀ f : SchwartzBruhat X, (∀ z ∈ Z, f z = 0) → D f = 0}
  zero_mem' := by intro f _; rfl
  add_mem' {D E} hD hE := by
    intro f hf
    change D f + E f = 0
    rw [hD f hf, hE f hf, add_zero]
  smul_mem' c D hD := by
    intro f hf
    change c • D f = 0
    rw [hD f hf, smul_zero]

@[simp]
theorem mem_supportedOn_iff (Z : Set X) (D : Distribution X) :
    D ∈ supportedOn Z ↔
      ∀ f : SchwartzBruhat X, (∀ z ∈ Z, f z = 0) → D f = 0 := Iff.rfl

theorem supportedOn_mono {Z W : Set X} (h : Z ⊆ W) :
    supportedOn Z ≤ supportedOn W := by
  intro D hD f hf
  exact hD f (fun z hz => hf z (h hz))

/-- Pushforward along the closed inclusion, defined by precomposition. -/
def closedPushforward {Z : Set X} (hZ : IsClosed Z) :
    Distribution Z →ₗ[ℂ] Distribution X :=
  (SchwartzBruhat.restrictClosed hZ).dualMap

@[simp]
theorem closedPushforward_apply {Z : Set X} (hZ : IsClosed Z)
    (D : Distribution Z) (f : SchwartzBruhat X) :
    closedPushforward hZ D f = D (SchwartzBruhat.restrictClosed hZ f) := rfl

theorem closedPushforward_mem_supportedOn {Z : Set X} (hZ : IsClosed Z)
    (D : Distribution Z) : closedPushforward hZ D ∈ supportedOn Z := by
  intro f hf
  rw [closedPushforward_apply]
  have h : SchwartzBruhat.restrictClosed hZ f = 0 := by
    ext z
    exact hf z.val z.property
  rw [h, map_zero]

/-- The same pushforward with its codomain restricted to supported distributions. -/
def closedPushforwardSupported {Z : Set X} (hZ : IsClosed Z) :
    Distribution Z →ₗ[ℂ] supportedOn Z :=
  (closedPushforward hZ).codRestrict (supportedOn Z)
    (closedPushforward_mem_supportedOn hZ)

@[simp]
theorem coe_closedPushforwardSupported {Z : Set X} (hZ : IsClosed Z)
    (D : Distribution Z) :
    (closedPushforwardSupported hZ D : Distribution X) = closedPushforward hZ D := rfl

/-- Restriction to an open subspace, dual to extension by zero. -/
def restrictOpen [T2Space X] {U : Set X} (hU : IsOpen U) :
    Distribution X →ₗ[ℂ] Distribution U :=
  (SchwartzBruhat.extendZero hU).dualMap

@[simp]
theorem restrictOpen_apply [T2Space X] {U : Set X} (hU : IsOpen U)
    (D : Distribution X) (f : SchwartzBruhat U) :
    restrictOpen hU D f = D (SchwartzBruhat.extendZero hU f) := rfl

end Distribution
end Langlands.HarmonicAnalysis
