import Langlands.Sheaf.Equivariant.LocalAction
import Langlands.Sheaf.Equivariant.Site
import Langlands.Sheaf.Equivariant.Smooth

/-!
# Local actions on the transport category of opens

On the transport category of a group action on a topological space, an open
subgroup acts admissibly on a transport open when each element acts through the
arrow labelled by its inverse. Such actions exist exactly on opens stable under
the subgroup, and they are the published invariant-arrow actions. For this
local action system, the published smooth equivariant module sheaves are
exactly the sheaves whose sections are locally discrete for the transport
topology.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory Opposite

universe u uX uG

namespace ActionOpens

variable {G : Type uG} [Group G] {X : Type uX} [TopologicalSpace X] [MulAction G X]

/-- The action of a subgroup on an open stable under it, through the
inverse-label arrows. -/
def invariantAction (H : Subgroup G) (U : ActionOpens G X)
    (hU : ∀ h : H, ∀ x ∈ U.openSet, (h : G) • x ∈ U.openSet) : H →* (End U)ᵐᵒᵖ where
  toFun h := MulOpposite.op (invariantArrow H U hU h)
  map_one' := by
    rw [invariantArrow_one]
    rfl
  map_mul' g h := by
    rw [invariantArrow_mul]
    rfl

@[simp]
theorem invariantAction_apply (H : Subgroup G) (U : ActionOpens G X)
    (hU : ∀ h : H, ∀ x ∈ U.openSet, (h : G) • x ∈ U.openSet) (h : H) :
    (invariantAction H U hU h).unop = invariantArrow H U hU h := rfl

variable (G X) in
/-- The admissible local actions on transport opens: every element of the open
subgroup acts through an arrow labelled by its inverse. -/
def localActionSystem [TopologicalSpace G] : LocalActionSystem (ActionOpens G X) G where
  IsAdmissible _ _ a := ∀ h, (a h).unop.label = (h : G)⁻¹

variable [TopologicalSpace G]

theorem isAdmissible_invariantAction (H : OpenSubgroup G) (U : ActionOpens G X)
    (hU : ∀ h : (H : Subgroup G), ∀ x ∈ U.openSet, (h : G) • x ∈ U.openSet) :
    (localActionSystem G X).IsAdmissible U H (invariantAction (H : Subgroup G) U hU) :=
  fun _ => rfl

/-- An open carrying an admissible action of an open subgroup is stable under it. -/
theorem stable_of_isAdmissible {U : ActionOpens G X} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} (ha : (localActionSystem G X).IsAdmissible U H a) :
    ∀ h : (H : Subgroup G), ∀ x ∈ U.openSet, (h : G) • x ∈ U.openSet := by
  intro h x hx
  have hmaps := (a h⁻¹).unop.mapsTo x hx
  rwa [ha, Subgroup.coe_inv, inv_inv] at hmaps

/-- Admissible actions are exactly the invariant-arrow actions on stable opens. -/
theorem isAdmissible_iff {U : ActionOpens G X} {H : OpenSubgroup G}
    {a : (H : Subgroup G) →* (End U)ᵐᵒᵖ} :
    (localActionSystem G X).IsAdmissible U H a ↔
      ∃ hU : ∀ h : (H : Subgroup G), ∀ x ∈ U.openSet, (h : G) • x ∈ U.openSet,
        a = invariantAction (H : Subgroup G) U hU := by
  constructor
  · intro ha
    refine ⟨stable_of_isAdmissible ha, ?_⟩
    ext h
    apply MulOpposite.unop_injective
    apply Hom.ext
    exact ha h
  · rintro ⟨hU, rfl⟩
    exact isAdmissible_invariantAction H U hU

end ActionOpens

variable (R : Type u) [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

/-- Smooth equivariant module sheaves are locally discrete for the transport
topology. -/
theorem IsSmoothSheaf.isLocallyDiscrete {F : TopologicalSheaf G X (ModuleCat.{u} R)}
    (hF : IsSmoothSheaf R G X F) :
    (ActionOpens.localActionSystem G X).IsLocallyDiscrete (transportTopology G X) F.obj := by
  intro U s
  rw [mem_transportTopology_iff]
  intro x hx
  obtain ⟨V, hVU, H, hV, hxV, hfix⟩ := hF U s x hx
  exact ⟨V, hVU, ⟨V, 𝟙 V, ActionOpens.inclusionHom hVU, H,
    ActionOpens.invariantAction (H : Subgroup G) V hV,
    ActionOpens.isAdmissible_invariantAction H V hV, ⟨H, le_rfl, fun h _ => hfix h⟩,
    Category.id_comp _⟩, hxV⟩

/-- Sheaves whose sections are locally discrete for the transport topology are
smooth. Conjugating the stabilizing subgroup back along the label of the
restriction arrow uses continuity of multiplication. -/
theorem isSmoothSheaf_of_isLocallyDiscrete [ContinuousMul G]
    {F : TopologicalSheaf G X (ModuleCat.{u} R)}
    (hF : (ActionOpens.localActionSystem G X).IsLocallyDiscrete (transportTopology G X) F.obj) :
    IsSmoothSheaf R G X F := by
  intro U s x hx
  obtain ⟨V₁, h₁, ⟨V, k, f, H, a, ha, ⟨K, hKH, hK⟩, hkf⟩, hxV₁⟩ :=
    mem_transportTopology_iff.1 (hF U s) x hx
  have hV := ActionOpens.stable_of_isAdmissible ha
  have hk : k.label = f.label⁻¹ := by
    have h := congrArg ActionOpens.Hom.label hkf
    change f.label * k.label = 1 at h
    exact eq_inv_of_mul_eq_one_right h
  have hcont : Continuous ((MulAut.conj f.label⁻¹).toMonoidHom : G → G) := by
    change Continuous fun g : G => f.label⁻¹ * g * f.label⁻¹⁻¹
    exact (continuous_const.mul continuous_id).mul continuous_const
  let K' : OpenSubgroup G := K.comap (MulAut.conj f.label⁻¹).toMonoidHom hcont
  have hK' : ∀ g : G, g ∈ K' ↔ f.label⁻¹ * g * f.label ∈ K := fun g => by
    change f.label⁻¹ * g * f.label⁻¹⁻¹ ∈ K ↔ _
    rw [inv_inv]
  let V' := ActionOpens.translate f.label V
  have hVU : V'.openSet ≤ U.openSet := ActionOpens.translate_le f
  have hV' : ∀ g : (K' : Subgroup G), ∀ y ∈ V'.openSet, (g : G) • y ∈ V'.openSet := by
    intro g y hy
    have hg : f.label⁻¹ * g * f.label ∈ H := hKH ((hK' g).1 g.2)
    have hmaps := hV ⟨_, hg⟩ _ hy
    rw [ActionOpens.mem_translate]
    have hy' : (f.label⁻¹ * (g : G) * f.label) • f.label⁻¹ • y = f.label⁻¹ • (g : G) • y := by
      rw [← mul_smul, ← mul_smul, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
    rw [← hy']
    exact hmaps
  refine ⟨V', hVU, K', hV', ?_, fun g => ?_⟩
  · rw [ActionOpens.mem_translate, ← hk]
    exact k.mapsTo x hxV₁
  · let kk : (H : Subgroup G) := ⟨f.label⁻¹ * g * f.label, hKH ((hK' g).1 g.2)⟩
    have hkk : (kk : G) ∈ K := (hK' g).1 g.2
    have harrow : ActionOpens.invariantArrow (K' : Subgroup G) V' hV' g ≫
          ActionOpens.inclusionHom hVU =
        (ActionOpens.translationIso f.label V).inv ≫ (a kk).unop ≫ f := by
      apply ActionOpens.Hom.ext
      rw [ActionOpens.comp_label, ActionOpens.comp_label, ActionOpens.comp_label, ha kk]
      change (1 : G) * (g : G)⁻¹ = f.label * (f.label⁻¹ * g * f.label)⁻¹ * f.label⁻¹
      group
    have key : F.obj.map (ActionOpens.invariantArrow (K' : Subgroup G) V' hV' g ≫
          ActionOpens.inclusionHom hVU).op s =
        F.obj.map (ActionOpens.inclusionHom hVU).op s := by
      rw [harrow, op_comp, Functor.map_comp_apply, op_comp, Functor.map_comp_apply, hK kk hkk,
        ← Functor.map_comp_apply, ← op_comp, ActionOpens.translationIso_inv_comp]
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, ← op_comp]
    exact key

/-- Smooth equivariant module sheaves are exactly the locally discrete sheaves
for the transport local action system. -/
theorem isSmoothSheaf_iff_isLocallyDiscrete [ContinuousMul G]
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    IsSmoothSheaf R G X F ↔
      (ActionOpens.localActionSystem G X).IsLocallyDiscrete (transportTopology G X) F.obj :=
  ⟨IsSmoothSheaf.isLocallyDiscrete R, isSmoothSheaf_of_isLocallyDiscrete R⟩

/-- Under the equivalence with transport sheaves, the published smoothness
property is the generic smooth sheaf property of the transport local action
system. -/
theorem smoothSheafProperty_sheafEquivalence_iff [ContinuousMul G]
    (F : TopologicalSheaf G X (ModuleCat.{u} R)) :
    (ActionOpens.localActionSystem G X).smoothSheafProperty (ModuleCat.{u} R)
        (transportTopology G X) ((sheafEquivalence G X (ModuleCat.{u} R)).functor.obj F) ↔
      smoothSheafProperty R G X F :=
  (isSmoothSheaf_iff_isLocallyDiscrete R F).symm

end Langlands.Sheaf.Equivariant
