/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-! # The normalized regular-unit mate on final ringed sites

Source: Stacks Project, Modules on Sites, Tag 03D7.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u uC vC uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SheafOfModules

attribute [local instance] monoidalCategory symmetricCategory

/-- The regular-unit mate of normalized direct image is invertible on final sites.
Source: Stacks 03D7 and Mathlib's PullbackFree
(auxiliary; not a blueprint node).
Proof: the unique normalized direct-image pairing has the coefficient-map unit.
Under the uniqueness isomorphism between the specified left adjoint and Mathlib's
pullback, its adjunct is that isomorphism followed by the canonical regular-unit
map. The latter is invertible because the site functor is final. -/
theorem normalized_unit_mate_isIso
    {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (v : C ⥤ D) [v.IsContinuous J K] [v.Final]
    (R : Sheaf J CommRingCat.{u + 1}) (S : Sheaf K CommRingCat.{u + 1})
    (c : (sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      (v.sheafPushforwardContinuous RingCat.{u + 1} J K).obj
        ((sheafCompose K (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S))
    {L : SheafOfModules ((sheafCompose J
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) ⥤
      SheafOfModules ((sheafCompose K
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)}
    (a : L ⊣ pushforward.{u + 1} c)
    (m : (pushforward.{u + 1} c).LaxMonoidal)
    (hm : RingedPushforwardPureTensor.{uC, vC, uD, vD, u + 1} v R S c m) :
    letI := m
    IsIso (a.leftAdjointOplaxMonoidal.η) := by
  let := m
  let := a.isRightAdjoint
  have hε : m.ε = unitToPushforwardObjUnit c := by
    obtain ⟨m₀, _, hε₀, huniq⟩ :=
      exists_unique_ringedPushforward_laxMonoidal v R S c
    have hm₀ : m = m₀ := huniq m hm
    subst m
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    exact LinearMap.ext (fun r ↦ (hε₀ U r).trans
      (unitToPushforwardObjUnit_val_app_apply c r).symm)
  let b := pullbackPushforwardAdjunction c
  let e := a.leftAdjointUniq b
  have he : a.homEquiv _ _ (e.hom.app (𝟙_ _) ≫ pullbackObjUnitToUnit c) =
      unitToPushforwardObjUnit c := by
    rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
    rw [Adjunction.unit_leftAdjointUniq_hom_app]
    exact pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit c
  have hmate : (a.homEquiv _ _).symm m.ε =
      e.hom.app (𝟙_ _) ≫ pullbackObjUnitToUnit c := by
    apply (a.homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, hε]
    exact he.symm
  change IsIso ((a.homEquiv _ _).symm m.ε)
  rw [hmate]
  infer_instance

end SheafOfModules
