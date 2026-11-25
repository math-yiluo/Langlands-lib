/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement

/-! # Actual section carriers and normalized open-extension units

Carrier equalities are proved before specializing the coefficient systems. Explicit transports
then keep the unit calculations from repeatedly unfolding the coefficient and sheafification
constructions. All carrier maps, naturality statements, and the unit-generation criterion
below are proved; this module introduces no postponed proof.

## References

* Stacks Project, Tags 03DI--03DJ
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe c v r u
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections.OpenUnitSections

attribute [local irreducible] systemRing ringPresheaf rings

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [EssentiallySmall.{max c v r} C]
  (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n) (U : C)
  (O : OpenSystems.{c, v, r} J B τ U)

/-- Application respects heterogeneous equality with the specified result carrier. -/
theorem apply_heq {α β γ δ : Type u} {f : α → β} {g : γ → δ}
    (hβ : β = δ) (hf : HEq f g) {x : α} {y : γ} (hx : HEq x y) :
    HEq (f x) (g y) := by
  cases hβ
  exact heq_of_eq (congr_heq hf hx)

private theorem section_congr
    {D : Type*} [Category D] {K : GrothendieckTopology D} {S : Sheaf K RingCat}
    {M N : SheafOfModules S} {f g : M ⟶ N} (h : f = g) (V : Dᵒᵖ)
    (x : M.val.obj V) : f.val.app V x = g.val.app V x := by
  cases h
  rfl

/-- A module-sheaf isomorphism is injective on every section module. -/
theorem iso_section_injective
    {D : Type*} [Category D] {K : GrothendieckTopology D} {S : Sheaf K RingCat}
    {M N : SheafOfModules S} (e : M ≅ N) (V : Dᵒᵖ) :
    Function.Injective (fun x ↦ e.hom.val.app V x) := by
  intro x y h
  have hx := section_congr e.hom_inv_id V x
  have hy := section_congr e.hom_inv_id V y
  exact hx.symm.trans ((congrArg (fun z ↦ e.inv.val.app V z) h).trans hy)

-- Prove carrier identifications before specializing to the large system coefficient rings.
-- Explicit casts below avoid repeatedly unfolding those coefficient constructions.
private theorem pushforward_type
    {D E : Type*} [Category D] [Category E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{u}} {T : Sheaf L RingCat.{u}}
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K L).obj T)
    (M : SheafOfModules.{u} T) (V : Dᵒᵖ) :
    (((SheafOfModules.pushforward.{u} a).obj M).val.obj V : Type u) =
      (M.val.obj (op (F.obj V.unop)) : Type u) := rfl

/-- Transport a section function along proved equalities of its source and target carriers. -/
def castMap {α β γ δ : Type u} (f : α → β) (ha : α = γ) (hb : β = δ) :
    γ → δ := fun x ↦ cast hb (f (cast ha.symm x))

private theorem castMap_comp {α β γ A B D : Type u} (f : α → β) (g : β → γ)
    (ha : α = A) (hb : β = B) (hc : γ = D) :
    castMap (g ∘ f) ha hc = castMap g hb hc ∘ castMap f ha hb := by
  cases ha
  cases hb
  cases hc
  rfl

/-- Carrier transport preserves the value of the original section function. -/
theorem castMap_heq {α β γ δ : Type u} (f : α → β) (ha : α = γ) (hb : β = δ)
    (x : γ) : HEq (castMap f ha hb x) (f (cast ha.symm x)) := cast_heq _ _

/-- Carrier transport preserves injectivity. -/
theorem castMap_injective {α β γ δ : Type u} (f : α → β)
    (ha : α = γ) (hb : β = δ) (hf : Function.Injective f) :
    Function.Injective (castMap f ha hb) := by
  cases ha
  cases hb
  exact hf

private theorem castMap_of_heq {α β γ δ : Type u} (f : α → β) (g : γ → δ)
    (ha : α = γ) (hb : β = δ) (h : HEq f g) : castMap f ha hb = g := by
  cases ha
  cases hb
  exact eq_of_heq h

private theorem pushforward_restrict_cast
    {D E : Type*} [Category D] [Category E]
    {K : GrothendieckTopology D} {L : GrothendieckTopology E}
    {F : D ⥤ E} [F.IsContinuous K L]
    {S : Sheaf K RingCat.{u}} {T : Sheaf L RingCat.{u}}
    (a : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} K L).obj T)
    (M : SheafOfModules.{u} T) {V W : Dᵒᵖ} (f : V ⟶ W) :
    castMap (fun x ↦ ((SheafOfModules.pushforward.{u} a).obj M).val.map f x)
      (pushforward_type a M V) (pushforward_type a M W) =
    (fun x ↦ M.val.map (F.map f.unop).op x) := rfl

/-- Evaluation preserves the underlying carrier of the corresponding system section. -/
theorem evaluation_type
    (M : Systems.{c, v, max c v r} J B τ) (n : ℕ) (V : Cᵒᵖ) :
    (((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj V : Type (max c v r)) =
      (M.val.obj (op (n, V.unop)) : Type (max c v r)) :=
  pushforward_type (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm) M V

/-- Open restriction preserves the carrier at the underlying system-site object. -/
theorem open_restriction_type
    (M : Systems.{c, v, max c v r} J B τ) (V : (ℕ × Over U)ᵒᵖ) :
    (((openRestriction.{c, v, r} J B τ U).obj M).val.obj V : Type (max c v r)) =
      (M.val.obj (op (V.unop.1, V.unop.2.left)) : Type (max c v r)) :=
  pushforward_type (eqToHom (openRing.{c, v, r} J B τ U).symm) M V

/-- The system adjunction unit, expressed in the actual base system section carrier. -/
def rawUnit
    (M : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (V : (ℕ × Over U)ᵒᵖ)
    (x : M.val.obj V) : (O.extension.obj M).val.obj (op (V.unop.1, V.unop.2.left)) :=
  cast (open_restriction_type.{c, v, r} J B τ U (O.extension.obj M) V)
    ((O.ordinaryAdjunction.unit.app M).val.app V x)

/-- The transported system unit commutes with every site restriction. -/
theorem rawUnit_naturality
    (M : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U))
    {V W : (ℕ × Over U)ᵒᵖ} (f : V ⟶ W) (x : M.val.obj V) :
    rawUnit.{c, v, r} J B τ U O M W (M.val.map f x) =
      (O.extension.obj M).val.map ((openSite U).map f.unop).op
        (rawUnit.{c, v, r} J B τ U O M V x) := by
  have h := PresheafOfModules.naturality_apply (O.ordinaryAdjunction.unit.app M).val f x
  have hh := congrArg (cast (open_restriction_type.{c, v, r} J B τ U (O.extension.obj M) W)) h
  have hm := congrFun (pushforward_restrict_cast
    (eqToHom (openRing.{c, v, r} J B τ U).symm) (O.extension.obj M) f)
    (rawUnit.{c, v, r} J B τ U O M V x)
  simp only [castMap, rawUnit] at hm
  exact hh.trans hm

/-- Restriction to a slice preserves the underlying base section carrier. -/
theorem over_type
    {D : Type*} [Category D] {K : GrothendieckTopology D}
    {A : Sheaf K RingCat.{u}} (M : SheafOfModules.{u} A) (U : D) (V : (Over U)ᵒᵖ) :
    (((SheafOfModules.overFunctor.{u} A U).obj M).val.obj V : Type u) =
      (M.val.obj (op V.unop.left) : Type u) := pushforward_type (𝟙 _) M V

private theorem over_map_cast
    {D : Type*} [Category D] {K : GrothendieckTopology D} {A : Sheaf K RingCat.{u}}
    {M N : SheafOfModules.{u} A} (f : M ⟶ N) (U : D) (V : (Over U)ᵒᵖ) :
    castMap (fun x ↦ ((SheafOfModules.overFunctor.{u} A U).map f).val.app V x)
      (over_type M U V) (over_type N U V) =
      (fun x ↦ f.val.app (op V.unop.left) x) := rfl

/-- Restriction of scalars preserves the underlying section carrier. -/
theorem res_type
    {A A' : Sheaf J CommRingCat.{max c v r}} (φ : A ⟶ A')
    (M : Mod.{c, v, max c v r} J A') (V : Cᵒᵖ) :
    (((res.{c, v, max c v r} φ).obj M).val.obj V : Type (max c v r)) =
      (M.val.obj V : Type (max c v r)) := rfl

/-- Restriction of scalars preserves the actual section function of a morphism. -/
theorem res_map_cast
    {A A' : Sheaf J CommRingCat.{max c v r}} (φ : A ⟶ A')
    {M N : Mod.{c, v, max c v r} J A'} (f : M ⟶ N) (V : Cᵒᵖ)
    {X Y : Type (max c v r)} (hM : (M.val.obj V : Type (max c v r)) = X)
    (hN : (N.val.obj V : Type (max c v r)) = Y) :
    castMap (fun x ↦ ((res.{c, v, max c v r} φ).map f).val.app V x)
      ((res_type.{c, v, r} J φ M V).trans hM) ((res_type.{c, v, r} J φ N V).trans hN) =
      castMap (fun x ↦ f.val.app V x) hM hN := by
  cases hM
  cases hN
  rfl

/-- Section-function transport respects composition of module-sheaf morphisms. -/
theorem section_cast_comp
    {D : Type*} [Category D] {K : GrothendieckTopology D} {A : Sheaf K RingCat.{u}}
    {M N P : SheafOfModules.{u} A} (f : M ⟶ N) (g : N ⟶ P) (V : Dᵒᵖ)
    {X Y Z : Type u} (hM : (M.val.obj V : Type u) = X)
    (hN : (N.val.obj V : Type u) = Y) (hP : (P.val.obj V : Type u) = Z) :
    castMap (fun x ↦ (f ≫ g).val.app V x) hM hP =
      castMap (fun x ↦ g.val.app V x) hN hP ∘ castMap (fun x ↦ f.val.app V x) hM hN :=
  castMap_comp _ _ hM hN hP

/-- Section-function transport respects a three-factor composite. -/
theorem section_cast_triple
    {D : Type*} [Category D] {K : GrothendieckTopology D} {A : Sheaf K RingCat.{u}}
    {M N P T : SheafOfModules.{u} A} (f : M ⟶ N) (g : N ⟶ P) (h : P ⟶ T) (V : Dᵒᵖ)
    {X Y Z W : Type u} (hM : (M.val.obj V : Type u) = X)
    (hN : (N.val.obj V : Type u) = Y) (hP : (P.val.obj V : Type u) = Z)
    (hT : (T.val.obj V : Type u) = W) :
    castMap (fun x ↦ (f ≫ g ≫ h).val.app V x) hM hT =
      castMap (fun x ↦ h.val.app V x) hP hT ∘
        castMap (fun x ↦ g.val.app V x) hN hP ∘ castMap (fun x ↦ f.val.app V x) hM hN := by
  cases hM
  cases hN
  cases hP
  cases hT
  rfl

/-- A transported system transition is the actual horizontal presheaf restriction. -/
theorem transition_cast
    (M : Systems.{c, v, max c v r} J B τ) {m n : ℕ} (h : n ≤ m) (V : Cᵒᵖ) :
    castMap (fun x ↦ ((transition J B τ h).app M).val.app V x)
      (evaluation_type.{c, v, r} J B τ M m V)
      ((res_type.{c, v, r} J (coefficientMap J B τ h) ((evaluation J B τ n).obj M) V).trans
        (evaluation_type.{c, v, r} J B τ M n V)) =
      (fun x ↦ M.val.map (Prod.mkHom (homOfLE h) (𝟙 V.unop)).op x) :=
  castMap_of_heq _ _ _ _ ((transition_exists J B τ h).exists.choose_spec M V)

/-- The ordinary localized adjunction unit is natural on actual section carriers. -/
theorem localized_unit_naturality_cast
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (A : Sheaf J CommRingCat.{max c v r}) (U : C)
    {M N : SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J A).over U)} (f : M ⟶ N)
    (V : (Over U)ᵒᵖ) (x : M.val.obj V) :
    ((SheafOfModules.localizedSystemExtension.{c, v, r} A U).map f).val.app
        (op V.unop.left)
        (cast (over_type ((SheafOfModules.localizedSystemExtension.{c, v, r} A U).obj M) U V)
          (((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.app M).val.app V x)) =
      cast (over_type ((SheafOfModules.localizedSystemExtension.{c, v, r} A U).obj N) U V)
        (((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.app N).val.app V
          (f.val.app V x)) := by
  have hn := section_congr
    ((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.naturality f) V x
  change ((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.app N).val.app V
      (f.val.app V x) =
    ((SheafOfModules.localizedSystemRestriction.{c, v, r} A U).map
      ((SheafOfModules.localizedSystemExtension.{c, v, r} A U).map f)).val.app V
        (((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.app M).val.app V x)
    at hn
  have hm := congrFun (over_map_cast
    ((SheafOfModules.localizedSystemExtension.{c, v, r} A U).map f) U V)
    (cast (over_type ((SheafOfModules.localizedSystemExtension.{c, v, r} A U).obj M) U V)
      (((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.app M).val.app V x))
  have hn' := congrArg
    (cast (over_type ((SheafOfModules.localizedSystemExtension.{c, v, r} A U).obj N) U V)) hn
  simp only [castMap, cast_cast, cast_eq] at hm
  exact hm.symm.trans hn'.symm

private theorem unit_generic
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) (U : C) (n : ℕ)
    (L : GrothendieckTopology (ℕ × C)) (K : GrothendieckTopology (ℕ × Over U))
    [(openSite U).IsContinuous K L]
    [(Prod.sectR n C).IsContinuous J L]
    [(Prod.sectR n (Over U)).IsContinuous (J.over U) K]
    (S : Sheaf L RingCat.{max c v r}) (T : Sheaf K RingCat.{max c v r})
    (A : Sheaf J RingCat.{max c v r}) (D : Sheaf (J.over U) RingCat.{max c v r})
    (a : T ⟶ ((openSite U).sheafPushforwardContinuous RingCat.{max c v r} K L).obj S)
    (b : A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous
      RingCat.{max c v r} J L).obj S)
    (d : D ⟶ ((Prod.sectR n (Over U)).sheafPushforwardContinuous
      RingCat.{max c v r} (J.over U) K).obj T)
    (e : D ⟶ ((Over.forget U).sheafPushforwardContinuous
      RingCat.{max c v r} (J.over U) J).obj A)
    {M : SheafOfModules.{max c v r} T} {N : SheafOfModules.{max c v r} S}
    {Z : SheafOfModules.{max c v r} A}
    (η : M ⟶ (SheafOfModules.pushforward.{max c v r} a).obj N)
    (ε : (SheafOfModules.pushforward.{max c v r} b).obj N ⟶ Z)
    (ρ : (SheafOfModules.pushforward.{max c v r} d).obj
        ((SheafOfModules.pushforward.{max c v r} a).obj N) ⟶
      (SheafOfModules.pushforward.{max c v r} e).obj
        ((SheafOfModules.pushforward.{max c v r} b).obj N))
    (θ : (SheafOfModules.pushforward.{max c v r} d).obj M ⟶
      (SheafOfModules.pushforward.{max c v r} e).obj Z)
    (hρ : ∀ V x, HEq (ρ.val.app V x) x)
    (hu : (SheafOfModules.pushforward.{max c v r} d).map η ≫ ρ ≫
        (SheafOfModules.pushforward.{max c v r} e).map ε = θ)
    (V : (Over U)ᵒᵖ) (x : M.val.obj (op (n, V.unop))) :
    ε.val.app (op V.unop.left) (η.val.app (op (n, V.unop)) x) = θ.val.app V x := by
  have hv := section_congr hu V x
  change ε.val.app (op V.unop.left)
    (ρ.val.app V (η.val.app (op (n, V.unop)) x)) = _ at hv
  have hr := eq_of_heq (hρ V (η.val.app (op (n, V.unop)) x))
  exact (congrArg (fun z ↦ ε.val.app (op V.unop.left) z) hr).symm.trans hv

private theorem unit_cast_generic
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C) (U : C) (n : ℕ)
    (L : GrothendieckTopology (ℕ × C)) (K : GrothendieckTopology (ℕ × Over U))
    [(openSite U).IsContinuous K L]
    [(Prod.sectR n C).IsContinuous J L]
    [(Prod.sectR n (Over U)).IsContinuous (J.over U) K]
    (S : Sheaf L RingCat.{max c v r}) (T : Sheaf K RingCat.{max c v r})
    (A : Sheaf J RingCat.{max c v r}) (D : Sheaf (J.over U) RingCat.{max c v r})
    (a : T ⟶ ((openSite U).sheafPushforwardContinuous RingCat.{max c v r} K L).obj S)
    (b : A ⟶ ((Prod.sectR n C).sheafPushforwardContinuous
      RingCat.{max c v r} J L).obj S)
    (d : D ⟶ ((Prod.sectR n (Over U)).sheafPushforwardContinuous
      RingCat.{max c v r} (J.over U) K).obj T)
    (e : D ⟶ ((Over.forget U).sheafPushforwardContinuous
      RingCat.{max c v r} (J.over U) J).obj A)
    {M : SheafOfModules.{max c v r} T} {N : SheafOfModules.{max c v r} S}
    {Z : SheafOfModules.{max c v r} A}
    (η : M ⟶ (SheafOfModules.pushforward.{max c v r} a).obj N)
    (ε : (SheafOfModules.pushforward.{max c v r} b).obj N ⟶ Z)
    (ρ : (SheafOfModules.pushforward.{max c v r} d).obj
        ((SheafOfModules.pushforward.{max c v r} a).obj N) ⟶
      (SheafOfModules.pushforward.{max c v r} e).obj
        ((SheafOfModules.pushforward.{max c v r} b).obj N))
    (θ : (SheafOfModules.pushforward.{max c v r} d).obj M ⟶
      (SheafOfModules.pushforward.{max c v r} e).obj Z)
    (hρ : ∀ V x, HEq (ρ.val.app V x) x)
    (hu : (SheafOfModules.pushforward.{max c v r} d).map η ≫ ρ ≫
        (SheafOfModules.pushforward.{max c v r} e).map ε = θ)
    (V : (Over U)ᵒᵖ) (x : M.val.obj (op (n, V.unop))) :
    ε.val.app (op V.unop.left)
      (cast (pushforward_type b N (op V.unop.left)).symm
        (cast (pushforward_type a N (op (n, V.unop)))
          (η.val.app (op (n, V.unop)) x))) =
      cast (pushforward_type e Z V)
        (θ.val.app V (cast (pushforward_type d M V).symm x)) := by
  dsimp only [pushforward_type, cast]
  exact unit_generic.{c, v, r} J U n L K S T A D a b d e η ε ρ θ hρ hu V x

private theorem open_unit_section_cast
    (hO : ∀ (n : ℕ) N V x,
      HEq (((O.restrictionEvaluation n).hom.app N).val.app V x) x)
    (M : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (n : ℕ) (V : (Over U)ᵒᵖ)
    (x : M.val.obj (op (n, V.unop))) :
    ((O.extensionEvaluation n).hom.app M).val.app (op V.unop.left)
      (cast (pushforward_type
        (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm)
        (O.extension.obj M) (op V.unop.left)).symm
        (cast (pushforward_type (eqToHom (openRing.{c, v, r} J B τ U).symm)
          (O.extension.obj M) (op (n, V.unop)))
          ((O.ordinaryAdjunction.unit.app M).val.app (op (n, V.unop)) x))) =
      cast (pushforward_type (𝟙 _)
        ((@SheafOfModules.localizedSystemExtension.{c, v, r} C _ J
          (abelianSheafify.{c, v, max c v r} J)
          (locallyBijective.{c, v, max c v r} J) (B n) U).obj
            ((evaluation.{max c v, v, max c v r} (J.over U) (openRings.{c, v, r} J B U)
              (openTransitions.{c, v, r} J B τ U) n).obj M)) V)
        (((@SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
          (abelianSheafify.{c, v, max c v r} J)
          (locallyBijective.{c, v, max c v r} J) (B n) U).unit.app
            ((evaluation.{max c v, v, max c v r} (J.over U) (openRings.{c, v, r} J B U)
              (openTransitions.{c, v, r} J B τ U) n).obj M)).val.app V
            (cast (pushforward_type (eqToHom
              (evaluation_ring.{max c v, v, max c v r} (J.over U)
                (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) n).symm)
              M V).symm x)) := by
  exact @unit_cast_generic.{c, v, r} C _ J U n
    (coefficientSequenceTopology J) (coefficientSequenceTopology (J.over U)) _ _ _
    (ring.{c, v, max c v r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ))
    (ring.{max c v, v, max c v r} (coefficientSequenceTopology (J.over U))
      (systemRing.{max c v, v, max c v r} (J.over U) (openRings.{c, v, r} J B U)
        (openTransitions.{c, v, r} J B τ U)))
    (ring.{c, v, max c v r} J (B n))
    (ring.{max c v, v, max c v r} (J.over U) (openRings.{c, v, r} J B U n))
    (eqToHom (openRing.{c, v, r} J B τ U).symm)
    (eqToHom (evaluation_ring.{c, v, max c v r} J B τ n).symm)
    (eqToHom (evaluation_ring.{max c v, v, max c v r} (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U) n).symm) (𝟙 _)
    M (O.extension.obj M) _
    (O.ordinaryAdjunction.unit.app M) ((O.extensionEvaluation n).hom.app M)
    ((O.restrictionEvaluation n).hom.app (O.extension.obj M))
    ((@SheafOfModules.localizedSystemAdjunction.{c, v, r} C _ J
      (abelianSheafify.{c, v, max c v r} J)
      (locallyBijective.{c, v, max c v r} J) (B n) U).unit.app _)
    (hO n (O.extension.obj M)) (O.unit_evaluation n M) V x

/-- The ordinary localized unit section, transported to its base section carrier. -/
def ordinaryUnitSection
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (A : Sheaf J CommRingCat.{max c v r}) (U : C)
    (M : SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J A).over U))
    (V : (Over U)ᵒᵖ) (x : M.val.obj V) :=
  cast (over_type ((SheafOfModules.localizedSystemExtension.{c, v, r} A U).obj M) U V)
    (((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.app M).val.app V x)

/-- The extension evaluation homomorphism on the actual system section carrier. -/
def rawExtensionEvaluation
    (M : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (n : ℕ) (V : Cᵒᵖ) :=
  castMap (fun x ↦ ((O.extensionEvaluation n).hom.app M).val.app V x)
    (evaluation_type.{c, v, r} J B τ (O.extension.obj M) n V) rfl

/-- The system unit becomes the ordinary localized unit under extension evaluation. -/
theorem rawUnit_evaluation
    (hO : ∀ (n : ℕ) N V x,
      HEq (((O.restrictionEvaluation n).hom.app N).val.app V x) x)
    (M : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (n : ℕ) (V : (Over U)ᵒᵖ)
    (x : M.val.obj (op (n, V.unop))) :
    rawExtensionEvaluation.{c, v, r} J B τ U O M n (op V.unop.left)
        (rawUnit.{c, v, r} J B τ U O M (op (n, V.unop)) x) =
      (@ordinaryUnitSection.{c, v, r} C _ J
        (abelianSheafify.{c, v, max c v r} J)
        (locallyBijective.{c, v, max c v r} J) (B n) U
        ((evaluation.{max c v, v, max c v r} (J.over U) (openRings.{c, v, r} J B U)
          (openTransitions.{c, v, r} J B τ U) n).obj M) V
        (cast (evaluation_type.{max c v, v, r} (J.over U) (openRings.{c, v, r} J B U)
          (openTransitions.{c, v, r} J B τ U) M n V).symm x)) := by
  exact open_unit_section_cast.{c, v, r} J B τ U O hO M n V x

private theorem localized_hom_ext
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (A : Sheaf J CommRingCat.{max c v r}) (U : C)
    (M : SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J A).over U))
    {E N : SheafOfModules.{max c v r} (ring.{c, v, max c v r} J A)}
    (e : E ≅ (SheafOfModules.localizedSystemExtension.{c, v, r} A U).obj M)
    {f g : E ⟶ N}
    (he : ∀ (V : (Over U)ᵒᵖ) (x : M.val.obj V),
      f.val.app (op V.unop.left) (e.inv.val.app (op V.unop.left)
        (((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.app M).val.app
          V x)) =
      g.val.app (op V.unop.left) (e.inv.val.app (op V.unop.left)
        (((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).unit.app M).val.app
          V x))) : f = g := by
  apply (cancel_epi e.inv).mp
  apply ((SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).homEquiv M N).injective
  rw [(SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).homEquiv_unit,
    (SheafOfModules.localizedSystemAdjunction.{c, v, r} A U).homEquiv_unit]
  ext V x
  exact he V x

private theorem localized_hom_ext_cast
    {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max c v r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    (A : Sheaf J CommRingCat.{max c v r}) (U : C)
    (M : SheafOfModules.{max c v r} ((ring.{c, v, max c v r} J A).over U))
    {E N : SheafOfModules.{max c v r} (ring.{c, v, max c v r} J A)}
    (e : E ≅ (SheafOfModules.localizedSystemExtension.{c, v, r} A U).obj M)
    {f g : E ⟶ N}
    (he : ∀ (V : (Over U)ᵒᵖ) (x : M.val.obj V),
      f.val.app (op V.unop.left) (e.inv.val.app (op V.unop.left)
        (ordinaryUnitSection.{c, v, r} J A U M V x)) =
      g.val.app (op V.unop.left) (e.inv.val.app (op V.unop.left)
        (ordinaryUnitSection.{c, v, r} J A U M V x))) : f = g := by
  apply localized_hom_ext.{c, v, r} J A U M e
  intro V x
  dsimp only [ordinaryUnitSection, over_type, pushforward_type, cast] at he
  exact he V x

/-- Maps from an evaluated open extension are determined by the transported system unit. -/
theorem open_level_hom_ext_raw
    (hO : ∀ (n : ℕ) N V x,
      HEq (((O.restrictionEvaluation n).hom.app N).val.app V x) x)
    (M : Systems (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U)) (n : ℕ)
    {N : Mod.{c, v, max c v r} J (B n)}
    {f g : (evaluation.{c, v, max c v r} J B τ n).obj (O.extension.obj M) ⟶ N}
    (he : ∀ (V : (Over U)ᵒᵖ) (x : M.val.obj (op (n, V.unop))),
      f.val.app (op V.unop.left)
          (cast (evaluation_type.{c, v, r} J B τ (O.extension.obj M) n (op V.unop.left)).symm
            (rawUnit.{c, v, r} J B τ U O M (op (n, V.unop)) x)) =
      g.val.app (op V.unop.left)
          (cast (evaluation_type.{c, v, r} J B τ (O.extension.obj M) n (op V.unop.left)).symm
            (rawUnit.{c, v, r} J B τ U O M (op (n, V.unop)) x))) : f = g := by
  apply @localized_hom_ext_cast.{c, v, r} C _ J
    (abelianSheafify.{c, v, max c v r} J)
    (locallyBijective.{c, v, max c v r} J) (B n) U
    ((evaluation.{max c v, v, max c v r} (J.over U) (openRings.{c, v, r} J B U)
      (openTransitions.{c, v, r} J B τ U) n).obj M) _ N ((O.extensionEvaluation n).app M)
  intro V x
  let y := cast (evaluation_type.{max c v, v, r} (J.over U)
    (openRings.{c, v, r} J B U) (openTransitions.{c, v, r} J B τ U) M n V) x
  have hu := rawUnit_evaluation.{c, v, r} J B τ U O hO M n V y
  simp only [rawExtensionEvaluation, castMap, cast_eq, y, cast_cast] at hu
  have hi := section_congr ((O.extensionEvaluation n).hom_inv_id_app M)
    (op V.unop.left)
    (cast (evaluation_type.{c, v, r} J B τ (O.extension.obj M) n (op V.unop.left)).symm
      (rawUnit.{c, v, r} J B τ U O M (op (n, V.unop)) y))
  have hu' := congrArg
    (fun z ↦ ((O.extensionEvaluation n).inv.app M).val.app (op V.unop.left) z) hu
  exact (congrArg (fun z ↦ f.val.app (op V.unop.left) z) (hi.symm.trans hu')).symm.trans
    ((he V y).trans (congrArg (fun z ↦ g.val.app (op V.unop.left) z) (hi.symm.trans hu')))

end WeilConjectures.SemilinearSections.OpenUnitSections
