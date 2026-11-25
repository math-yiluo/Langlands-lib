/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Pullback of power maps from the constant sheaf to units

Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, proper case,
compatible primitive-root trivializations (blueprint: lem-sc-power-map-pullback).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Source: blueprint sec-curve-estimates/sbc-thm-algebraically-closed-invariance, proper case,
compatible primitive-root trivializations (blueprint: lem-sc-power-map-pullback).

Proof: transpose both maps under inverse image/direct image and the constant-sheaf/global-
sections adjunction. Uniqueness of left adjoints defining the constant comparison identifies
its transpose with the identity on constant global sections. The units comparison is adjoint
to pullback of functions. On the constant presheaf, a natural-number class a is sent to the
restriction of ζ^a. Pullback of functions preserves powers, and restriction commutes with
pullback by the defining pullback square of each object of the small étale site. Thus the
transposes agree on every a; all classes of ZMod n are natural-number classes. The universal
property of sheafification and the two adjunctions give the asserted equality. This includes
n = 1 and empty schemes; no primitivity or field hypothesis is used. -/
theorem constantZModToGmSheaf_pullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (n : ℕ) [NeZero n] (ζ : Γ(Y, ⊤)ˣ) (hζ : ζ ^ n = 1)
    (η : Γ(X, ⊤)ˣ) (hη : η ^ n = 1)
    (h : Units.map g.appTop.hom.toMonoidHom ζ = η) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).map
        (Y.constantZModToGmSheaf n ζ hζ) ≫ upperStarGmSheafToGmSheaf g =
      ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).app
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod n)))).hom ≫
      X.constantZModToGmSheaf n η hη := by
  let A := AddCommGrpCat.of (ULift.{u + 1} (ZMod n))
  let adjY := constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let adjX := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal
  let adjG := Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g
  let β := Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g
  let adj := (adjY.comp adjG).ofNatIsoRight β
  apply (adj.homEquiv A X.gmSheaf).injective
  have hr (m : X.constantZMod n ⟶ X.gmSheaf) :
      adj.homEquiv A X.gmSheaf
        (((upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).app A).hom ≫ m) =
      adjX.homEquiv A X.gmSheaf m := by
    change adj.homEquiv A X.gmSheaf ((adj.leftAdjointUniq adjX).hom.app A ≫ m) = _
    rw [adj.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_unit]
  rw [hr]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change adjY.homEquiv A _ (adjG.homEquiv _ _
    ((Etale.upperStar AddCommGrpCat.{u + 1} g).map
      (Y.constantZModToGmSheaf n ζ hζ) ≫ upperStarGmSheafToGmSheaf g)) ≫
    β.hom.app X.gmSheaf = _
  rw [adjG.homEquiv_naturality_left,
    show adjG.homEquiv Y.gmSheaf X.gmSheaf (upperStarGmSheafToGmSheaf g) =
      gmSheafToLowerStarGmSheaf g from (adjG.homEquiv _ _).apply_symm_apply _]
  have hc {Z : Scheme.{u}} (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u + 1})
      (m : Z.constantZMod n ⟶ F) :
      (constantSheafAdj Z.smallEtaleTopology AddCommGrpCat.{u + 1}
        terminalIsTerminal).homEquiv A F m =
      (toSheafify Z.smallEtaleTopology _ ≫ m.hom).app (Opposite.op (⊤_ Z.Etale)) := by
    rw [constantSheafAdj, Adjunction.comp_homEquiv]
    change (constantPresheafAdj AddCommGrpCat.{u + 1} terminalIsTerminal).homEquiv _ _
      ((sheafificationAdjunction Z.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _ m)
        = _
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    rfl
  rw [show adjY = constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal from rfl, hc,
    show adjX = constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal from rfl, hc]
  rw [InducedCategory.comp_hom, ← Category.assoc,
    toSheafify_constantZModToGmSheaf, toSheafify_constantZModToGmSheaf]
  ext a
  obtain ⟨a⟩ := a
  rw [← ZMod.natCast_zmod_val a]
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  let q := (PreservesTerminal.iso g.Etale).inv
  change ((Additive.toMul
    ((X.gmPresheaf.map q.op)
      ((gmSheafToLowerStarGmSheaf g).hom.app (Opposite.op (⊤_ Y.Etale))
        ((Y.zmodToGmPresheaf n ζ hζ).app (Opposite.op (⊤_ Y.Etale))
          (ULift.up (a.val : ZMod n))))).down :
      Γ((⊤_ X.Etale).left, ⊤)ˣ) : Γ((⊤_ X.Etale).left, ⊤)) = _
  rw [gmPresheaf_map_apply]
  change q.left.appTop
      ((pullback.fst (⊤_ Y.Etale).hom g).appTop
        ((Additive.toMul (((Y.zmodToGmPresheaf n ζ hζ).app
          (Opposite.op (⊤_ Y.Etale)) (ULift.up (a.val : ZMod n))).down) :
          Γ((⊤_ Y.Etale).left, ⊤)ˣ) : Γ((⊤_ Y.Etale).left, ⊤))) = _
  erw [Y.zmodToGmPresheaf_app_natCast n ζ hζ _ a.val,
    X.zmodToGmPresheaf_app_natCast n η hη _ a.val]
  rw [map_pow, map_pow]
  apply congrArg (fun x : Γ((⊤_ X.Etale).left, ⊤) ↦ x ^ a.val)
  have hw : q.left ≫ pullback.snd (⊤_ Y.Etale).hom g = (⊤_ X.Etale).hom :=
    MorphismProperty.Over.w q
  have e : q.left ≫ pullback.fst (⊤_ Y.Etale).hom g ≫ (⊤_ Y.Etale).hom =
      (⊤_ X.Etale).hom ≫ g := by
    rw [pullback.condition, ← Category.assoc, hw]
  change (q.left ≫ pullback.fst (⊤_ Y.Etale).hom g ≫ (⊤_ Y.Etale).hom).appTop
    (ζ : Γ(Y, ⊤)) = (⊤_ X.Etale).hom.appTop (η : Γ(X, ⊤))
  rw [e, Hom.comp_appTop, CommRingCat.comp_apply]
  apply congrArg (⊤_ X.Etale).hom.appTop
  exact congrArg Units.val h

end AlgebraicGeometry.Scheme
