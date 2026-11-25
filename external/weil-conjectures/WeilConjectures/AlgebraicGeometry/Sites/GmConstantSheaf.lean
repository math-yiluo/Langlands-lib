/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.GmPullback
public import WeilConjectures.ConstructibleSheaf.Defs

/-!
# Maps from constant sheaves to `𝔾ₘ` and pullback

A morphism `const M ⟶ 𝔾ₘ` from a constant étale sheaf of abelian groups to `𝔾ₘ` on `Y` is the
same as a homomorphism `M ⟶ 𝔾ₘ(Y)` (`CategoryTheory.constantSheafAdj`). For `g : X ⟶ Y`, pulling
such a morphism back and composing with the comparison map `g^* 𝔾ₘ ⟶ 𝔾ₘ`
(`AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf`) gives the morphism `const M ⟶ 𝔾ₘ` on `X`
of the composite `M ⟶ 𝔾ₘ(Y) ⟶ 𝔾ₘ(X)` with the pullback of units
(`AlgebraicGeometry.Scheme.upperStar_map_constantSheafAdj_homEquiv_symm_comp`).

## Main definitions

- `AlgebraicGeometry.Scheme.gmSection`: the section of `𝔾ₘ` over the terminal object of `X_ét`
  given by a unit of `Γ(X, 𝒪_X)`.
- `AlgebraicGeometry.Scheme.gmSectionsPullback`: the pullback of sections of `𝔾ₘ` over the
  terminal objects along `g : X ⟶ Y`.

## Main statements

- `AlgebraicGeometry.Scheme.gmSectionsPullback_gmSection`: it is the pullback of units.
- `AlgebraicGeometry.Scheme.upperStar_map_constantSheafAdj_homEquiv_symm_comp`: the
  compatibility above.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- The sections of `𝔾ₘ` over the terminal object of `X_ét`. -/
noncomputable abbrev gmSections (X : Scheme.{u}) : AddCommGrpCat.{u + 1} :=
  ((sheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op (⊤_ X.Etale))).obj
    X.gmSheaf

/-- The section of `𝔾ₘ` over the terminal object of `X_ét` given by a unit `u` of `Γ(X, 𝒪_X)`: the
pullback of `u` along the structure morphism of the terminal object. -/
noncomputable def gmSection (u : Γ(X, ⊤)ˣ) : gmSections X :=
  ULift.up (Additive.ofMul (Units.map (⊤_ X.Etale).hom.appTop.hom.toMonoidHom u))

lemma gmSection_mul (u v : Γ(X, ⊤)ˣ) : gmSection (u * v) = gmSection u + gmSection v := by
  simp only [gmSection, map_mul, ofMul_mul]
  rfl

/-- The pullback of sections of `𝔾ₘ` over the terminal objects along `g : X ⟶ Y`: restriction
along `𝔾ₘ ⟶ g_* 𝔾ₘ`, followed by the identification of the sections of `g_* 𝔾ₘ` over the
terminal object of `Y_ét` with those of `𝔾ₘ` over the terminal object of `X_ét`. -/
noncomputable def gmSectionsPullback (g : X ⟶ Y) : gmSections Y ⟶ gmSections X :=
  ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op (⊤_ Y.Etale))).map
      (gmSheafToLowerStarGmSheaf g) ≫
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g).hom.app X.gmSheaf

/-- The pullback of sections of `𝔾ₘ` over the terminal objects is the pullback of units. -/
lemma gmSectionsPullback_gmSection (g : X ⟶ Y) (u : Γ(Y, ⊤)ˣ) :
    (gmSectionsPullback g).hom (gmSection u) =
      gmSection (Units.map g.appTop.hom.toMonoidHom u) := by
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  change ((PreservesTerminal.iso g.Etale).inv.left).appTop
      ((pullback.fst (⊤_ Y.Etale).hom g).appTop ((⊤_ Y.Etale).hom.appTop (u : Γ(Y, ⊤)))) =
    (⊤_ X.Etale).hom.appTop (g.appTop (u : Γ(Y, ⊤)))
  have h : (PreservesTerminal.iso g.Etale).inv.left ≫ pullback.fst (⊤_ Y.Etale).hom g ≫
      (⊤_ Y.Etale).hom = (⊤_ X.Etale).hom ≫ g := by
    rw [pullback.condition, ← Category.assoc]
    congr 1
    exact MorphismProperty.Over.w (PreservesTerminal.iso g.Etale).inv
  have := congrArg (fun φ ↦ φ.appTop.hom (u : Γ(Y, ⊤))) h
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at this
  exact this

/-- Pulling back a morphism `const M ⟶ 𝔾ₘ` on `Y` given by `ψ : M ⟶ 𝔾ₘ(Y)` and composing with
the comparison map `g^* 𝔾ₘ ⟶ 𝔾ₘ` gives the morphism `const M ⟶ 𝔾ₘ` on `X` given by
`M ⟶ 𝔾ₘ(Y) ⟶ 𝔾ₘ(X)`, through `g^* const M ≅ const M`. -/
lemma upperStar_map_constantSheafAdj_homEquiv_symm_comp (g : X ⟶ Y) {M : AddCommGrpCat.{u + 1}}
    (ψ : M ⟶ gmSections Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).map
        (((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).homEquiv _ _).symm ψ) ≫ upperStarGmSheafToGmSheaf g =
      (upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).hom.app M ≫
        ((constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u + 1}
          terminalIsTerminal).homEquiv _ _).symm (ψ ≫ gmSectionsPullback g) := by
  let adj := ((constantSheafAdj Y.smallEtaleTopology AddCommGrpCat.{u + 1} terminalIsTerminal).comp
      (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)).ofNatIsoRight
    (Etale.lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{u + 1} g)
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, upperStarConstantSheafIso,
    Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app,
    ← Adjunction.homEquiv_unit, Equiv.apply_symm_apply, ← Adjunction.homEquiv_naturality_right]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  simp only [Adjunction.comp_homEquiv]
  erw [Equiv.trans_apply]
  erw [Adjunction.homEquiv_naturality_left]
  rw [
    Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply, upperStarGmSheafToGmSheaf,
    Equiv.apply_symm_apply, gmSectionsPullback, Category.assoc]

end AlgebraicGeometry.Scheme
