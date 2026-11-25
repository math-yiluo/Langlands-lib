/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition

/-! # Graph-normalized unbounded compact-support composition

proof.md`, paragraph 3;
upstream `LowerShriekComposition.lean`, graph constructions in the proofs of
`nonempty_iso_rightDerivedLowerShriekOfCompactification` and
`nonempty_iso_rightDerivedLowerShriek_comp`
(auxiliary; not a blueprint node).

Expose the actual graph constructions as data, without choosing an arbitrary
isomorphism from their existence theorems. The supplied open parts may be non-qc.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Compute compact support through a proper map and a proper/open factorization,
by the two graph embeddings in the product of the proper parts and their open
intersection. This is the construction in upstream `LowerShriekComposition.lean`,
proof of `nonempty_iso_rightDerivedLowerShriekOfCompactification`;
source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3
(auxiliary; not a blueprint node). -/
def sfGraphCompactificationComparison {X Y P U : Scheme.{u}}
    {f : X ⟶ Y} (c : Compactification f) (π : P ⟶ Y) [IsProper π] (e : U ⟶ P)
    [IsOpenImmersion e] (h : X ⟶ U) [IsProper h] (fac : h ≫ e ≫ π = f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ≅
      R((h)_*[ModuleCat.{u + 1} Λ]) ⋙ D((e)_!open[ModuleCat.{u + 1} Λ]) ⋙
        R((π)_*[ModuleCat.{u + 1} Λ]) := by
  let 𝔸 := ModuleCat.{u + 1} Λ
  let p₁ := pullback.fst π c.g
  let p₂ := pullback.snd π c.g
  have : IsProper p₁ := MorphismProperty.pullback_fst _ _ c.isProper
  have : IsProper p₂ := MorphismProperty.pullback_snd _ _ ‹IsProper π›
  let ι : X ⟶ pullback π c.g := pullback.lift (h ≫ e) c.i (by
    rw [Category.assoc, fac]; exact c.comm)
  -- the graph of `X` in `P ×_Y X`, open in `P ×_Y Z`
  let a₁ := pullback.fst p₂ c.i
  let s₁ := pullback.snd p₂ c.i
  have : IsSeparated s₁ := MorphismProperty.pullback_snd _ _ inferInstance
  let Γ₁ : X ⟶ pullback p₂ c.i := pullback.lift ι (𝟙 X) (by simp [ι, p₂])
  have : IsProper (Γ₁ ≫ s₁) := by rw [show Γ₁ ≫ s₁ = 𝟙 X from pullback.lift_snd _ _ _]
                                  infer_instance
  have : IsProper Γ₁ := IsProper.of_comp Γ₁ s₁
  -- `X` in `U ×_Y Z`, open in `P ×_Y Z`
  let a₂ := pullback.fst p₁ e
  let s₂ := pullback.snd p₁ e
  have : IsSeparated s₂ := MorphismProperty.pullback_snd _ _ inferInstance
  let h₂ : X ⟶ pullback p₁ e := pullback.lift ι h (by simp [ι, p₁])
  have : IsProper (h₂ ≫ s₂) := by rw [show h₂ ≫ s₂ = h from pullback.lift_snd _ _ _]
                                  infer_instance
  have : IsProper h₂ := IsProper.of_comp h₂ s₂
  -- the intersection of the two opens
  let b₁ := pullback.fst a₁ a₂
  let b₂ := pullback.snd a₁ a₂
  let γ : X ⟶ pullback a₁ a₂ := pullback.lift Γ₁ h₂ (by simp [Γ₁, h₂, a₁, a₂])
  let eΓ : R((γ)_*[𝔸]) ⋙ D((b₁)_!open[𝔸]) ≅ R((Γ₁)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ γ b₁ Γ₁ (pullback.lift_fst _ _ _)
  let eh : R((γ)_*[𝔸]) ⋙ D((b₂)_!open[𝔸]) ≅ R((h₂)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ γ b₂ h₂ (pullback.lift_snd _ _ _)
  -- the two extensions by zero agree
  let eC : R((Γ₁)_*[𝔸]) ⋙ D((a₁)_!open[𝔸]) ≅ R((h₂)_*[𝔸]) ⋙ D((a₂)_!open[𝔸]) :=
    Functor.isoWhiskerRight eΓ.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 b₁ a₁).symm ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekCongr 𝔸 pullback.condition ≪≫
          mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 b₂ a₂) ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eh _
  -- the side of `c`
  let eA : Rf_!(c)[𝔸] ≅ R((Γ₁)_*[𝔸]) ⋙ D((a₁)_!open[𝔸]) ⋙ R((p₁ ≫ π)_*[𝔸]) :=
    (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerRight ((rightDerivedLowerStarIdIso Λ X).symm ≪≫
        (rightDerivedLowerStarCompOfEq 𝔸 Γ₁ s₁ (𝟙 X) (pullback.lift_snd _ _ _)).symm) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso Λ
          (IsPullback.of_hasPullback p₂ c.i).flip) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq 𝔸 p₂ c.g (p₁ ≫ π)
          pullback.condition.symm))
  -- the side of `π`
  let eB : R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((π)_*[𝔸]) ≅
      R((h₂)_*[𝔸]) ⋙ D((a₂)_!open[𝔸]) ⋙ R((p₁ ≫ π)_*[𝔸]) :=
    Functor.isoWhiskerRight (rightDerivedLowerStarCompOfEq 𝔸 h₂ s₂ h
        (pullback.lift_snd _ _ _)).symm _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso Λ
          (IsPullback.of_hasPullback p₁ e).flip) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq 𝔸 p₁ π (p₁ ≫ π) rfl))
  exact eA ≪≫ (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight eC _ ≪≫
    Functor.associator _ _ _ ≪≫ eB.symm

/-- The graph-normalized compositor for three supplied compactifications.
Source: blueprint `thm-asd-smooth-tensor.proof.md`, paragraph 3; upstream
`LowerShriekComposition.lean`, proof of `nonempty_iso_rightDerivedLowerShriek_comp`.
Compute both sides in the product of the proper parts, restrict to its open over Y,
and interchange proper direct image and open extension. No closure or qc hypothesis
is used (auxiliary; not a blueprint node). -/
def sfGraphCompactSupportCompIso {X Y T : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ T) (cf : Compactification f) (cg : Compactification g)
    (cfg : Compactification (f ≫ g)) :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cfg ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cf ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} Λ) cg := by
  let 𝔸 := ModuleCat.{u + 1} Λ
  -- `P = V ×_T W`
  let φ := pullback.fst cfg.g cg.g
  let ψ := pullback.snd cfg.g cg.g
  have : IsProper φ := MorphismProperty.pullback_fst _ _ cg.isProper
  have : IsProper ψ := MorphismProperty.pullback_snd _ _ cfg.isProper
  -- `X` in the open `P ×_V X` of `P`
  let e := pullback.fst φ cfg.i
  let σ := pullback.snd φ cfg.i
  have : IsSeparated σ := MorphismProperty.pullback_snd _ _ inferInstance
  have w₁ : cfg.i ≫ cfg.g = (f ≫ cg.i) ≫ cg.g := by
    rw [← cfg.comm, Category.assoc, ← cg.comm]
  let h : X ⟶ pullback φ cfg.i :=
    pullback.lift (pullback.lift cfg.i (f ≫ cg.i) w₁) (𝟙 X) (by simp [φ])
  have : IsProper (h ≫ σ) := by rw [show h ≫ σ = 𝟙 X from pullback.lift_snd _ _ _]
                                infer_instance
  have : IsProper h := IsProper.of_comp h σ
  have he : h ≫ e = pullback.lift cfg.i (f ≫ cg.i) w₁ := pullback.lift_fst _ _ _
  let e₁ := sfGraphCompactificationComparison Λ cfg (ψ ≫ cg.g) e h
    (by rw [reassoc_of% he, pullback.lift_snd_assoc, Category.assoc, ← cg.comm])
  -- `P ×_W Y`, open in `P` and proper over `Y`
  let eY := pullback.fst ψ cg.i
  let πY := pullback.snd ψ cg.i
  have : IsProper πY := MorphismProperty.pullback_snd _ _ inferInstance
  let uY := pullback.fst e eY
  let e' := pullback.snd e eY
  let ρ : X ⟶ pullback ψ cg.i := pullback.lift (h ≫ e) f (by rw [he]; simp [ψ])
  let h' : X ⟶ pullback e eY := pullback.lift h ρ (by simp [ρ, eY])
  have : IsProper (h' ≫ uY) := by rw [show h' ≫ uY = h from pullback.lift_fst _ _ _]
                                  infer_instance
  have : IsProper h' := IsProper.of_comp h' uY
  let e₂ := sfGraphCompactificationComparison Λ cf πY e' h'
    (by simp [h', e', ρ, πY])
  let eh : R((h')_*[𝔸]) ⋙ D((uY)_!open[𝔸]) ≅ R((h)_*[𝔸]) :=
    rightDerivedLowerStarCompOpenImmersionLowerShriekIso Λ h' uY h (pullback.lift_fst _ _ _)
  let ex : R((πY)_*[𝔸]) ⋙ D((cg.i)_!open[𝔸]) ≅ D((eY)_!open[𝔸]) ⋙ R((ψ)_*[𝔸]) :=
    openImmersionLowerShriekLowerStarExchangeIso Λ (IsPullback.of_hasPullback ψ cg.i).flip
  let e₃ : R((h)_*[𝔸]) ⋙ D((e)_!open[𝔸]) ⋙ R((ψ ≫ cg.g)_*[𝔸]) ≅
      (R((h')_*[𝔸]) ⋙ D((e')_!open[𝔸]) ⋙ R((πY)_*[𝔸])) ⋙ D((cg.i)_!open[𝔸]) ⋙
        R((cg.g)_*[𝔸]) :=
    Functor.isoWhiskerRight eh.symm _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight
          ((mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 uY e).symm ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekCongr 𝔸 pullback.condition ≪≫
            mapDerivedCategoryOpenImmersionLowerShriekComp 𝔸 e' eY) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
            (rightDerivedLowerStarCompOfEq 𝔸 ψ cg.g _ rfl).symm ≪≫
          (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight ex.symm _ ≪≫
          Functor.associator _ _ _)) ≪≫
      Functor.isoWhiskerLeft _ (Functor.associator _ _ _).symm ≪≫
      (Functor.associator _ _ _).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
      Functor.associator _ _ _
  exact e₁ ≪≫ e₃ ≪≫ Functor.isoWhiskerRight e₂.symm _

end AlgebraicGeometry.Etale
