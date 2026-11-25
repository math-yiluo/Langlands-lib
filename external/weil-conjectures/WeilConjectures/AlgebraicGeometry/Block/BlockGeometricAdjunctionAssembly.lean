/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.System.SystemBlockConstructions
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearOrdinaryDirectSystem

/-! # Assembly of the repeated ordinary geometric adjunction

Source: Zheng Construction 4.1 and the paragraph preceding Lemma 4.10.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe c v r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ u h
open CategoryTheory CategoryTheory.Limits Opposite
namespace WeilConjectures.SemilinearSections

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) (t : SystemBlockMap)
  {C' : Type c} [Category.{v} C'] [EssentiallySmall.{max c v r} C']
  (J' : GrothendieckTopology C')
  (B₀ : ℕ → Sheaf J CommRingCat.{max c v r}) (τ₀ : ∀ n, B₀ (n + 1) ⟶ B₀ n)
  (A : Data.{c, v, r} J B₀ τ₀)
  (uInv : Sheaf J (Type (max c v r)) ⥤ Sheaf J' (Type (max c v r)))
  (uPush : Sheaf J' (Type (max c v r)) ⥤ Sheaf J (Type (max c v r)))
  (adjSet : uInv ⊣ uPush)
  (G : Geometry.{c, v, r} J B₀ τ₀ A J' uInv uPush adjSet)
  (RX : SystemBlockRepetition J' G.coefficients G.coefficientTransition t)
  (RY : SystemBlockRepetition J B₀ τ₀ t)
  (P : OrdinaryInverseSystem.{c, v, r}
    J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) J' uInv
    (blockCoefficients G.coefficients t)
    (blockTransitions J' G.coefficients G.coefficientTransition t)
    (fun m ↦ G.inverseImage (t.index m)))
  (K : OrdinaryDirectSystemCore.{c, v, r}
    J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) J' uInv
    (blockCoefficients G.coefficients t)
    (blockTransitions J' G.coefficients G.coefficientTransition t)
    (fun m ↦ G.inverseImage (t.index m)) P
    (fun m ↦ G.levelPush (t.index m)) (fun m ↦ G.levelAdjunction (t.index m)))
  (δ : G.pull ⋙ RX.repetition ≅ RY.repetition ⋙ P.pull)
  (s : RX.repetition ⋙ K.push ≅ G.push ⋙ RY.repetition)
  (hp : ∀ (M : Systems J B₀ τ₀) (m : ℕ),
    (evaluation J' (blockCoefficients G.coefficients t)
        (blockTransitions J' G.coefficients G.coefficientTransition t) m).map (δ.hom.app M) ≫
      (P.component m).hom.app (RY.repetition.obj M) ≫
      (G.inverseImage (t.index m)).modules.map ((RY.evaluation m).hom.app M) =
    (RX.evaluation m).hom.app (G.pull.obj M) ≫
      (G.ordinaryPullEvaluation (t.index m)).hom.app M)
  (hq : ∀ (N : Systems J' G.coefficients G.coefficientTransition) (m : ℕ),
    (evaluation J (blockCoefficients B₀ t) (blockTransitions J B₀ τ₀ t) m).map (s.hom.app N) ≫
      (RY.evaluation m).hom.app (G.push.obj N) ≫
      (G.ordinaryPushEvaluation (t.index m)).hom.app N =
    (K.component m).hom.app (RX.repetition.obj N) ≫
      (G.levelPush (t.index m)).map ((RX.evaluation m).hom.app N))

include hp hq

attribute [local irreducible] evaluation systemRing ringPresheaf rings

end WeilConjectures.SemilinearSections
