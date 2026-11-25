/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearExchangeCoherence
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateCoefficientComposition

/-! # Composition of compact-support transport with ordered Tate coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek affineLinearBaseCoefficient
  leftDerivedUpperStarComp upperStar Functor.leftDerivedFunctor

private theorem exchange_paste_named
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X X' X'' Y Y' Y'' : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X'']
    [IsNoetherian Y] [IsNoetherian Y'] [IsNoetherian Y'']
    {p : X ⟶ Y} {p' : X' ⟶ Y'} {p'' : X'' ⟶ Y''}
    {v : Y' ⟶ Y} {w : Y'' ⟶ Y'} {v' : X' ⟶ X} {w' : X'' ⟶ X'}
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] [HasCompactification p'] [HasCompactification p'']
    [QuasiCompact p'] [QuasiCompact p'']
    (sq₁ : IsPullback v' p' p v) (sq₂ : IsPullback w' p'' p' w)
    (z : X'' ⟶ X) (c : Y'' ⟶ Y) (hz : z = w' ≫ v') (hc : c = w ≫ v)
    (sq : IsPullback z p'' p c) (K : DerivedCategoryModule A X) :
    (ordinaryFinitePullback A w).map ((rightDerivedLowerShriekBaseChangeMap A sq₁).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq₂).app
          ((ordinaryFinitePullback A v').obj K) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v c hc).inv.app _ ≫
        (rightDerivedLowerShriekBaseChangeMap A sq).app K ≫
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p'').map
          ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w' v' z hz).hom.app K) := by
  subst hz hc
  exact affineLinearExchange_paste A sq₁ sq₂ K

/-- Compact-support exchange over the identity, with ordered coefficient transport. -/
def affineVectorTraceAction (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' B : Scheme.{u}} (p : X ⟶ B) (p' : X' ⟶ B)
    [HasCompactification p] [HasCompactification p'] [QuasiCompact p']
    (v : X' ⟶ X) (sq : IsPullback v p' p (𝟙 B))
    (hX : IsUnit (N : Γ(X, ⊤))) (d : ℕ) :=
  (leftDerivedUpperStarId (ModuleCat.{u + 1} A) B).inv.app _ ≫
    (rightDerivedLowerShriekBaseChangeMap A sq).app (affineLinearBaseCoefficient A N hA X d) ≫
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p').map
      (vectorIntegrationBaseCoefficientPullback A N hA t v hX d).hom

/-- Ordered Tate transport and compact-support exchange compose strictly after
removing identity pullback. This statement contains no integration or trace map.
Source: vector integration, exchange pasting and Tate composition.
(blueprint: lem-pur-affine-vector-trace-action-comp). -/
theorem affineVectorTraceAction_comp (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' X'' B : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian X'] [IsNoetherian X''] [IsNoetherian B]
    (p : X ⟶ B) (p' : X' ⟶ B) (p'' : X'' ⟶ B)
    [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p]
    [HasCompactification p] [HasCompactification p'] [HasCompactification p'']
    [QuasiCompact p'] [QuasiCompact p'']
    (v : X' ⟶ X) (w : X'' ⟶ X')
    (sq : IsPullback v p' p (𝟙 B)) (sq' : IsPullback w p'' p' (𝟙 B))
    (sq'' : IsPullback (w ≫ v) p'' p (𝟙 B))
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X', ⊤))) (d : ℕ) :
    affineVectorTraceAction A N hA t p p' v sq hX d ≫
      affineVectorTraceAction A N hA t p' p'' w sq' hX' d =
    affineVectorTraceAction A N hA t p p'' (w ≫ v) sq'' hX d := by
  let K := affineLinearBaseCoefficient A N hA X d
  let I := leftDerivedUpperStarId (ModuleCat.{u + 1} A) B
  let L' := rightDerivedLowerShriek (ModuleCat.{u + 1} A) p'
  let L'' := rightDerivedLowerShriek (ModuleCat.{u + 1} A) p''
  let c := vectorIntegrationBaseCoefficientPullback A N hA t v hX d
  have hn := I.inv.naturality (L'.map c.hom)
  have he := (rightDerivedLowerShriekBaseChangeMap A sq').naturality c.hom
  have hp := exchange_paste_named A sq sq' (w ≫ v) (𝟙 B) rfl
    (Category.id_comp _).symm sq'' K
  have hc := orderedTateCoefficientComposition A N hA t w v (w ≫ v) rfl hX hX' d
  have hu := leftDerivedUpperStarComp_id_left_hom_app
    (ModuleCat.{u + 1} A) (𝟙 B)
    ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj K)
  have hp' :
      (ordinaryFinitePullback A (𝟙 B)).map
          ((rightDerivedLowerShriekBaseChangeMap A sq).app K) ≫
        (rightDerivedLowerShriekBaseChangeMap A sq').app
          ((ordinaryFinitePullback A v).obj K) =
      I.hom.app _ ≫ (rightDerivedLowerShriekBaseChangeMap A sq'').app K ≫
        L''.map ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A) w v).hom.app K) := by
    have hcomp :
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) (𝟙 B) (𝟙 B) (𝟙 B)
          (Category.id_comp _).symm).inv.app
          ((rightDerivedLowerShriek (ModuleCat.{u + 1} A) p).obj K) = I.hom.app _ := by
      apply (cancel_epi ((leftDerivedUpperStarComp (ModuleCat.{u + 1} A)
        (𝟙 B) (𝟙 B) (𝟙 B) (Category.id_comp _).symm).hom.app _)).mp
      simpa only [Iso.hom_inv_id_app, I] using hu.symm
    simpa only [hcomp, L''] using hp
  unfold affineVectorTraceAction
  simp only [Category.assoc]
  dsimp only [Functor.id_map, Functor.comp_map] at hn he
  rw [reassoc_of% hn, reassoc_of% he]
  have hn' := I.inv.naturality ((rightDerivedLowerShriekBaseChangeMap A sq).app K)
  dsimp only [Functor.id_map] at hn'
  dsimp only [K, I, L', L'', c, ordinaryFinitePullback, Functor.comp_obj]
    at hn' hp' hc ⊢
  rw [reassoc_of% hn', reassoc_of% hp']
  simp only [Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp, hc]

end AlgebraicGeometry.Etale
