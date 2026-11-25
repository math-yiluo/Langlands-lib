/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all Mathlib.Logic.Small.Defs
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import WeilConjectures.CategoryTheory.ShiftedCompositeComparison
/-!
Source: blueprint thm-amb-p1-adjunction.proof.md.
(auxiliary; not a blueprint node).

# Composition of the normalized finite-line comparisons -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero
attribute [local irreducible] upperStar Functor.leftDerivedFunctor Functor.rightDerivedFunctor
/-- Normalization on roots and pure tensors forces the composition law. -/
theorem ordinaryFiniteLinePullback_comp
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (t.line (f ≫ g) hZ).hom =
      (upperStarComp (ModuleCat.{u + 1} A) f g).hom.app
        (Scheme.finiteEtaleTateLine Z N A hA) ≫
      (upperStar (ModuleCat.{u + 1} A) f).map (t.line g hZ).hom ≫ (t.line f hY).hom := by
  obtain ⟨l, hl, _, hcomp⟩ :=
    Scheme.finiteEtaleTateLine_pullback_normalized A N hN hA
  have hr {U V : Scheme.{u}} (v : U ⟶ V) (hV : IsUnit (N : Γ(V, ⊤))) :
      (t.roots v hV).hom = Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf N v := by
    apply (cancel_mono (kernel.ι (N • 𝟙 U.gmSheaf))).mp
    exact (t.roots_normalization v hV).symm.trans
      (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι N v).symm
  let t' : OrdinaryFiniteTwistTransport A N hA :=
    { roots := t.roots
      line := fun {X Y} f hY ↦ @l Y X f hY
      roots_normalization := t.roots_normalization
      line_normalization := by
        intro U V v hV W a z
        dsimp only
        rw [hr]
        exact hl v hV W a z }
  have he := ordinaryFiniteTwistTransport_unique A N hA t t'
  have ht {U V : Scheme.{u}} (v : U ⟶ V) (hV : IsUnit (N : Γ(V, ⊤))) :
      t.line v hV = l v hV := congrArg (fun t₀ ↦ t₀.line v hV) he
  rw [ht, ht, ht]
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc] using
    congrArg Iso.hom (hcomp g f hZ hY)

private theorem compared_composite
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F F₀ : C ⥤ D) (G G₀ : D ⥤ E) (H H₀ : C ⥤ E)
    (eF : F ≅ F₀) (eG : G ≅ G₀) (eH : H ≅ H₀) (c : H₀ ≅ F₀ ⋙ G₀)
    {K : C} {L : D} {M : E}
    (a : F₀.obj K ⟶ L) (b : G₀.obj L ⟶ M) (d : H₀.obj K ⟶ M)
    (h : c.hom.app K ≫ G₀.map a ≫ b = d) :
    (eH ≪≫ c ≪≫ Functor.isoWhiskerRight eF.symm G₀ ≪≫
        Functor.isoWhiskerLeft F eG.symm).hom.app K ≫
      G.map (eF.hom.app K ≫ a) ≫ (eG.hom.app L ≫ b) = eH.hom.app K ≫ d := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  rw [← eG.inv.naturality_assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
  rw [h]

/-- The specified shifted finite-line comparisons preserve inverse-image composition. -/
theorem ordinaryFiniteShiftedLinePullback_comp
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g).hom.app
        ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A f).map
        (ordinaryFiniteShiftedLinePullback A N hA t g hZ).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
        (ordinaryFiniteShiftedLinePullback A N hA t (f ≫ g) hZ).hom := by
  let c := Functor.mapDerivedCategoryNatIso
      (upperStarComp (ModuleCat.{u + 1} A) f g) ≪≫
    (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) g)
      (upperStar (ModuleCat.{u + 1} A) f)).symm
  have : NatTrans.CommShift c.hom ℤ := by
    dsimp only [c, Iso.trans_hom]
    infer_instance
  have h₀ := exactLine₀_comp A f g (f ≫ g) rfl
    (t.line g hZ) (t.line f hY) (t.line (f ≫ g) hZ)
    (ordinaryFiniteLinePullback_comp A N hN hA t f g hZ hY).symm
  have hs := shifted_composite_comparison
    (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) (f ≫ g)).mapDerivedCategory c.hom
    (ordinaryFiniteLine A N hA Z) (ordinaryFiniteLine A N hA Y)
    (ordinaryFiniteLine A N hA X)
    (exactLine₀ A g (t.line g hZ)) (exactLine₀ A f (t.line f hY))
    (exactLine₀ A (f ≫ g) (t.line (f ≫ g) hZ)) h₀ (2 : ℤ)
  have hc : leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g =
      leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (f ≫ g) ≪≫ c ≪≫
        Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).symm
          (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft (ordinaryFinitePullback A g)
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm := by
    apply Iso.ext
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
      c, ordinaryFinitePullback]
  rw [shiftedLine_eq, shiftedLine_eq, shiftedLine_eq, hc]
  apply compared_composite
    (ordinaryFinitePullback A g) (upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory
    (ordinaryFinitePullback A f) (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory
    (ordinaryFinitePullback A (f ≫ g))
    (upperStar (ModuleCat.{u + 1} A) (f ≫ g)).mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) (f ≫ g)) c
    (exactLine A g (t.line g hZ)) (exactLine A f (t.line f hY))
    (exactLine A (f ≫ g) (t.line (f ≫ g) hZ))
  simpa only [exactLine, shiftedHom, ordinaryFiniteLine, ordinaryFiniteDegreeZero,
    ordinaryFiniteSingleFunctor] using hs

/-- The same composition law with a named composite morphism. -/
theorem ordinaryFiniteShiftedLinePullback_comp_of_eq
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app
        ((ordinaryFiniteLine A N hA Z)⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePullback A f).map
        (ordinaryFiniteShiftedLinePullback A N hA t g hZ).hom ≫
      (ordinaryFiniteShiftedLinePullback A N hA t f hY).hom =
        (ordinaryFiniteShiftedLinePullback A N hA t fg hZ).hom := by
  subst hfg
  exact ordinaryFiniteShiftedLinePullback_comp A N hN hA t f g hZ hY

end AlgebraicGeometry.Etale
