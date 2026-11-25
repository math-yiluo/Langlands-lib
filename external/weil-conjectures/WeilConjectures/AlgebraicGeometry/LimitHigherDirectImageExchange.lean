/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageGermDescent
import WeilConjectures.AlgebraicGeometry.CartesianHigherImageGermVanishing

/-! # Degreewise continuity of relative exchange under affine inverse limits

Source: Stacks Project, Tag 0EZT, second assertion, and Tag 0EYM.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

private theorem isIso_homology_pullback {S T : Scheme.{u}} (a : T ⟶ S)
    {P Q : DerivedCategory.Plus (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (m : P ⟶ Q) (n : ℤ)
    (hm : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map m)) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.map m)) := by
  have := hm
  exact (NatIso.isIso_map_iff
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlusHomologyFunctorIso n) m).1
      (by
        change IsIso ((upperStar AddCommGrpCat.{u + 1} a).map
          ((DerivedCategory.Plus.homologyFunctor _ n).map m))
        infer_instance)

private theorem isIso_homology_cartesianDerivedImageMap
    {X S T T' : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) (g' : T' ⟶ S)
    (a : T' ⟶ T) (w : g' = a ≫ g)
    (P : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (n : ℤ)
    (h : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f g).toCommSq).app P)))
    (h' : IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f g').toCommSq).app P))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ n).map
      (cartesianDerivedImageMap f g g' a w P)) := by
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf T'.smallEtaleTopology AddCommGrpCat.{u + 1}) n
  have hpull := isIso_homology_pullback a
    ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
      (IsPullback.of_hasPullback f g).toCommSq).app P) n h
  have := h'
  have hcomp : IsIso (H.map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a g g' w).hom.app
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj P)) ≫
      H.map ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f g).toCommSq).app P)) ≫
      H.map (cartesianDerivedImageMap f g g' a w P)) := by
    rw [← H.map_comp, ← H.map_comp, cartesianDerivedImageMap_exchange]
    exact h'
  have hmid : IsIso (H.map
      ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f g).toCommSq).app P)) ≫
      H.map (cartesianDerivedImageMap f g g' a w P)) :=
    IsIso.of_isIso_comp_left (H.map
      ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} a g g' w).hom.app
        ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj P))) _
  exact IsIso.of_isIso_comp_left
    (H.map ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryPlus.map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f g).toCommSq).app P))) _

/-- In nonnegative degree, canonical exchange passes from the stages to an affine
inverse limit. This assertion concerns a single cohomology sheaf, with arbitrary
abelian coefficients; it has no smoothness, torsion, or injectivity assumption.
Source: Stacks Project, Lemma 59.86.3, Tag 0EZT, second assertion, and
Lemma 59.51.8, Tag 0EYM.
(blueprint: lem-sc-limit-higher-direct-image-exchange)

Proof: Replace I by a cofinal directed inverse system. Pull f back to every D_i;
the resulting sources have affine transition morphisms and limit the pullback of f
to c.pt. The original source and base are constant systems. The coefficient system
is constant F; its colimit is F because I is nonempty and connected. Apply Tag 0EYM
to these systems, including after base change to each descended affine etale object.
Every affine etale object of c.pt descends to a stage. Tag 0EZT identifies the limit
higher-direct-image exchange on that object with the filtered colimit of the
stage exchanges. The given stage maps are isomorphisms, and hence so is their
filtered colimit. These affine etale objects form a basis, so the resulting map
of sheaves is an isomorphism. The exact-inverse-image homology comparison and the
single-complex/right-derived comparison identify this map with the displayed
homology of derivedBaseChangeMapPlus. Compatibility of these comparisons with
transition maps follows from their naturality and the resolution formula for
canonical exchange. The proof works for q = 0, the zero sheaf, and empty X. -/
theorem isIso_limit_homology_derivedBaseChangeMapPlus
    {k : Type u} [Field k]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Over (Spec (.of k)))
    [∀ i, QuasiCompact (D.obj i).hom] [∀ i, QuasiSeparated (D.obj i).hom]
    [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a).left]
    (c : Cone D) (hc : IsLimit ((Over.forget _).mapCone c))
    [QuasiCompact c.pt.hom] [QuasiSeparated c.pt.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ)
    (hstage : ∀ i, IsIso
      ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f (D.obj i).hom).toCommSq).app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f c.pt.hom).toCommSq).app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) := by
  classical
  let P := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let H := DerivedCategory.Plus.homologyFunctor
    (Sheaf c.pt.left.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℤ)
  let α := H.map ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
    (IsPullback.of_hasPullback f c.pt.hom).toCommSq).app P)
  let e (i : I) : _ ⟶ cartesianHigherImageStage D c f F q i := H.map
    ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (c.π.app i).left (D.obj i).hom
        c.pt.hom (Over.w (c.π.app i)).symm).hom.app
          ((lowerStar AddCommGrpCat.{u + 1} f).rightDerivedFunctorPlus.obj P) ≫
      (upperStar AddCommGrpCat.{u + 1} (c.π.app i).left).mapDerivedCategoryPlus.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
          (IsPullback.of_hasPullback f (D.obj i).hom).toCommSq).app P))
  have he (i : I) : IsIso (e i) := by
    have hp := isIso_homology_pullback (c.π.app i).left
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
        (IsPullback.of_hasPullback f (D.obj i).hom).toCommSq).app P) (q : ℤ) (hstage i)
    dsimp only [e]
    rw [H.map_comp]
    have : IsIso (H.map
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app i).left).mapDerivedCategoryPlus.map
          ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1}
            (IsPullback.of_hasPullback f (D.obj i).hom).toCommSq).app P))) := hp
    infer_instance
  have hfac (i : I) : e i ≫ cartesianHigherImageLeg D c f F q i = α := by
    dsimp only [e, cartesianHigherImageLeg, α]
    rw [← H.map_comp, Category.assoc]
    exact congrArg H.map (cartesianDerivedImageMap_exchange f (D.obj i).hom c.pt.hom
      (c.π.app i).left (Over.w (c.π.app i)).symm P)
  have htransition {i j : I} (a : j ⟶ i) :
      IsIso (cartesianHigherImageTransition D c f F q a) := by
    have ht := isIso_homology_cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom
      (D.map a).left (Over.w (D.map a)).symm P (q : ℤ) (hstage i) (hstage j)
    have hp := isIso_homology_pullback (c.π.app j).left
      (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom (D.map a).left
        (Over.w (D.map a)).symm P) (q : ℤ) ht
    dsimp only [cartesianHigherImageTransition]
    rw [Functor.map_comp]
    have hpost : IsIso ((DerivedCategory.Plus.homologyFunctor _ (q : ℤ)).map
        ((upperStar AddCommGrpCat.{u + 1} (c.π.app j).left).mapDerivedCategoryPlus.map
          (cartesianDerivedImageMap f (D.obj i).hom (D.obj j).hom (D.map a).left
            (Over.w (D.map a)).symm ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))) := hp
    exact inferInstanceAs (IsIso
      ((H.mapIso ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1}
        (c.π.app j).left (D.map a).left (c.π.app i).left
        (congrArg (fun b ↦ b.left) (c.w a)).symm).app
          (cartesianDerivedImage f (D.obj i).hom P)) ≪≫
        @asIso _ _ _ _ _ hpost).hom))
  change IsIso α
  apply Scheme.isIso_of_isIso_sheafFiber_map
  intro s
  let T := (c.pt.left.uliftPointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})
  have (i : I) : IsIso (T.map (e i)) := by
    have := he i
    infer_instance
  have {i j : I} (a : j ⟶ i) : IsIso
      (T.map (cartesianHigherImageTransition D c f F q a)) := by
    have := htransition a
    infer_instance
  have hfacT (i : I) : T.map (e i) ≫ T.map (cartesianHigherImageLeg D c f F q i) =
      T.map α := by rw [← T.map_comp, hfac]
  apply (ConcreteCategory.isIso_iff_bijective (T.map α)).2
  constructor
  · apply (injective_iff_map_eq_zero (T.map α).hom).2
    intro x hx
    let i : I := Classical.choice (IsCofiltered.nonempty (C := I))
    have hz : T.map (cartesianHigherImageLeg D c f F q i) (T.map (e i) x) = 0 := by
      rw [← AddCommGrpCat.comp_apply, hfacT]
      exact hx
    obtain ⟨j, a, ha⟩ := exists_cartesianHigherImage_germ_eq_zero D c hc f F q s i
      (T.map (e i) x) hz
    have hy : T.map (e i) x = 0 :=
      (ConcreteCategory.bijective_of_isIso
        (T.map (cartesianHigherImageTransition D c f F q a))).1
          (ha.trans (map_zero _).symm)
    exact (ConcreteCategory.bijective_of_isIso (T.map (e i))).1
      (hy.trans (map_zero _).symm)
  · intro y
    obtain ⟨i, x, hx⟩ := exists_cartesianHigherImage_germ_rep D c hc f F q s y
    obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso (T.map (e i))).2 x
    refine ⟨z, ?_⟩
    rw [← hfacT i, AddCommGrpCat.comp_apply]
    exact (congrArg (fun v ↦ T.map (cartesianHigherImageLeg D c f F q i) v) hz).trans hx

end AlgebraicGeometry.Etale
