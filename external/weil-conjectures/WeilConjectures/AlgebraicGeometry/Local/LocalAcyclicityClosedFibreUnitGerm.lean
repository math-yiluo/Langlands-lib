/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityClosedFibreOrdinaryGerm
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjunctionSingleZero

/-! # The unit map on closed-fibre stalks

## References

* Stacks Project, Tag 0GJU, identification with alpha following the stalk calculation
* Tag 0GJP
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem homology_map_conjugate
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {K T : DerivedCategory.Plus C} (a : K ⟶ T) {M N : C}
    (cK : (DerivedCategory.Plus.homologyFunctor C 0).obj K ≅ M)
    (cT : (DerivedCategory.Plus.homologyFunctor C 0).obj T ≅ N) (b : M ⟶ N)
    (ha : (DerivedCategory.Plus.homologyFunctor C 0).map a ≫ cT.hom = cK.hom ≫ b) :
    (DerivedCategory.Plus.homologyFunctor D 0).map (F.mapDerivedCategoryPlus.map a) ≫
        ((F.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app T ≫ F.map cT.hom) =
      ((F.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app K ≫ F.map cK.hom) ≫
        F.map b := by
  have hn := (F.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.naturality a
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, ha,
    Functor.map_comp, ← Category.assoc]

private theorem map_conjugacy
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
    {X Y X' Y' : C} (a : X ⟶ Y) (b : X' ⟶ Y') (A : X ≅ X') (B : Y ≅ Y')
    (ha : a ≫ B.hom = A.hom ≫ b)
    {Z W : D} (A₀ : F.obj X' ≅ Z) (B₀ : F.obj Y' ≅ W) (c : Z ⟶ W)
    (hb : F.map b ≫ B₀.hom = A₀.hom ≫ c) :
    F.map a ≫ (F.mapIso B ≪≫ B₀).hom = (F.mapIso A ≪≫ A₀).hom ≫ c := by
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← F.map_comp, ha, F.map_comp, Category.assoc, hb,
    ← Category.assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On zeroth cohomology, the closed-fibre stalk of the derived adjunction unit is
conjugate to the canonical map defining local acyclicity. No local acyclicity is assumed. -/
theorem closedFibre_derivedUnit_zero_stalk_comparison
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    {Ξ : Type u} [Field Ξ] [IsAlgClosed Ξ]
    (z : Spec (.of Ξ) ⟶
      pullback (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
        (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))) :
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
    let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
      (Scheme.strictHenselizationRingPointEvaluation s)))
    let h := pullback.fst f' t
    let x := (z ≫ i) ≫ p
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} p).obj G)
    let β := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K
    let a := (Scheme.pointSmallEtale z).sheafFiber.map
      ((DerivedCategory.Plus.homologyFunctor _ 0).map
        ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map β))
    ∃ e : Scheme.strictHenselizationScheme s ≅ Scheme.strictHenselizationScheme (x ≫ f),
      ∃ A : (Scheme.pointSmallEtale z).sheafFiber.obj
          ((DerivedCategory.Plus.homologyFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.obj K)) ≅
          (Scheme.pointSmallEtale x).sheafFiber.obj G,
        ∃ B : (Scheme.pointSmallEtale z).sheafFiber.obj
            ((DerivedCategory.Plus.homologyFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.obj
                (((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus ⋙
                  (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus).obj K))) ≅
            (Sheaf.Γ (localAcyclicityFiber f x (t ≫ e.hom)).smallEtaleTopology
              AddCommGrpCat.{u + 1}).obj
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst (localAcyclicityStrictMap f x) (t ≫ e.hom) ≫
                  Scheme.strictHenselizationStructuralMap x)).obj G),
          a ≫ B.hom = A.hom ≫ localAcyclicityAlpha f x (t ≫ e.hom) G  := by
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
  let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
    (Scheme.strictHenselizationRingPointEvaluation s)))
  let h := pullback.fst f' t
  let M := (upperStar AddCommGrpCat.{u + 1} p).obj G
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj M
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h
  let Fi := upperStar AddCommGrpCat.{u + 1} i
  let Φ := (Scheme.pointSmallEtale z).sheafFiber (A := AddCommGrpCat.{u + 1})
  let u := adj.derivedPlus.unit.app K
  let η := adj.unit.app M
  obtain ⟨e, A₀, B₀, h₀⟩ := closedFibre_unit_stalk_comparison f G s t z
  obtain ⟨c, hc⟩ := adj.derivedPlus_unit_homology_zero M
  let cS := (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).app M
  let eI := Fi.mapDerivedCategoryPlusHomologyFunctorIso 0
  let A := Φ.mapIso ((eI.app K).symm ≪≫ Fi.mapIso cS) ≪≫ A₀
  let T := ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus ⋙
    (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus).obj K
  let B := Φ.mapIso ((eI.app T).symm ≪≫ Fi.mapIso c) ≪≫ B₀
  refine ⟨e, A, B, ?_⟩
  have htrans := homology_map_conjugate Fi u cS c η hc
  exact map_conjugacy Φ _ (Fi.map η) ((eI.app K).symm ≪≫ Fi.mapIso cS)
    ((eI.app T).symm ≪≫ Fi.mapIso c)
    (by simpa only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_inv,
      Functor.id_obj, Functor.comp_obj, eI, T, u, adj, Fi, K, M, h, i, f', p] using htrans)
    A₀ B₀ _ h₀

end AlgebraicGeometry.Etale
