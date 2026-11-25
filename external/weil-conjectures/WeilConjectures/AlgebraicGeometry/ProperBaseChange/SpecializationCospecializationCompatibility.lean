/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpecializationCospecializationArrows
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Strict.StrictBaseFibreMapFactorization
import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityClosedFibreUnit

/-!
# Specialization and cospecialization commute with fibre maps

## References

* Stacks Project, Tag 0GJV, specialized to `G[0]`
* Stacks Project, Tag 0GJV, `K = G[0]`
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
private lemma etaleDerivedRestriction_naturality
    {Y Z : Scheme.{u}} (v : Z ⟶ Y)
    {K L : _root_.DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})} (a : K ⟶ L) :
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map a ≫
        etaleDerivedRestriction v L =
      etaleDerivedRestriction v K ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((upperStar AddCommGrpCat.{u + 1} v).mapDerivedCategoryPlus.map a) := by
  have hu := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} v).derivedPlus.unit.naturality a
  dsimp only [Functor.id_map, Functor.comp_map] at hu
  unfold etaleDerivedRestriction
  rw [← Functor.map_comp_assoc, hu, Functor.map_comp_assoc]
  have hl := (etaleLerayPlus v).hom.naturality
    ((upperStar AddCommGrpCat.{u + 1} v).mapDerivedCategoryPlus.map a)
  dsimp only [Functor.comp_map] at hl
  rw [Category.assoc, hl]

private lemma restriction_cancel_unit
    {Y Z W : Scheme.{u}} (i : Z ⟶ Y) (h : W ⟶ Y)
    (K : _root_.DerivedCategory.Plus
      (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}))
    [IsIso ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K))] :
    etaleDerivedRestriction h K ≫
      ((etaleLerayPlus h).inv.app _ ≫ etaleDerivedRestriction i _ ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          (inv ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K)))) =
      etaleDerivedRestriction i K := by
  conv_lhs => lhs; unfold etaleDerivedRestriction
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have hn := etaleDerivedRestriction_naturality i
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K)
  have hn' :
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K) ≫
        etaleDerivedRestriction i
          ((h)_*[AddCommGrpCat.{u + 1}].rightDerivedFunctorPlus.obj
            ((h)^*[AddCommGrpCat.{u + 1}].mapDerivedCategoryPlus.obj K)) =
      etaleDerivedRestriction i K ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K)) := by
    simpa only [Functor.id_obj, Functor.comp_obj] using hn
  calc
    _ = etaleDerivedRestriction i K ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K)) ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          (inv ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K))) :=
      (by simpa only [Category.assoc] using congrArg (fun z ↦ z ≫
        (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          (inv ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map
            ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K)))) hn')
    _ = etaleDerivedRestriction i K := by
      simp only [← Functor.map_comp, IsIso.hom_inv_id]
      simp

set_option backward.isDefEq.respectTransparency false in
private lemma restriction_cospecialization
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLocallyAcyclicRelative f G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    etaleDerivedRestriction (strictBaseFiberInclusion f s t)
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1}
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj G)) ≫
      etaleCospecialization f G hG s t =
    etaleDerivedRestriction (strictBaseFiberInclusion f s
      (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s))))
        ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
          ((upperStar AddCommGrpCat.{u + 1}
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj G)) := by
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let i := strictBaseFiberInclusion f s
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))
  let h := strictBaseFiberInclusion f s t
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} p).obj G)
  let β := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K
  have := isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative f G hG s t
  exact restriction_cancel_unit i h K

/-- Specialization, the canonical fibre maps and cospecialization form a commutative
square in the bounded below derived category of abelian groups. The geometric point
`t` is arbitrary, including the distinguished closed-point lift. There is no properness
or torsion assumption and no invertibility assertion about the arrows in the square. -/
theorem specialization_cospecialization_compatibility
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLocallyAcyclicRelative f G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    (derivedEtaleStalkSpecialization s t).app
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
      strictBaseSheafFiberMap f G s t ≫ etaleCospecialization f G hG s t =
        closedStrictBaseSheafFiberMap f G s := by
  obtain ⟨a, ht, hs⟩ := strictBaseSheafFiberMap_factorization f G s t
  rw [← Category.assoc, ht, Category.assoc, restriction_cospecialization f G hG s t]
  exact hs

end AlgebraicGeometry.Etale
