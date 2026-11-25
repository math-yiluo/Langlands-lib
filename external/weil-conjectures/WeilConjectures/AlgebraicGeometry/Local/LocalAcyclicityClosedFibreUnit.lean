/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityAbelianSheaf
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityClosedFibreStalks
import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityClosedFibreUnitGerm
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint

/-!
# Local acyclicity and the closed-fibre restriction of the derived unit

## References

* Stacks Project, Tag 0GJU, specialized to `G[0]`
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

private theorem isIso_of_geometric_cohomology_stalks
    {Y : Scheme.{u}}
    {K L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (a : K ⟶ L)
    (ha : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (z : Spec (.of Ω) ⟶ Y)
      (q : ℤ), IsIso ((Scheme.pointSmallEtale z).sheafFiber.map
        ((DerivedCategory.Plus.homologyFunctor _ q).map a))) : IsIso a := by
  apply (DerivedCategory.Plus.isIso_iff a).2
  intro q
  apply Scheme.isIso_of_isIso_sheafFiber_map
  intro y
  have h := ha _ (Y.algClosurePoint y) q
  exact (NatIso.isIso_map_iff
    ((Scheme.pointSmallEtale (Y.algClosurePoint y)).uliftSheafFiberIso
      AddCommGrpCat.{u + 1}) _).2 h

private theorem isZero_exact_homology
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (K : DerivedCategory.Plus C) (q : ℤ)
    (hK : IsZero ((DerivedCategory.Plus.homologyFunctor C q).obj K)) :
    IsZero ((DerivedCategory.Plus.homologyFunctor D q).obj
      (F.mapDerivedCategoryPlus.obj K)) := by
  exact (F.map_isZero hK).of_iso
    ((F.mapDerivedCategoryPlusHomologyFunctorIso q).app K).symm

/-- For a locally acyclic morphism relative to an abelian étale sheaf, the derived
unit for any geometric fibre over the strict local base becomes an isomorphism
on the closed geometric fibre. No properness or torsion assumption is needed.
-/
theorem isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLocallyAcyclicRelative f G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    IsIso
      ((Functor.mapDerivedCategoryPlus
        (upperStar AddCommGrpCat.{u + 1}
          (pullback.fst (pullback.snd f (Scheme.strictHenselizationStructuralMap s))
            (Spec.map (CommRingCat.ofHom
              (Scheme.strictHenselizationRingPointEvaluation s)))))).map
        ((Adjunction.derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
            (pullback.fst (pullback.snd f (Scheme.strictHenselizationStructuralMap s)) t))).unit.app
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1}
              (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj G)))) := by
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let f' := pullback.snd f (Scheme.strictHenselizationStructuralMap s)
  let i := pullback.fst f' (Spec.map (CommRingCat.ofHom
    (Scheme.strictHenselizationRingPointEvaluation s)))
  let h := pullback.fst f' t
  let G' := (upperStar AddCommGrpCat.{u + 1} p).obj G
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj G'
  let β := (Adjunction.derivedPlus
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h)).unit.app K
  change IsIso ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map β)
  apply isIso_of_geometric_cohomology_stalks
  intro Ξ _ _ z q
  by_cases hq : q = 0
  · subst q
    obtain ⟨e, A, B, hab⟩ := closedFibre_derivedUnit_zero_stalk_comparison f G s t z
    have hi : IsIso (localAcyclicityAlpha f ((z ≫ i) ≫ p) (t ≫ e.hom) G) :=
      (hG _ ((z ≫ i) ≫ p) _ (t ≫ e.hom)).1
    have hcomp : IsIso
        (A.hom ≫ localAcyclicityAlpha f ((z ≫ i) ≫ p) (t ≫ e.hom) G) := inferInstance
    rw [← hab] at hcomp
    exact IsIso.of_isIso_comp_right _ B.hom
  · have hsource := isZero_exact_homology (upperStar AddCommGrpCat.{u + 1} i) K q
      (by
        rcases lt_or_gt_of_ne hq with hq | hq
        · exact DerivedCategory.Plus.isZero_homology_of_isGE K 0 q hq
        · exact DerivedCategory.Plus.isZero_homology_of_isLE K 0 q hq)
    have htarget : IsZero ((Scheme.pointSmallEtale z).sheafFiber.obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj
          ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.obj
            (((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus ⋙
              (lowerStar AddCommGrpCat.{u + 1} h).rightDerivedFunctorPlus).obj K)))) := by
      rcases lt_or_gt_of_ne hq with hq | hq
      · let e : (upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K ≅
            (DerivedCategory.Plus.singleFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1} h).obj G') :=
          ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlusSingleFunctor 0).app G'
        have : ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K).IsGE 0 :=
          DerivedCategory.Plus.TStructure.t.isGE_of_iso e.symm 0
        exact (Scheme.pointSmallEtale z).sheafFiber.map_isZero
          (isZero_exact_homology (upperStar AddCommGrpCat.{u + 1} i) _ q
            (Functor.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
              (lowerStar AddCommGrpCat.{u + 1} h) _ 0 hq))
      · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_lt hq)
        obtain ⟨e, he⟩ := closedFibre_derivedUnit_target_stalks f G s t z
        obtain ⟨E⟩ := he n
        exact ((hG _ ((z ≫ i) ≫ p) _ (t ≫ e.hom)).2 n (by omega)).of_iso E
    exact ⟨⟨0, ((Scheme.pointSmallEtale z).sheafFiber.map_isZero hsource).eq_of_src _ _,
      htarget.eq_of_src _ _⟩⟩

end AlgebraicGeometry.Etale
