/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SpecializationCospecializationArrows
import WeilConjectures.AlgebraicGeometry.Derived.DerivedSpecializationRestriction
import WeilConjectures.AlgebraicGeometry.Closed.ClosedLiftStalkSpecialization

/-! # Fibre maps factor through restriction on the strict-local base

Source: Stacks Project, Tag 0GJV, proof of lemma-specialization-cospecialization.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Fibre-map factorization through strict-local restriction.
Source: Stacks Project, Tag 0GJV, proof of lemma-specialization-cospecialization.
(blueprint: lem-weil-pbc-strict-base-fibre-map-factorization).

Proof plan: Put `K = G[0]` and form the comparison from the derived stalk at `s` to
sections over the strict henselization by the canonical germ restriction, the derived
pullback exchange mate, and Leray. Exactness of strict-local sections identifies this
with the displayed derived morphism. On every affine pointed etale neighbourhood,
the defining equation of the germ restriction says that its composite with the
limit-leg section is restriction of that section. Restricting a representative germ
along the limit leg and then to `t` is exactly the definition of
`derivedEtaleStalkSpecialization`; at the distinguished closed lift the same equation
is the original germ because the point-evaluation map is the closed lift. Naturality
of the derived exchange mate and the global-germ/exchange identity move these
representative equations through the derived comparison. The resulting equations
are equalities of morphisms in the bounded-below derived category, giving the two
conjuncts. This argument uses no local acyclicity, properness, torsion, or
invertibility assertion. -/
theorem strictBaseSheafFiberMap_factorization
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    ∃ a : (Scheme.pointSmallEtale s).sheafFiber.mapDerivedCategoryPlus.obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) ⟶
      (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
        AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1}
              (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj G)),
      (derivedEtaleStalkSpecialization s t).app
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
          strictBaseSheafFiberMap f G s t =
        a ≫ etaleDerivedRestriction (strictBaseFiberInclusion f s t) _ ∧
      a ≫ etaleDerivedRestriction (strictBaseFiberInclusion f s
          (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))) _ =
        closedStrictBaseSheafFiberMap f G s := by
  let a := strictLocalSheafComparison f G s
  have ht (Ω' : Type u) [Field Ω'] [IsAlgClosed Ω']
      (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
      (derivedEtaleStalkSpecialization s t).app
          ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)) ≫
          strictBaseSheafFiberMap f G s t =
        a ≫ etaleDerivedRestriction (strictBaseFiberInclusion f s t) _ := by
    let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G
    let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    let h := strictBaseFiberInclusion f s t
    let H := (Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus
    let e := (Functor.mapDerivedCategoryPlusSingleFunctor
      (upperStar AddCommGrpCat.{u + 1} p) 0).hom.app G
    have hb := derivedFiberMap_restriction f (strictBaseChangeMap f s)
      (Scheme.strictHenselizationStructuralMap s) p
      (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)) t K
    rw [derivedEtaleStalkSpecialization_restriction]
    unfold strictBaseSheafFiberMap strictBaseDerivedFiberMap
    simp only [Category.assoc]
    erw [reassoc_of% hb]
    change _ = a ≫ etaleDerivedRestriction h _
    have hn : etaleDerivedRestriction h
          ((upperStar AddCommGrpCat.{u + 1} p).mapDerivedCategoryPlus.obj K) ≫
        (Sheaf.Γ (pullback (strictBaseChangeMap f s) t).smallEtaleTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
          ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.map e) =
        H.map e ≫ etaleDerivedRestriction h _ := by
      unfold etaleDerivedRestriction
      have hu := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.naturality
        e
      have hl := (etaleLerayPlus h).hom.naturality
        ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.map e)
      simp only [Functor.comp_map, Functor.id_map] at hu hl
      simp only [Category.assoc]
      erw [← hl]
      change H.map _ ≫ H.map _ ≫ _ = H.map e ≫ H.map _ ≫ _
      rw [← H.map_comp_assoc]
      erw [← hu]
      simp only [Functor.map_comp, Category.assoc]
    dsimp only [a, strictLocalSheafComparison]
    simp only [Category.assoc]
    erw [hn]
  refine ⟨a, ht Ω' t, ?_⟩
  have hs := ht Ω
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))
  rw [derivedEtaleStalkSpecialization_closed] at hs
  exact hs.symm

end AlgebraicGeometry.Etale
