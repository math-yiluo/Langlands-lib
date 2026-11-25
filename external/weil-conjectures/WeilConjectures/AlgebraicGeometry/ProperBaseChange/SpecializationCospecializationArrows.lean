/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleStalkSpecialization
public import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationClosedLift
public import WeilConjectures.AlgebraicGeometry.Local.LocalAcyclicityClosedFibreUnit
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.CohomologyPullbackCanonicalArrows

/-!
# Canonical arrows in the specialization--cospecialization diagram

## References

* Stacks Project, Tag 03Q1, exactness of geometric stalks
* Stacks Project, Tag 0GJ2
* Stacks Project, Tag 03Q1 (3)
* Stacks Project, Tags 0GJU and 0GJV
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The coefficient universe admits filtered colimits indexed in the scheme universe. -/
noncomputable instance geometricStalkCoefficientsAB5 : AB5OfSize.{u, u} AddCommGrpCat.{u + 1} :=
  AB5OfSize_shrink.{u, u, u + 1, u + 1} _

/-- The exact geometric fibre functor on abelian sheaves is additive. -/
noncomputable instance geometricSheafFiber_additive
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).Additive :=
  GrothendieckTopology.Point.sheafFiber_additive _

open GrothendieckTopology.Point in
/-- Exact geometric stalks preserve finite limits in the fixed coefficient universe. -/
noncomputable instance geometricSheafFiber_preservesFiniteLimits
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    PreservesFiniteLimits
      ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})) := by
  have : LocallySmall.{u} S.Etale := locallySmall_self _
  exact instPreservesFiniteLimitsSheafSheafFiberOfLocallySmallOfHasFiniteLimitsOfAB5OfSize
    (Φ := Scheme.pointSmallEtale s)

/-- Naturality of the canonical specialization of abelian étale stalks. -/
theorem etaleStalkSpecialization_naturality
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : F ⟶ G) :
    (Scheme.pointSmallEtale s).sheafFiber.map a ≫ etaleStalkSpecialization s t G =
      etaleStalkSpecialization s t F ≫
        (Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.map a :=
  by
  let r : ∀ H : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1},
      (Scheme.pointSmallEtale s).sheafFiber.obj H ⟶
        (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{u + 1}).obj
          ((upperStar AddCommGrpCat.{u + 1}
            (Scheme.strictHenselizationStructuralMap s)).obj H) :=
    fun H ↦ Classical.choose ((strictLocalSectionCone s).existsUnique_restriction H)
  have hr {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}} (a : F ⟶ G) :
      (Scheme.pointSmallEtale s).sheafFiber.map a ≫ r G =
        r F ≫ (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
          AddCommGrpCat.{u + 1}).map
          ((upperStar AddCommGrpCat.{u + 1}
            (Scheme.strictHenselizationStructuralMap s)).map a) := by
    let N := (equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse ⋙
      Scheme.strictHenselizationAffineInclusion s ⋙ ObjectProperty.ι
        (fun n : (Scheme.pointSmallEtale s).fiber.Elements ↦ IsAffine n.1.left)
    have hN : N.Initial := (Scheme.strictHenselization_properties s).1
    let c := ((Scheme.pointSmallEtale s).presheafFiberCocone F.obj).whisker N.op
    let hc : IsColimit c :=
      (Functor.Final.isColimitWhiskerEquiv N.op _).symm
        ((Scheme.pointSmallEtale s).isColimitPresheafFiberCocone F.obj)
    apply hc.hom_ext
    intro j
    have hrF := (Classical.choose_spec
      ((strictLocalSectionCone s).existsUnique_restriction F)).1
    have hrG := (Classical.choose_spec
      ((strictLocalSectionCone s).existsUnique_restriction G)).1
    change (Scheme.pointSmallEtale s).toPresheafFiber
        ((Scheme.AffineEtale.Spec S).obj
          ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
            j.unop).1)
        ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
          j.unop).2 F.obj ≫ _ = _
    erw [← Category.assoc,
      (Scheme.pointSmallEtale s).toPresheafFiber_naturality a.hom, Category.assoc]
    erw [hrG j.unop]
    have hrF' : c.ι.app j ≫ r F = (strictLocalSectionCone s).restriction F j.unop :=
      hrF j.unop
    conv_rhs => rw [← Category.assoc, hrF']
    dsimp only [PointedEtaleSectionCone.restriction]
    simp only [Category.assoc]
    let g := Scheme.strictHenselizationStructuralMap s
    let W := (Scheme.AffineEtale.Spec S).obj
      ((equivSmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
        j.unop).1
    let V := Scheme.Etale.mk (𝟙 (Scheme.strictHenselizationScheme s))
    have hu := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.naturality a
    have he := congrArg (fun b ↦ b.hom.app (Opposite.op W)) hu
    dsimp only [Functor.id_map, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app] at he
    rw [← Category.assoc, ← Category.assoc]
    erw [he]
    simp only [Category.assoc]
    have hn := ((upperStar AddCommGrpCat.{u + 1} g).map a).hom.naturality
      (strictLocalNeighbourhoodSection s j.unop).op
    erw [← reassoc_of% hn]
    have ht := (Sheaf.ΓNatIsoSheafSections _ _
      (IsTerminal.isTerminalOfObj
        (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤
          (Scheme.strictHenselizationScheme s)) V Over.mkIdTerminal)).inv.naturality
      ((upperStar AddCommGrpCat.{u + 1} g).map a)
    change ((upperStar AddCommGrpCat.{u + 1} g).map a).hom.app (Opposite.op V) ≫ _ = _ at ht
    erw [ht]
    rfl
  let e := Functor.whiskerLeft
      (upperStar AddCommGrpCat.{u + 1} (Scheme.strictHenselizationStructuralMap s))
      (globalGerm t) ≫
    (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1}
      (Scheme.strictHenselizationStructuralMap s) t).hom
  change (Scheme.pointSmallEtale s).sheafFiber.map a ≫ (r G ≫ e.app G) =
    (r F ≫ e.app F) ≫
      (Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.map a
  rw [← Category.assoc, hr a, Category.assoc]
  erw [e.naturality]
  rw [Category.assoc]

/-- The natural transformation with the already defined specialization as its components. -/
noncomputable def etaleStalkSpecializationNatTrans
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    (Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1}) ⟶
      (Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber :=
  { app := etaleStalkSpecialization s t
    naturality := fun _ _ a ↦ etaleStalkSpecialization_naturality s t a }

/-- Specialization on bounded below derived stalks, computed termwise since stalks are exact. -/
noncomputable def derivedEtaleStalkSpecialization
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    ((Scheme.pointSmallEtale s).sheafFiber (A := AddCommGrpCat.{u + 1})).mapDerivedCategoryPlus ⟶
      (Scheme.pointSmallEtale
        (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber.mapDerivedCategoryPlus :=
  (Scheme.pointSmallEtale s).sheafFiber.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv ≫
    Functor.rightDerivedFunctorPlusNatTrans (etaleStalkSpecializationNatTrans s t) ≫
    (Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
      ((Scheme.pointSmallEtale (t ≫ Scheme.strictHenselizationStructuralMap s)).sheafFiber
        (A := AddCommGrpCat.{u + 1}))).hom

/-- Inverse image followed by the identity-point stalk computes the original derived stalk. -/
noncomputable def derivedGeometricPointStalkIso
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) :
    (upperStar AddCommGrpCat.{u + 1} s).mapDerivedCategoryPlus ⋙
      (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.mapDerivedCategoryPlus ≅
        (Scheme.pointSmallEtale s).sheafFiber.mapDerivedCategoryPlus :=
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (upperStarCompSheafFiberIso AddCommGrpCat.{u + 1} s (𝟙 (Spec (.of Ω)))) ≪≫
    eqToIso (by rw [Category.id_comp])

/-- Fibre map for a geometric-point square: derived exchange, global sections and Leray.
The inverse global germ on the geometric base identifies the last two operations. -/
noncomputable def etaleDerivedFiberMap
    {X Z S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    {f : X ⟶ S} {k : Z ⟶ X} {q : Z ⟶ Spec (.of Ω)} {s : Spec (.of Ω) ⟶ S}
    (sq : CommSq k q f s)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (Scheme.pointSmallEtale s).sheafFiber.mapDerivedCategoryPlus.obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj K) ⟶
      (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        ((upperStar AddCommGrpCat.{u + 1} k).mapDerivedCategoryPlus.obj K) := by
  letI := isIso_globalGerm_identity Ω
  letI := isIso_derivedGlobalGerm q (𝟙 (Spec (.of Ω)))
  exact (derivedGeometricPointStalkIso s).inv.app _ ≫
    (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).sheafFiber.mapDerivedCategoryPlus.map
      ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq).app K) ≫
    inv ((derivedGlobalGerm q (𝟙 (Spec (.of Ω)))).app _)

/-- The projection of the base change to the strict-local base. -/
noncomputable abbrev strictBaseChangeMap {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :=
  pullback.snd f (Scheme.strictHenselizationStructuralMap s)

/-- The geometric fibre inclusion after strict-local base change. -/
noncomputable abbrev strictBaseFiberInclusion {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :=
  pullback.fst (strictBaseChangeMap f s) t

/-- The fibre map for the outer square, followed by inverse-image composition. -/
noncomputable def strictBaseDerivedFiberMap
    {X S : Scheme.{u}} (f : X ⟶ S)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :=
  etaleDerivedFiberMap
      (CommSq.mk (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
        rfl) : CommSq
        (strictBaseFiberInclusion f s t ≫
          pullback.fst f (Scheme.strictHenselizationStructuralMap s))
        (pullback.snd (strictBaseChangeMap f s) t) f
        (t ≫ Scheme.strictHenselizationStructuralMap s)) K ≫
    (Sheaf.Γ (pullback (strictBaseChangeMap f s) t).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((upperStarCompDerivedPlus AddCommGrpCat.{u + 1} (strictBaseFiberInclusion f s t)
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).hom.app K)

/-- Fibre map with the pulled-back sheaf placed in degree zero on the strict base. -/
noncomputable def strictBaseSheafFiberMap
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :=
  strictBaseDerivedFiberMap f s t ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G) ≫
    (Sheaf.Γ (pullback (strictBaseChangeMap f s) t).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
        ((upperStar AddCommGrpCat.{u + 1}
          (strictBaseFiberInclusion f s t)).mapDerivedCategoryPlus.map
            ((Functor.mapDerivedCategoryPlusSingleFunctor
              (upperStar AddCommGrpCat.{u + 1}
                (pullback.fst f (Scheme.strictHenselizationStructuralMap s))) 0).hom.app G))

/-- The closed fibre map, with its source transported along the canonical lift over `s`. -/
noncomputable def closedStrictBaseSheafFiberMap
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S) :=
  eqToHom (congrArg
      (fun y : Spec (.of Ω) ⟶ S ↦
        (Functor.mapDerivedCategoryPlus
          ((Scheme.pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1}))).obj
        ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} f).obj
          ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj G)))
      (Scheme.strictHenselizationClosedLift_over s).symm) ≫
    strictBaseSheafFiberMap f G s
      (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))

/-- Cospecialization: inverse Leray, restriction to the closed fibre, then inverse closed
fibre unit. Local acyclicity supplies invertibility of precisely this last unit. -/
noncomputable def etaleCospecialization
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : IsLocallyAcyclicRelative f G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    {Ω' : Type u} [Field Ω'] [IsAlgClosed Ω']
    (t : Spec (.of Ω') ⟶ Scheme.strictHenselizationScheme s) :
    (Sheaf.Γ (pullback (strictBaseChangeMap f s) t).smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
        ((upperStar AddCommGrpCat.{u + 1}
          (strictBaseFiberInclusion f s t)).mapDerivedCategoryPlus.obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj G))) ⟶
    (Sheaf.Γ (pullback (strictBaseChangeMap f s)
      (Spec.map (CommRingCat.ofHom
        (Scheme.strictHenselizationRingPointEvaluation s)))).smallEtaleTopology
          AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.obj
      ((upperStar AddCommGrpCat.{u + 1} (strictBaseFiberInclusion f s
        (Spec.map (CommRingCat.ofHom
          (Scheme.strictHenselizationRingPointEvaluation s))))).mapDerivedCategoryPlus.obj
            ((_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
              ((upperStar AddCommGrpCat.{u + 1}
                (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).obj G))) := by
  let p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
  let i := strictBaseFiberInclusion f s
    (Spec.map (CommRingCat.ofHom (Scheme.strictHenselizationRingPointEvaluation s)))
  let h := strictBaseFiberInclusion f s t
  let K := (_root_.DerivedCategory.Plus.singleFunctor _ 0).obj
    ((upperStar AddCommGrpCat.{u + 1} p).obj G)
  let β := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).derivedPlus.unit.app K
  letI := isIso_closedFibre_derivedUnit_of_isLocallyAcyclicRelative f G hG s t
  exact (etaleLerayPlus h).inv.app _ ≫
    etaleDerivedRestriction i ((rightDerivedLowerStarPlus AddCommGrpCat.{u + 1} h).obj
      ((upperStar AddCommGrpCat.{u + 1} h).mapDerivedCategoryPlus.obj K)) ≫
    (Sheaf.Γ _ AddCommGrpCat.{u + 1}).rightDerivedFunctorPlus.map
      (inv ((upperStar AddCommGrpCat.{u + 1} i).mapDerivedCategoryPlus.map β))

end AlgebraicGeometry.Etale
