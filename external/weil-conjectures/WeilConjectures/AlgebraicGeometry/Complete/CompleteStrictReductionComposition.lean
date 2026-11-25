/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Complete.CompleteStrictPullComposition
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedReductionComparisonPasting
import all WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedReductionPullbackSquare
import all WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement

/-!
# Composition of normalized derived reduction comparisons

Reduction comparisons normalized on good representatives are compatible with composites
of exact functors, whenever the underlying ordinary comparisons are. In particular the
normalized reduction/pullback comparisons are compatible with the inverse-image
compositors.

Source: Weil conjectures blueprint, node proposition-composition-base-change-rf-shriek--4, proof
step 8; Stacks Tags 06YY and 0D6D (blueprint: proposition-composition-base-change-rf-shriek--4).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

section Triangle

variable {BY BY' BX DY DY' DX : Type*}
  [Category BY] [Category BY'] [Category BX] [Category DY] [Category DY'] [Category DX]
  [Abelian BY] [Abelian BY'] [Abelian BX] [Abelian DY] [Abelian DY'] [Abelian DX]
  [HasDerivedCategory BY] [HasDerivedCategory BY'] [HasDerivedCategory BX]
  [HasDerivedCategory DY] [HasDerivedCategory DY'] [HasDerivedCategory DX]
  (Fg : BY ⥤ BY') (Ff : BY' ⥤ BX) (Fh : BY ⥤ BX)
  (Gg : DY ⥤ DY') (Gf : DY' ⥤ DX) (Gh : DY ⥤ DX)
  [Fg.Additive] [Ff.Additive] [Fh.Additive] [Gg.Additive] [Gf.Additive] [Gh.Additive]
  [PreservesFiniteLimits Fg] [PreservesFiniteColimits Fg]
  [PreservesFiniteLimits Ff] [PreservesFiniteColimits Ff]
  [PreservesFiniteLimits Fh] [PreservesFiniteColimits Fh]
  [PreservesFiniteLimits Gg] [PreservesFiniteColimits Gg]
  [PreservesFiniteLimits Gf] [PreservesFiniteColimits Gf]
  [PreservesFiniteLimits Gh] [PreservesFiniteColimits Gh]
  (RY : BY ⥤ DY) (RY' : BY' ⥤ DY') (RX : BX ⥤ DX)
  [RY.Additive] [RY'.Additive] [RX.Additive]
  (MY : DerivedCategory BY ⥤ DerivedCategory DY)
  (MY' : DerivedCategory BY' ⥤ DerivedCategory DY')
  (MX : DerivedCategory BX ⥤ DerivedCategory DX)
  (εY : DerivedCategory.Q ⋙ MY ⟶ RY.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εY' : DerivedCategory.Q ⋙ MY' ⟶ RY'.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
  (εX : DerivedCategory.Q ⋙ MX ⟶ RX.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)

/-- Reduction comparisons normalized on good complexes are compatible with composition,
provided the underlying ordinary comparisons are. The derived compositor `χ` of the source
need only be the localization of the ordinary one on good complexes.
Source: Stacks Tags 06YY and 0D6D (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem derivedReductionTriangle_paste
    (eg : RY ⋙ Gg ≅ Fg ⋙ RY') (ef : RY' ⋙ Gf ≅ Ff ⋙ RX) (eh : RY ⋙ Gh ≅ Fh ⋙ RX)
    (ρg : MY ⋙ Gg.mapDerivedCategory ≅ Fg.mapDerivedCategory ⋙ MY')
    (ρf : MY' ⋙ Gf.mapDerivedCategory ≅ Ff.mapDerivedCategory ⋙ MX)
    (ρh : MY ⋙ Gh.mapDerivedCategory ≅ Fh.mapDerivedCategory ⋙ MX)
    (σ : Fh ≅ Fg ⋙ Ff) (τ : Gh ≅ Gg ⋙ Gf)
    (χ : Fh.mapDerivedCategory ≅ Fg.mapDerivedCategory ⋙ Ff.mapDerivedCategory)
    (good : ObjectProperty (CochainComplex BY ℤ))
    (res : ∀ K, ∃ (P : CochainComplex BY ℤ) (p : P ⟶ K), good P ∧ QuasiIso p)
    (hχ : ∀ P, good P →
      Fh.mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P) =
        χ.hom.app (DerivedCategory.Q.obj P) ≫
          Ff.mapDerivedCategory.map (Fg.mapDerivedCategoryFactors.hom.app P) ≫
          Ff.mapDerivedCategoryFactors.hom.app ((Fg.mapHomologicalComplex (.up ℤ)).obj P))
    (hg : ∀ P, good P → DerivedReductionComparisonFormula Fg Gg RY RY' MY MY'
      (fun P ↦ εY.app P) (fun P ↦ εY'.app P) eg ρg P)
    (hf : ∀ P, good P → DerivedReductionComparisonFormula Ff Gf RY' RX MY' MX
      (fun P ↦ εY'.app P) (fun P ↦ εX.app P) ef ρf ((Fg.mapHomologicalComplex (.up ℤ)).obj P))
    (hh : ∀ P, good P → DerivedReductionComparisonFormula Fh Gh RY RX MY MX
      (fun P ↦ εY.app P) (fun P ↦ εX.app P) eh ρh P)
    (hiso : ∀ P, good P → IsIso (εX.app ((Ff.mapHomologicalComplex (.up ℤ)).obj
      ((Fg.mapHomologicalComplex (.up ℤ)).obj P))))
    (hab : ∀ M : BY, eh.hom.app M ≫ RX.map (σ.hom.app M) =
      τ.hom.app (RY.obj M) ≫ Gf.map (eg.hom.app M) ≫ ef.hom.app (Fg.obj M))
    (K : DerivedCategory BY) :
    ρh.hom.app K ≫ MX.map (χ.hom.app K) =
      (Functor.mapDerivedCategoryTriangleIso' τ).hom.app (MY.obj K) ≫
        Gf.mapDerivedCategory.map (ρg.hom.app K) ≫
        ρf.hom.app (Fg.mapDerivedCategory.obj K) := by
  have key : ∀ P, good P →
      ρh.hom.app (DerivedCategory.Q.obj P) ≫ MX.map (χ.hom.app (DerivedCategory.Q.obj P)) =
        (Functor.mapDerivedCategoryTriangleIso' τ).hom.app
            (MY.obj (DerivedCategory.Q.obj P)) ≫
          Gf.mapDerivedCategory.map (ρg.hom.app (DerivedCategory.Q.obj P)) ≫
          ρf.hom.app (Fg.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) := by
    intro P hP
    have := hiso P hP
    apply (cancel_mono (MX.map (Ff.mapDerivedCategory.map
        (Fg.mapDerivedCategoryFactors.hom.app P) ≫
          Ff.mapDerivedCategoryFactors.hom.app ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        εX.app ((Ff.mapHomologicalComplex (.up ℤ)).obj
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P)))).1
    simp only [Category.assoc]
    -- left-hand side
    have l1 := hχ P hP
    have l2 : MX.map (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P)) ≫
        εX.app ((Ff.mapHomologicalComplex (.up ℤ)).obj
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) =
      εX.app ((Fh.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map ((RX.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P)) :=
      εX.naturality _
    have l3 := hh P hP
    unfold DerivedReductionComparisonFormula at l3
    -- right-hand side
    have r1 : Gf.mapDerivedCategory.map (MY'.map (Fg.mapDerivedCategoryFactors.hom.app P)) ≫
        ρf.hom.app (DerivedCategory.Q.obj ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) =
      ρf.hom.app (Fg.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) ≫
        MX.map (Ff.mapDerivedCategory.map (Fg.mapDerivedCategoryFactors.hom.app P)) :=
      ρf.hom.naturality _
    have r2 := hf P hP
    unfold DerivedReductionComparisonFormula at r2
    have r3 := hg P hP
    unfold DerivedReductionComparisonFormula at r3
    have r3m := congrArg (Gf.mapDerivedCategory.map) r3
    simp only [Functor.map_comp] at r3m
    have r4 : Gf.mapDerivedCategory.map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P)) ≫
        Gf.mapDerivedCategoryFactors.hom.app ((RY'.mapHomologicalComplex (.up ℤ)).obj
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P)) =
      Gf.mapDerivedCategoryFactors.hom.app ((Gg.mapHomologicalComplex (.up ℤ)).obj
          ((RY.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Q.map ((Gf.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P)) :=
      Gf.mapDerivedCategoryFactors.hom.naturality _
    have r5 : Gh.mapDerivedCategory.map (εY.app P) ≫
        (Functor.mapDerivedCategoryTriangleIso' τ).hom.app
          (DerivedCategory.Q.obj ((RY.mapHomologicalComplex (.up ℤ)).obj P)) =
      (Functor.mapDerivedCategoryTriangleIso' τ).hom.app (MY.obj (DerivedCategory.Q.obj P)) ≫
        Gf.mapDerivedCategory.map (Gg.mapDerivedCategory.map (εY.app P)) :=
      (Functor.mapDerivedCategoryTriangleIso' τ).hom.naturality _
    have r6 := Functor.mapDerivedCategoryTriangleIso'_hom_app_factors τ
      ((RY.mapHomologicalComplex (.up ℤ)).obj P)
    have hx : (NatTrans.mapHomologicalComplex eh.hom (.up ℤ)).app P ≫
        (RX.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex σ.hom (.up ℤ)).app P) =
      (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app
          ((RY.mapHomologicalComplex (.up ℤ)).obj P) ≫
        (Gf.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex eg.hom (.up ℤ)).app P) ≫
        (NatTrans.mapHomologicalComplex ef.hom (.up ℤ)).app
          ((Fg.mapHomologicalComplex (.up ℤ)).obj P) := by
      ext n
      exact hab (P.X n)
    have hx' := congrArg DerivedCategory.Q.map hx
    simp only [Functor.map_comp] at hx'
    have l1m := congrArg MX.map l1
    simp only [Functor.map_comp] at l1m
    simp only [Functor.map_comp, Category.assoc]
    rw [← reassoc_of% l1m, l2, reassoc_of% l3, hx', ← reassoc_of% r1, r2, reassoc_of% r3m,
      reassoc_of% r4, ← reassoc_of% r5, ← reassoc_of% r6]
  obtain ⟨P, p, hP, hp⟩ := res (DerivedCategory.Q.objPreimage K)
  have : IsIso (DerivedCategory.Q.map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  let e : DerivedCategory.Q.obj P ≅ K :=
    asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso K
  have n1 := ρh.hom.naturality e.hom
  have n2 := (Functor.mapDerivedCategoryTriangleIso' τ).hom.naturality (MY.map e.hom)
  have n3 := ρg.hom.naturality e.hom
  have n4 := ρf.hom.naturality (Fg.mapDerivedCategory.map e.hom)
  have n5 := χ.hom.naturality e.hom
  dsimp only [Functor.comp_obj, Functor.comp_map] at n1 n2 n3 n4 n5
  rw [← cancel_epi ((MY ⋙ Gh.mapDerivedCategory).map e.hom)]
  dsimp only [Functor.comp_map]
  rw [reassoc_of% n1, ← MX.map_comp, n5, MX.map_comp, reassoc_of% key P hP,
    reassoc_of% n2, ← Gf.mapDerivedCategory.map_comp_assoc, n3, Functor.map_comp,
    Category.assoc, n4]

end Triangle

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

section ReductionComposition

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)

/-- The normalized reduction comparisons are compatible with composition, for any module
compositor whose derived functor is the specified derived compositor.
Source: Stacks Tags 06YY and 0D6D (blueprint: proposition-composition-base-change-rf-shriek--4). -/
theorem reductionTowerPullbackIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (κ : stratumModulePull d (f ≫ g) ≅ stratumModulePull d g ⋙ stratumModulePull d f)
    (hκ : d.pullComp f g = Functor.mapDerivedCategoryTriangleIso' κ) (K : d.derived Z) :
    (d.reductionTowerPullbackIso (f ≫ g)).hom.app K ≫
        (completedReductionTower X d).map ((d.pullComp f g).hom.app K) =
      (Functor.mapDerivedCategoryTriangleIso' (towerCompositor d f g κ)).hom.app
          ((completedReductionTower Z d).obj K) ≫
        (d.towerPull f).map ((d.reductionTowerPullbackIso g).hom.app K) ≫
        (d.reductionTowerPullbackIso f).hom.app ((d.pull g).obj K) := by
  let good : ObjectProperty (CochainComplex (reductionModules Z (d.completedRing Z)) ℤ) :=
    fun P ↦ P.IsKFlatIndependentCoefficients ∧
      ∀ n, SheafOfModules.IsFlatOnSite (J := ProEt.topology Z) (R := d.completedRing Z) (P.X n)
  have res (L : CochainComplex (reductionModules Z (d.completedRing Z)) ℤ) :
      ∃ P, ∃ p : P ⟶ L, good P ∧ QuasiIso p := by
    obtain ⟨P, p, hP, hflat, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (R := d.completedRing Z) L
    exact ⟨P, p, ⟨hP, fun n ↦ (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso (d.completedRing Z) (P.X n)).symm
        (hflat n)⟩, hp⟩
  have hcounit (T : Scheme.{u}) : (fun P ↦ (stratumComplexCounit d T).app P) =
      completedReductionTowerComplexCounit T d := funext (stratumComplexCounit_app d T)
  have spec {U V : Scheme.{u}} (q : U ⟶ V) :
      StratumReductionFormula d q (d.reductionTowerPullbackIso q) :=
    (completedReductionPullbackIso_existsUnique d q).choose_spec.1
  have hf_flat (P) (hP : good P) (n : ℤ) := pullback_flatTerms f g
    (d.completedRing Z) (d.completedRing Y) (d.completedRing X)
    (d.integralRingIso g) (d.integralRingIso f) P hP.1 hP.2 n
  refine derivedReductionTriangle_paste
    (stratumModulePull d g) (stratumModulePull d f) (stratumModulePull d (f ≫ g))
    _ _ _
    (completedReductionModuleTowerFunctor Z d) (completedReductionModuleTowerFunctor Y d)
    (completedReductionModuleTowerFunctor X d)
    (completedReductionTower Z d) (completedReductionTower Y d) (completedReductionTower X d)
    (stratumComplexCounit d Z) (stratumComplexCounit d Y) (stratumComplexCounit d X)
    (stratumModuleReductionIso d g) (stratumModuleReductionIso d f)
    (stratumModuleReductionIso d (f ≫ g))
    (d.reductionTowerPullbackIso g) (d.reductionTowerPullbackIso f)
    (d.reductionTowerPullbackIso (f ≫ g)) κ (towerCompositor d f g κ) (d.pullComp f g)
    good res ?_ ?_ ?_ ?_ ?_ ?_ K
  · intro P _
    rw [hκ]
    exact Functor.mapDerivedCategoryTriangleIso'_hom_app_factors κ P
  · intro P hP
    rw [hcounit, hcounit]
    exact spec g P hP.1
  · intro P hP
    rw [hcounit, hcounit]
    exact spec f _ (stratumPull_flatKFlat d g P hP.1 hP.2)
  · intro P hP
    rw [hcounit, hcounit]
    exact spec (f ≫ g) P hP.1
  · intro P hP
    rw [stratumComplexCounit_app]
    exact towerCounit_isIso X d _ (stratumPull_flatKFlat d f _
      (stratumPull_flatKFlat d g P hP.1 hP.2) (hf_flat P hP))
  · intro M
    apply NatTrans.ext
    funext n
    have := stratumModuleUnit_epi d Z M n.unop
    apply (cancel_epi ((stratumModulePull d (f ≫ g)).map
      (((completedReductionModuleUnit d Z).app M).app n))).1
    simp only [NatTrans.comp_app]
    rw [reassoc_of% (reductionIso_level d (f ≫ g) M n)]
    have hu := NatTrans.congr_app ((completedReductionModuleUnit d X).naturality (κ.hom.app M)) n
    simp only [NatTrans.comp_app, Functor.const_map_app] at hu
    rw [← hu]
    have hκn := κ.hom.naturality (((completedReductionModuleUnit d Z).app M).app n)
    simp only [Functor.comp_map] at hκn
    simp only [towerCompositor, Iso.trans_hom, NatTrans.comp_app, Functor.mapIso_hom,
      Iso.symm_hom, Functor.whiskeringRight_map_app_app, Functor.whiskeringRightObjCompIso,
      Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
    simp only [Iso.refl_inv, NatTrans.id_app]
    erw [Category.comp_id]
    rw [reassoc_of% hκn, ← Functor.map_comp_assoc]
    erw [reductionIso_level d g M n]
    erw [reductionIso_level d f ((stratumModulePull d g).obj M) n]
    rfl


end ReductionComposition

end AlgebraicGeometry.Scheme
