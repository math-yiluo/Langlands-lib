/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernPullbackData
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TowerReductionMateInvertible
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernIntegralNormalizations
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerPullbackTranspose

/-! # Pullback of integral reduction to the quotient tower

Source: blueprint classes proof (2), realization steps 2--4, before extension to E
(blueprint: lem-sp-tower-chern-reduction-pullback).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option Elab.async false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local implicit_reducible] HomotopyCategory.singleFunctors

section
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
  (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ C) (I : C ⥤ D)
  [F.Additive] [G.Additive] [H.Additive] [I.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits I] [PreservesFiniteColimits I]
private theorem square_factors (e : F ⋙ G ≅ H ⋙ I) (K : CochainComplex A ℤ) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app K) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [CategoryTheory.Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  erw [CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors,
    CategoryTheory.Functor.mapDerivedCategoryNatIso_fac]
  rw [← CategoryTheory.Functor.mapDerivedCategoryCompIso_hom_app_factors F G K]
  erw [Category.assoc, Iso.hom_inv_id_app_assoc]
  exact Category.assoc _ _ _

private theorem single_factors (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (X : A) :
    (F.mapDerivedCategorySingleFunctor 0).hom.app X =
      F.mapDerivedCategoryFactors.hom.app
        ((HomologicalComplex.single A (.up ℤ) 0).obj X) ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X) := by
  erw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X]
  erw [Iso.hom_inv_id_app_assoc]

private theorem square_single (e : F ⋙ G ≅ H ⋙ I) (X : A) :
    (CategoryTheory.Functor.mapDerivedCategorySquareIso e).hom.app
        ((DerivedCategory.singleFunctor A 0).obj X) ≫
      I.mapDerivedCategory.map ((H.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (I.mapDerivedCategorySingleFunctor 0).hom.app (H.obj X) =
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).hom.app X) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app (F.obj X) ≫
      (DerivedCategory.singleFunctor D 0).map (e.hom.app X) := by
  let K := (HomologicalComplex.single A (.up ℤ) 0).obj X
  let cF := HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0
  let cG := HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0
  let cH := HomologicalComplex.singleMapHomologicalComplex H (.up ℤ) 0
  let cI := HomologicalComplex.singleMapHomologicalComplex I (.up ℤ) 0
  let ec := NatIso.mapHomologicalComplex e (.up ℤ)
  have hc : ec.hom.app K ≫ (I.mapHomologicalComplex (.up ℤ)).map (cH.hom.app X) ≫
      cI.hom.app (H.obj X) =
      (G.mapHomologicalComplex (.up ℤ)).map (cF.hom.app X) ≫ cG.hom.app (F.obj X) ≫
        (HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X) := by
    apply HomologicalComplex.Hom.ext
    funext i
    by_cases hi : i = 0
    · subst i
      simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
        ec, NatIso.mapHomologicalComplex, NatTrans.mapHomologicalComplex_app_f,
        HomologicalComplex.single_map_f_self, cF, cG, cH, cI,
        HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        CategoryTheory.Functor.map_comp, Category.assoc]
      simp only [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
        CategoryTheory.Functor.map_id, Category.id_comp,
        Iso.inv_hom_id_assoc]
      simpa only [K, CategoryTheory.Functor.comp_map, Category.assoc] using!
        congrArg (fun z ↦ z ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 ((H ⋙ I).obj X)).inv)
          (e.hom.naturality (HomologicalComplex.singleObjXSelf (.up ℤ) 0 X).hom).symm
    · exact ((F ⋙ G).map_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 X i hi)).eq_of_src _ _
  rw [single_factors H X, single_factors I (H.obj X), single_factors F X,
    single_factors G (F.obj X)]
  change (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      I.mapDerivedCategory.map
        (H.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (cH.hom.app X)) ≫
      (I.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C (.up ℤ) 0).obj (H.obj X)) ≫
        DerivedCategory.Q.map (cI.hom.app (H.obj X))) =
    G.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map (cF.hom.app X)) ≫
      (G.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single B (.up ℤ) 0).obj (F.obj X)) ≫
        DerivedCategory.Q.map (cG.hom.app (F.obj X))) ≫
      DerivedCategory.Q.map ((HomologicalComplex.single D (.up ℤ) 0).map (e.hom.app X))
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  erw [I.mapDerivedCategoryFactors.hom.naturality_assoc (cH.hom.app X)]
  erw [reassoc_of% (square_factors F G H I e K)]
  erw [G.mapDerivedCategoryFactors.hom.naturality_assoc (cF.hom.app X)]
  congr 2
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ = DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _
  simp only [← CategoryTheory.Functor.map_comp]
  exact DerivedCategory.Q.congr_map hc
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  {L : A ⥤ B} {R : B ⥤ A} {L' : A' ⥤ B'} {R' : B' ⥤ A'}
  (a : L ⊣ R) (a' : L' ⊣ R') (F : A ⥤ A') (G : B ⥤ B')
  (ρ : R ⋙ F ≅ G ⋙ R') (θ : L ⋙ G ≅ F ⋙ L')
  (hθ : ∀ X, a'.unit.app (F.obj X) ≫ R'.map (θ.inv.app X) =
    F.map (a.unit.app X) ≫ ρ.hom.app (L.obj X))
include hθ in
private theorem normalized_exchange
    (X : A) (X' : A') (Y : B) (Y' : B') (d : F.obj X ⟶ X') (g : G.obj Y ⟶ Y')
    (i : L.obj X ⟶ Y) (i' : L'.obj X' ⟶ Y')
    (f : X ⟶ R.obj Y) (f' : X' ⟶ R'.obj Y')
    (hi : a.unit.app X ≫ R.map i = f) (hi' : a'.unit.app X' ≫ R'.map i' = f')
    (hf : F.map f ≫ ρ.hom.app Y ≫ R'.map g = d ≫ f') :
    G.map i ≫ g = θ.hom.app X ≫ L'.map d ≫ i' := by
  apply (cancel_epi (θ.inv.app X)).1
  simp only [Iso.inv_hom_id_app_assoc]
  apply (a'.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, hθ]
  simp only [Category.assoc]
  rw [← reassoc_of% (ρ.hom.naturality i)]
  rw [← F.map_comp_assoc, hi]
  rw [hf]
  rw [← reassoc_of% (a'.unit.naturality d), hi']
end

section
variable {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
  [Abelian A] [Abelian B] [Abelian A'] [Abelian B']
  [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory A'] [HasDerivedCategory B']
  (R : B ⥤ A) (F : A ⥤ A') (G : B ⥤ B') (R' : B' ⥤ A')
  [R.Additive] [F.Additive] [G.Additive] [R'.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits R'] [PreservesFiniteColimits R']
  (ρ : R ⋙ F ≅ G ⋙ R')
private theorem single_normalized_square
    (Z : A) (Z' : A') (Y : B) (Y' : B')
    (q : Z ⟶ R.obj Y) (q' : Z' ⟶ R'.obj Y')
    (d : F.obj Z ⟶ Z') (g : G.obj Y ⟶ Y')
    (t : (DerivedCategory.singleFunctor A 0).obj Z ⟶
      R.mapDerivedCategory.obj ((DerivedCategory.singleFunctor B 0).obj Y))
    (t' : (DerivedCategory.singleFunctor A' 0).obj Z' ⟶
      R'.mapDerivedCategory.obj ((DerivedCategory.singleFunctor B' 0).obj Y'))
    (ht : t ≫ (R.mapDerivedCategorySingleFunctor 0).hom.app Y =
      (DerivedCategory.singleFunctor A 0).map q)
    (ht' : t' ≫ (R'.mapDerivedCategorySingleFunctor 0).hom.app Y' =
      (DerivedCategory.singleFunctor A' 0).map q')
    (hq : F.map q ≫ ρ.hom.app Y ≫ R'.map g = d ≫ q')
    (dD : F.mapDerivedCategory.obj ((DerivedCategory.singleFunctor A 0).obj Z) ⟶
      (DerivedCategory.singleFunctor A' 0).obj Z')
    (gD : G.mapDerivedCategory.obj ((DerivedCategory.singleFunctor B 0).obj Y) ⟶
      (DerivedCategory.singleFunctor B' 0).obj Y')
    (hd : dD = (F.mapDerivedCategorySingleFunctor 0).hom.app Z ≫
      (DerivedCategory.singleFunctor A' 0).map d)
    (hg : gD = (G.mapDerivedCategorySingleFunctor 0).hom.app Y ≫
      (DerivedCategory.singleFunctor B' 0).map g) :
    F.mapDerivedCategory.map t ≫
        (Functor.mapDerivedCategorySquareIso ρ).hom.app
          ((DerivedCategory.singleFunctor B 0).obj Y) ≫
        R'.mapDerivedCategory.map gD = dD ≫ t' := by
  rw [hd, hg]
  apply (cancel_mono ((R'.mapDerivedCategorySingleFunctor 0).hom.app Y')).1
  simp only [Category.assoc]
  rw [ht']
  simp only [Functor.map_comp, Category.assoc]
  erw [(R'.mapDerivedCategorySingleFunctor 0).hom.naturality g]
  erw [reassoc_of% (square_single R F G R' ρ Y)]
  rw [← F.mapDerivedCategory.map_comp_assoc, ht]
  erw [reassoc_of% (F.mapDerivedCategorySingleFunctor 0).hom.naturality q]
  simp only [Functor.comp_map, ← Functor.map_comp]
  rw [hq]
end

attribute [local irreducible] HasDerivedCategory.standard DerivedCategory.singleFunctors
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

open Opposite WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem integer_comparison {X Y : Scheme.{u}} (f : X ⟶ Y) :
    integerDerivedPull f =
      ((abPull f).mapDerivedCategorySingleFunctor 0).hom.app (integers Y) ≫
        (DerivedCategory.singleFunctor (Ab X) 0).map (integerPull f) := by rfl

private theorem unit_comparison
    {X Y : Scheme.{u}} {f : X ⟶ Y} {cY : Chern l E Y} {cX : Chern l E X}
    (d : IntegralCoefficientPullback l E f cY cX) :
    d.derivedUnit.hom =
      (d.pull.mapDerivedCategorySingleFunctor 0).hom.app (coefficient Y (Rrings l Y)) ≫
        (DerivedCategory.singleFunctor (Systems X (Rrings l X)) 0).map d.unitIso.hom := by
  rfl

private theorem source_normalization {T : Scheme.{u}} (c : Chern l E T)
    (n : c.Normalized l E) :
    (c.reduction.derivedAdjunction.homEquiv _ _) c.unitIso.hom ≫
        (c.reduction.forget.F.mapDerivedCategorySingleFunctor 0).hom.app
          (coefficient T (Rrings l T)) =
      (DerivedCategory.singleFunctor (Ab T) 0).map
        (integerGenerator T (Rrings l T) c.reduction.forget) := by
  exact chern_integral_source_normalization l T (Rrings l T) (Arings l E T)
    (coefficientSystemMap l E T) c (scalarGenerator l E T) n

private theorem integer_transpose
    {X Y : Scheme.{u}} {f : X ⟶ Y}
    {cY : Chern l E Y} {cX : Chern l E X}
    (nY : cY.Normalized l E) (nX : cX.Normalized l E)
    (d : IntegralCoefficientPullback l E f cY cX) :
    (abPull f).mapDerivedCategory.map
        ((cY.reduction.derivedAdjunction.homEquiv _ _) cY.unitIso.hom) ≫
      (Functor.mapDerivedCategorySquareIso d.forgetIso).hom.app (unit Y (Rrings l Y)) ≫
      cX.reduction.forget.F.mapDerivedCategory.map d.derivedUnit.hom =
    integerDerivedPull f ≫
      (cX.reduction.derivedAdjunction.homEquiv _ _) cX.unitIso.hom := by
  exact single_normalized_square (A := Ab Y) (B := Systems Y (Rrings l Y))
    (A' := Ab X) (B' := Systems X (Rrings l X))
    cY.reduction.forget.F (abPull f) d.pull cX.reduction.forget.F d.forgetIso
    (integers Y) (integers X) (coefficient Y (Rrings l Y)) (coefficient X (Rrings l X))
    (integerGenerator Y (Rrings l Y) cY.reduction.forget)
    (integerGenerator X (Rrings l X) cX.reduction.forget) (integerPull f) d.unitIso.hom
    ((cY.reduction.derivedAdjunction.homEquiv _ _) cY.unitIso.hom)
    ((cX.reduction.derivedAdjunction.homEquiv _ _) cX.unitIso.hom)
    (source_normalization l E cY nY) (source_normalization l E cX nX)
    d.unit_normalization (integerDerivedPull f) d.derivedUnit.hom
    (integer_comparison f) (unit_comparison l E d)

/-- Integral reduction commutes with an exact inverse image of the quotient module
towers. Only the Z-to-R stage occurs; no scalar extension to A, Tate tensor line,
or coefficient/line comparison at A occurs in the conclusion.

Source: blueprint classes proof (2); realization proof steps 2--4
(blueprint: lem-sp-tower-chern-reduction-pullback).

Proof: identify abelian towers with sheaves on the vertical sequence site, and
their R-modules with the recorded module systems. The forgetful square identifies
the underlying inverse image; the Z/ell^(n+1) action is unique on each torsion
sheaf, so the identification is R-linear and respects quotient transitions.
Apply the derived algebra-diagram extension/pullback comparison for Z -> R.
Transport it to the given reduction functors by the unique isomorphisms respecting
their universal derived counits. This gives eta on every integral derived object.
For integers, transpose through the reduction adjunctions. The source normalization
turns both transposes into integerGenerator, and unit_normalization identifies
the results, including the canonical single comparisons.
For full units, transpose through the same adjunctions instead of recomputing
any cohomology. The target normalizations identify the transposes of rootIso
with the shifted signed Kummer boundaries. Exact-functor transport of the
short-exact-sequence triangle commutes with that boundary, including its shift
comparison. Naturality of the triangle under d.kummer then compares its two
boundaries. Substitute d.kummer_roots for the first component and d.kummer_units
for the last. Naturality of the single comparison, followed by the shift-by-two
comparison, gives exactly derivedRoot. The normalized mate relation of the
extension comparison identifies these equal transposes with the two sides of
the second equation. Injectivity of the reduction adjunction's hom equivalence
proves equality in the module-system derived category. No faithfulness of
forgetting or derived evaluation is asserted. Nothing uses nonemptiness,
flatness of f, or unramified E. -/
theorem tower_chernReduction_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (_hX : IsUnit (l : Γ(X, ⊤))) (_hY : IsUnit (l : Γ(Y, ⊤)))
    (cY : Chern l E Y) (cX : Chern l E X)
    (_nY : cY.Normalized l E) (_nX : cX.Normalized l E)
    (d : IntegralCoefficientPullback l E f cY cX) :
    ∃ η : cY.reduction.derived ⋙ d.pull.mapDerivedCategory ⟶
        (abPull f).mapDerivedCategory ⋙ cX.reduction.derived,
      η.app ((DerivedCategory.singleFunctor (Ab Y) 0).obj (integers Y)) ≫
          cX.reduction.derived.map (integerDerivedPull f) ≫ cX.unitIso.hom =
        d.pull.mapDerivedCategory.map cY.unitIso.hom ≫ d.derivedUnit.hom ∧
      η.app (((DerivedCategory.singleFunctor (Ab Y) 0).obj (units Y))⟦(1 : ℤ)⟧) ≫
          cX.reduction.derived.map (unitsDerivedPull f) ≫ cX.rootIso.hom =
        d.pull.mapDerivedCategory.map cY.rootIso.hom ≫ (d.derivedRoot 2).hom := by
  let : IsIso (reductionPullbackMate l E d) := tower_reductionMate_isIso l E d
  let θ := (asIso (reductionPullbackMate l E d)).symm
  have hθ (M : DerivedCategory (Ab Y)) :
      cX.reduction.derivedAdjunction.unit.app ((abPull f).mapDerivedCategory.obj M) ≫
        cX.reduction.forget.F.mapDerivedCategory.map (θ.inv.app M) =
      (abPull f).mapDerivedCategory.map (cY.reduction.derivedAdjunction.unit.app M) ≫
        (Functor.mapDerivedCategorySquareIso d.forgetIso).hom.app
          (cY.reduction.derived.obj M) := by
    exact (unit_mateEquiv_symm cY.reduction.derivedAdjunction
      cX.reduction.derivedAdjunction
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d.forgetIso).hom) M).symm
  refine ⟨θ.hom, ?_, ?_⟩
  · exact (normalized_exchange cY.reduction.derivedAdjunction cX.reduction.derivedAdjunction
      (abPull f).mapDerivedCategory d.pull.mapDerivedCategory
      (Functor.mapDerivedCategorySquareIso d.forgetIso) θ hθ
      _ _ _ _ (integerDerivedPull f) d.derivedUnit.hom cY.unitIso.hom cX.unitIso.hom
      _ _ (by simp only [Adjunction.homEquiv_unit])
      (by simp only [Adjunction.homEquiv_unit])
      (integer_transpose l E _nY _nX d)).symm
  · exact (normalized_exchange cY.reduction.derivedAdjunction cX.reduction.derivedAdjunction
      (abPull f).mapDerivedCategory d.pull.mapDerivedCategory
      (Functor.mapDerivedCategorySquareIso d.forgetIso) θ hθ
      _ _ _ _ (unitsDerivedPull f) (d.derivedRoot 2).hom cY.rootIso.hom cX.rootIso.hom
      _ _ (by simp only [Adjunction.homEquiv_unit])
      (by simp only [Adjunction.homEquiv_unit])
      (kummer_pullback_transpose l E _nY _nX d)).symm

end AlgebraicGeometry.ProEtale.SpTowerClasses
