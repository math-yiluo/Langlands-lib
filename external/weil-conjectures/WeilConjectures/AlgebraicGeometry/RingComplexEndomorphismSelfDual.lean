/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality

/-! # Self-duality of endomorphisms of the ring complex

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe v

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.ConstantCompletion

private theorem unitEndomorphismSelfDual
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v})
    (a : SheafOfModules.unit (siteModuleRings R) ⟶
      SheafOfModules.unit (siteModuleRings R)) :
    SheafOfModules.homObjMap (R := R) a (𝟙 _) ≫
        (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom =
      (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom ≫ a := by
  apply SheafOfModules.hom_ext
  ext U φ : 3
  let f : R.obj.obj U →ₗ[R.obj.obj U] R.obj.obj U :=
    (φ.app (op (Over.mk (𝟙 U.unop)))).hom
  let g : R.obj.obj U →ₗ[R.obj.obj U] R.obj.obj U := (a.val.app U).hom
  change f (g 1) = g (f 1)
  have hf (x : R.obj.obj U) : f x = x * f 1 := by
    simpa only [smul_eq_mul, mul_one] using f.map_smul x 1
  have hg (x : R.obj.obj U) : g x = x * g 1 := by
    simpa only [smul_eq_mul, mul_one] using g.map_smul x 1
  rw [hf, hg (f 1), mul_comm]

private theorem rankOneEndomorphismSelfDual
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v}) (X : Mod R)
    (s : X ≅ SheafOfModules.unit (siteModuleRings R)) (a : X ⟶ X) :
    SheafOfModules.homObjMap (R := R) a (𝟙 X) ≫
        SheafOfModules.homObjMap (R := R) s.inv (𝟙 X) ≫
          (SheafOfModules.homObjUnitIso (R := R) X).hom =
      SheafOfModules.homObjMap (R := R) s.inv (𝟙 X) ≫
        (SheafOfModules.homObjUnitIso (R := R) X).hom ≫ a := by
  let b := s.inv ≫ a ≫ s.hom
  let h := SheafOfModules.homObjMap (R := R) s.inv s.hom
  have hh : SheafOfModules.homObjMap (R := R) a (𝟙 X) ≫ h =
      h ≫ SheafOfModules.homObjMap (R := R) b (𝟙 _) := by
    simp only [h, SheafOfModules.homObjMap_comp_homObjMap,
      Category.comp_id, Category.id_comp]
    congr 1
    simp [b]
  have he : SheafOfModules.homObjMap (R := R) s.inv (𝟙 X) ≫
      (SheafOfModules.homObjUnitIso (R := R) X).hom ≫ s.hom =
        h ≫ (SheafOfModules.homObjUnitIso (R := R) (SheafOfModules.unit _)).hom := by
    rw [← evaluation_naturality J R s.hom, ← Category.assoc]
    erw [SheafOfModules.homObjMap_comp_homObjMap (R := R)]
    simp only [Category.id_comp, h]
  apply (cancel_mono s.hom).1
  simp only [Category.assoc]
  rw [he, ← Category.assoc, hh, Category.assoc, unitEndomorphismSelfDual]
  rw [← Category.assoc h _ b, ← he]
  simp [b]

/-- An endomorphism of the ring complex is its own dual under evaluation at one.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X (internal Hom complexes),
and sites-modules.tex, internal Hom evaluated on the rank-one ring module.
(auxiliary; not a blueprint node).

Proof: a linear endomorphism of the ring module is multiplication by its value
at one. Two such multiplication maps commute over a commutative ring, so
precomposition by an endomorphism, followed by evaluation at one, is the same
as evaluation at one followed by that endomorphism. Transport this identity
along the degree-zero isomorphism of the single complex, using naturality of
evaluation. Project the Hom-complex map onto its source degree zero factor.
The projection formula gives the desired identity in degree zero. In every
other degree its target is a zero object, so the two morphisms agree. This
also applies to zero rings and empty sites. -/
theorem ringComplexEndomorphism_selfDual
    {C : Type v} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{v})
    (a : ringedSiteRingComplex R ⟶ ringedSiteRingComplex R) :
    ((homComplexFunctor (R := R)).flip.obj (ringedSiteRingComplex R)).map a.op ≫
        (ringedHomUnitEvaluationIso R (ringedSiteRingComplex R)).hom =
      (ringedHomUnitEvaluationIso R (ringedSiteRingComplex R)).hom ≫ a := by
  let U := ringedSiteRingComplex R
  let s : U.X 0 ≅ SheafOfModules.unit (siteModuleRings R) :=
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 (SheafOfModules.unit _)
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = 0
  · subst n
    simp only [HomologicalComplex.comp_f]
    rw [ringedHomUnitEvaluationIso_hom_f_projection, ← Category.assoc]
    have h := homComplexFunctor_map_f_π a (𝟙 U) 0 0 0 (by omega)
    simp only [Functor.map_id, Category.comp_id, HomologicalComplex.id_f] at h
    erw [h]
    simp only [Category.assoc]
    congr 1
    exact rankOneEndomorphismSelfDual R (U.X 0) s (a.f 0)
  · exact (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (SheafOfModules.unit (siteModuleRings R)) n hn).eq_of_tgt _ _

end CategoryTheory.ConstantCompletion
