/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComparisonIso
public import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionHomologyCoherence
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartAugmentationNaturality
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality
import WeilConjectures.AlgebraicGeometry.QCohTensorResolutionChartComparisonIsoFormula

/-! # K-flat chart comparison naturality

Source: Stacks Project, Tags 08DX(2), 06YT and 01I9.
(blueprint: new-t3-qcoh-tensor-resolution-chart-comparison-naturality).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable local instance QCohTensorResolutionChartComparisonNaturality_monoidal
    (X : Scheme.{u}) : MonoidalCategory X.Modules :=
  SheafOfModules.monoidalCategory X.sheaf
local instance QCohTensorResolutionChartComparisonNaturality_zero
    (X : Scheme.{u}) : (curriedTensor X.Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
local instance QCohTensorResolutionChartComparisonNaturality_objZero
    (X : Scheme.{u}) (L : X.Modules) :
    ((curriedTensor X.Modules).obj L).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf L

/-- Naturality in the component form of the chart restriction comparison. -/
private theorem tensorResolutionChartRestrictionComplexIso_naturality
    (Y : Scheme.{u}) (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    {E E' : CochainComplex Y.Modules ℤ} (g : E ⟶ E') :
    ((Scheme.Modules.restrictFunctor
      (Spec.map (Y.presheaf.map (homOfLE h).op))).mapHomologicalComplex (.up ℤ)).map
        (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).map g) ≫
      (tensorResolutionChartRestrictionComplexIso Y V U h E').hom =
    (tensorResolutionChartRestrictionComplexIso Y V U h E).hom ≫
      ((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).map g := by
  exact (Functor.mapHomologicalComplexCompIso
    (tensorResolutionChartRestrictionIso Y V U h) (.up ℤ)).hom.naturality g

/-- Keep the chart transition's complex type behind a named construction. -/
private noncomputable def tensorResolutionChartTransition {Y : Scheme.{u}}
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (MA : ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (MB : ModuleCat.{u} (Γ(Y, V.1) : Type u))
    (PA : ProjectiveResolution MA) (PB : ProjectiveResolution MB)
    (a : PA.complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj PB.complex) :
    ((Scheme.Modules.restrictFunctor
      (Spec.map (Y.presheaf.map (homOfLE h).op))).mapHomologicalComplex (.up ℤ)).obj
        (tensorResolutionChartComplex U MA PA) ⟶ tensorResolutionChartComplex V MB PB :=
  tensorResolutionSemilinearComplexMap (Y.presheaf.map (homOfLE h).op) (.up ℤ)
    (PA.complex.extend ComplexShape.embeddingDownNat)
    (PB.complex.extend ComplexShape.embeddingDownNat)
    (tensorResolutionExtendSemilinear (Y.presheaf.map (homOfLE h).op).hom
      ComplexShape.embeddingDownNat PA.complex PB.complex a)

/-- Compose a comparison square with the inverse of a normalization square. -/
private theorem tensorResolution_normalize_comparison
    {C D : Type*} [Category C] [Category D] (R : C ⥤ D)
    {A B Q : C} {A' B' Q' : D}
    (gU : A ≅ B) (gV : A' ≅ B') (eU : Q ≅ B) (eV : Q' ≅ B')
    (ρ : R.obj Q ⟶ Q') (v : R.obj A ⟶ A') (t : R.obj B ⟶ B')
    (hc : R.map gU.hom ≫ t = v ≫ gV.hom)
    (hn : R.map eU.hom ≫ t = ρ ≫ eV.hom) :
    R.map (gU ≪≫ eU.symm).hom ≫ ρ = v ≫ (gV ≪≫ eV.symm).hom := by
  have hninv : R.map eU.inv ≫ ρ = t ≫ eV.inv := by
    apply (cancel_epi (R.map eU.hom)).1
    rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [← Category.assoc, hn]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [hninv]
  simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ eV.inv) hc

-- The four tensor squares require a larger elaboration budget.

/-- Naturality of the common K-flat comparison and normalized open restriction.

Source: Stacks Tags 08DX(2), 06YT and 01I9: compare the two ordinary tensor
calculations through a common K-flat resolution and use functorial restriction.

Proof in words: the formula ha implies that the extended sheafification of a
commutes with the two chart augmentations to M[0]; this is exactly
 tensorResolutionChartAugmentation_naturality. The restriction complex isomorphisms
for K, F, M[0] and N[0] commute with q and s by naturality. Apply
 tensorResolution_restrictedTensor_square to these squares and the augmentation
square. This gives the four commuting squares between the legs of the tensor
zigzags through the same restricted F. Take homology, inserting the inverse
exact-restriction homology isomorphism at each vertex. Every horizontal leg of
the zigzag is invertible by K-flat tensor invariance. The elementary cancellation
lemma tensorResolution_homology_zigzag therefore gives the comparison square.
The normalized open-restriction homology isomorphism is itself natural by
 tensorResolutionNormalizedRestrictHomologyIso_naturality, using the total tensor
restriction square tensorResolutionChartRestriction_total. Compose its inverse
square with the comparison square and cancel adjacent inverse isomorphisms to
obtain the displayed formula. Neither b, k nor a coefficient presentation of N
is involved. The argument allows arbitrary n, zero complexes and unbounded K.

(blueprint: new-t3-qcoh-tensor-resolution-chart-comparison-naturality) -/
theorem tensorResolutionChartComparisonIso_naturality
    (Y : Scheme.{u}) (M N : Y.Modules) [M.IsQuasicoherent]
    (MA : ∀ U : Y.affineOpens, ModuleCat.{u} (Γ(Y, U.1) : Type u))
    (sM : ∀ U : Y.affineOpens, MA U ≃ₗ[Γ(Y, U.1)] M.val.obj (op U.1))
    (P : ∀ U, ProjectiveResolution (MA U))
    (K F : CochainComplex Y.Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj M)
    (s : F ⟶ (CochainComplex.singleFunctor Y.Modules 0).obj N)
    (hK : CochainComplex.IsKFlatTensor (R := Y.sheaf) K)
    (hF : CochainComplex.IsKFlatTensor (R := Y.sheaf) F)
    (hq : QuasiIso q) (hs : QuasiIso s) (n : ℕ)
    (V U : Y.affineOpens) (h : V.1 ≤ U.1)
    (a : (P U).complex ⟶ ((ModuleCat.restrictScalars
      (Y.presheaf.map (homOfLE h).op).hom).mapHomologicalComplex (.down ℕ)).obj
        (P V).complex)
    (ha : ∀ x : (P U).complex.X 0,
      sM V ((P V).π.f 0 (a.f 0 x)) =
        M.val.map (homOfLE h).op (sM U ((P U).π.f 0 x))) :
    let φ := Y.presheaf.map (homOfLE h).op
    let R := Scheme.Modules.restrictFunctor (Spec.map φ)
    let N0 := (CochainComplex.singleFunctor Y.Modules 0).obj N
    let RU := (Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let RV := (Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)
    let EA := tensorResolutionChartComplex U (MA U) (P U)
    let EB := tensorResolutionChartComplex V (MA V) (P V)
    let α := tensorResolutionSemilinearComplexMap φ (.up ℤ)
      ((P U).complex.extend ComplexShape.embeddingDownNat)
      ((P V).complex.extend ComplexShape.embeddingDownNat)
      (tensorResolutionExtendSemilinear φ.hom ComplexShape.embeddingDownNat
        (P U).complex (P V).complex a)
    let β := tensorResolutionRestrictionTensorMap (Spec.map φ) EA (RU.obj N0)
      EB (RV.obj N0) α (tensorResolutionChartRestrictionComplexIso Y V U h N0).hom
    R.map (tensorResolutionChartComparisonIso Y M N U (MA U) (sM U) (P U)
        K F q s hK hF hq hs (-(n : ℤ)) ≪≫
      (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K N0 (-(n : ℤ))).symm).hom ≫
      (tensorResolutionChartRestrictionIso Y V U h).hom.app
        ((CochainComplex.mapBifunctor K N0 (curriedTensor Y.Modules)).homology (-(n : ℤ))) =
    (((CochainComplex.mapBifunctor EA (RU.obj N0)
        (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc (-(n : ℤ))).mapHomologyIso R).inv ≫
      HomologicalComplex.homologyMap β (-(n : ℤ)) ≫
        (tensorResolutionChartComparisonIso Y M N V (MA V) (sM V) (P V)
            K F q s hK hF hq hs (-(n : ℤ)) ≪≫
          (tensorResolutionNormalizedRestrictHomologyIso V.2.fromSpec K N0 (-(n : ℤ))).symm).hom
    := by
  dsimp only
  let αc := tensorResolutionChartTransition V U h (MA U) (MA V) (P U) (P V) a
  have : QuasiIso q := hq
  have : QuasiIso s := hs
  let f₀ := tensorResolutionRestrictionTensorMap (Spec.map (Y.presheaf.map (homOfLE h).op))
    (tensorResolutionChartComplex U (MA U) (P U)) (((Scheme.Modules.restrictFunctor
    U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor Y.Modules
    0).obj N))
    (tensorResolutionChartComplex V (MA V) (P V)) (((Scheme.Modules.restrictFunctor
      V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor Y.Modules
      0).obj N)) αc ((tensorResolutionChartRestrictionComplexIso Y V U h
      ((CochainComplex.singleFunctor Y.Modules 0).obj N)).hom)
  let f₄ := tensorResolutionRestrictionTensorMap (Spec.map (Y.presheaf.map (homOfLE h).op))
    (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
    (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
    ((CochainComplex.singleFunctor Y.Modules 0).obj N))
    (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K)
      (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      ((tensorResolutionChartRestrictionComplexIso Y V U h K).hom)
      ((tensorResolutionChartRestrictionComplexIso Y V U h ((CochainComplex.singleFunctor
      Y.Modules 0).obj N)).hom)
  have hz := tensorResolutionComparison_restriction (Spec.map (Y.presheaf.map (homOfLE h).op))
    (tensorResolutionChartComplex U (MA U) (P U)) (((Scheme.Modules.restrictFunctor
      U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K) (((Scheme.Modules.restrictFunctor
      U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor Y.Modules
      0).obj M)) (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up
      ℤ)).obj F) (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up
      ℤ)).obj ((CochainComplex.singleFunctor Y.Modules 0).obj N))
    (tensorResolutionChartComplex V (MA V) (P V)) (((Scheme.Modules.restrictFunctor
      V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K) (((Scheme.Modules.restrictFunctor
      V.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor Y.Modules
      0).obj M)) (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up
      ℤ)).obj F) (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up
      ℤ)).obj ((CochainComplex.singleFunctor Y.Modules 0).obj N))
    (tensorResolutionChartAugmentation M U (MA U) (sM U) (P U)) (((Scheme.Modules.restrictFunctor
      U.2.fromSpec).mapHomologicalComplex (.up ℤ)).map q) (((Scheme.Modules.restrictFunctor
      U.2.fromSpec).mapHomologicalComplex (.up ℤ)).map s) (tensorResolutionChartAugmentation M V
      (MA V) (sM V) (P V)) (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex
      (.up ℤ)).map q) (((Scheme.Modules.restrictFunctor V.2.fromSpec).mapHomologicalComplex (.up
      ℤ)).map s)
    (tensorResolution_isKFlat_bundledRing Γ(Y, U.1) (MA U) (P U))
    (isKFlat_restrict U.2.fromSpec K hK) (isKFlat_restrict U.2.fromSpec F hF)
    (tensorResolution_isKFlat_bundledRing Γ(Y, V.1) (MA V) (P V))
    (isKFlat_restrict V.2.fromSpec K hK) (isKFlat_restrict V.2.fromSpec F hF)
    (tensorResolutionChartAugmentation_quasiIso M U (MA U) (sM U) (P U))
    (by infer_instance) (by infer_instance)
    (tensorResolutionChartAugmentation_quasiIso M V (MA V) (sM V) (P V))
    (by infer_instance) (by infer_instance)
    αc ((tensorResolutionChartRestrictionComplexIso Y V U h K).hom)
      ((tensorResolutionChartRestrictionComplexIso Y V U h ((CochainComplex.singleFunctor
      Y.Modules 0).obj M)).hom) ((tensorResolutionChartRestrictionComplexIso Y V U h F).hom)
      ((tensorResolutionChartRestrictionComplexIso Y V U h ((CochainComplex.singleFunctor
      Y.Modules 0).obj N)).hom)
    (tensorResolutionChartAugmentation_naturality M V U h
      (MA U) (MA V) (sM U) (sM V) (P U) (P V) a ha)
    (tensorResolutionChartRestrictionComplexIso_naturality Y V U h q)
    (tensorResolutionChartRestrictionComplexIso_naturality Y V U h s) (-(n : ℤ))
  have hn := tensorResolutionNormalizedRestrictHomologyIso_naturality Y V U h K
    ((CochainComplex.singleFunctor Y.Modules 0).obj N)
    (-(n : ℤ)) (tensorResolutionChartRestriction_total Y V U h K ((CochainComplex.singleFunctor
      Y.Modules 0).obj N))
  simpa only [Category.assoc, f₀, αc, tensorResolutionChartTransition] using
    tensorResolution_normalize_comparison (Scheme.Modules.restrictFunctor (Spec.map
      (Y.presheaf.map (homOfLE h).op)))
    (tensorResolutionChartComparisonIso Y M N U (MA U) (sM U) (P U)
      K F q s hK hF hq hs (-(n : ℤ)))
    (tensorResolutionChartComparisonIso Y M N V (MA V) (sM V) (P V)
      K F q s hK hF hq hs (-(n : ℤ)))
    (tensorResolutionNormalizedRestrictHomologyIso U.2.fromSpec K ((CochainComplex.singleFunctor
      Y.Modules 0).obj N) (-(n : ℤ)))
    (tensorResolutionNormalizedRestrictHomologyIso V.2.fromSpec K ((CochainComplex.singleFunctor
      Y.Modules 0).obj N) (-(n : ℤ)))
    ((tensorResolutionChartRestrictionIso Y V U h).hom.app
      ((CochainComplex.mapBifunctor K ((CochainComplex.singleFunctor Y.Modules 0).obj N)
        (curriedTensor Y.Modules)).homology (-(n : ℤ))))
    ((((CochainComplex.mapBifunctor (tensorResolutionChartComplex U (MA U) (P U))
      (((Scheme.Modules.restrictFunctor U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj
      ((CochainComplex.singleFunctor Y.Modules 0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc (-(n : ℤ))).mapHomologyIso
        (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op)))).inv ≫
        HomologicalComplex.homologyMap f₀ (-(n : ℤ)))
    ((((CochainComplex.mapBifunctor (((Scheme.Modules.restrictFunctor
      U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj K) (((Scheme.Modules.restrictFunctor
      U.2.fromSpec).mapHomologicalComplex (.up ℤ)).obj ((CochainComplex.singleFunctor Y.Modules
      0).obj N))
      (curriedTensor (Spec Γ(Y, U.1)).Modules)).sc (-(n : ℤ))).mapHomologyIso
        (Scheme.Modules.restrictFunctor (Spec.map (Y.presheaf.map (homOfLE h).op)))).inv ≫
        HomologicalComplex.homologyMap f₄ (-(n : ℤ)))
    (by simpa only [tensorResolutionChartComparisonIso_hom_eq, Category.assoc] using hz)
    (by simpa only [Category.assoc] using hn)

end AlgebraicGeometry
