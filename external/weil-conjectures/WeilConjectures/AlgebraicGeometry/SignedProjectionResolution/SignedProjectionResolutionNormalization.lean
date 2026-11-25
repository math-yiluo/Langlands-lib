/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionFormulaArrows
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.FixedTensorLocalization.FixedTensorLocalizationComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleMixedProjectionMate

/-! # Normalized signed projection formula on chosen resolutions

The source and target comparisons are the specified mixed tensor comparisons,
with arbitrary derived isomorphisms to the chosen representatives. All operations
are on the original small pro-etale sites and ordinary uncompleted derived categories.

## References

* Stacks Tag 0B56
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.SignedProjectionResolution

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)

/-- The coefficient complex pulled back termwise by the exact module pullback. -/
abbrev pulledCoefficient (F : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  ((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj F

/-- The signed total complex C = Tot(f_* I tensor F); its second differential
has sign (-1)^a on bidegree (a,r). -/
abbrev sourceComplex (I : CochainComplex (proEtaleRingModules X S) ℤ)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  CochainComplex.mapBifunctor
    (((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj I)
    F (proEtaleOrdinaryTensor Y R)

/-- The signed total complex J = Tot(I tensor f^* F), with the same sign convention. -/
abbrev targetComplex (I : CochainComplex (proEtaleRingModules X S) ℤ)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  CochainComplex.mapBifunctor I (pulledCoefficient f R S c F) (proEtaleOrdinaryTensor X S)

/-- The ordinary direct image B = f_* J, taken termwise. -/
abbrev pushTargetComplex (I : CochainComplex (proEtaleRingModules X S) ℤ)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ) :=
  ((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj
    (targetComplex f R S c I F)

/-- The right-derived comparison eta_H, without an injectivity restriction on H. -/
def derivedComparison (H : CochainComplex (proEtaleRingModules X S) ℤ) :
    DerivedCategory.Q.obj
        (((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj H) ⟶
      (proEtaleRingDerivedDirectImage f R S c).obj (DerivedCategory.Q.obj H) :=
  (proEtaleRingModuleDirectImage f R S c).rightDerivedFunctorUnitQ H

/-- Flat-term K-flat coefficient models, the K-injective target total, and the
invertible right-derived comparisons. -/
theorem model_properties
    (I : CochainComplex (proEtaleRingModules X S) ℤ) (hI : I.IsKInjective)
    (F : CochainComplex (proEtaleRingModules Y R) ℤ)
    (package : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F)
    (bounded : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (F.X r)) :
    proEtaleFlatRepresentatives Y R F ∧
      proEtaleFlatRepresentatives X S (pulledCoefficient f R S c F) ∧
      (targetComplex f R S c I F).IsKInjective ∧
      IsIso (derivedComparison f R S c I) ∧
      IsIso (derivedComparison f R S c (targetComplex f R S c I F)) := by
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let L := proEtaleRingModulePullback f R S c
  let j := Classical.choose (proEtaleProjectionUnit_existsUnique f R S c).exists
  let e (n : ℕ) := PreservesProduct.iso L (fun _ : Fin n ↦ 𝟙_ (proEtaleRingModules Y R)) ≪≫
    Pi.mapIso (fun _ : Fin n ↦ j)
  let package' : SheafOfModules.StrictPerfectCoefficientPackageOnSite
      ((sheafCompose (ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
      (pulledCoefficient f R S c F) :=
    { N := package.N
      i := fun r ↦ L.map (package.i r) ≫ (e (package.N r)).hom
      p := fun r ↦ (e (package.N r)).inv ≫ L.map (package.p r)
      splitting := fun r ↦ by
        simp only [Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp,
          package.splitting, L.map_id]
        rfl }
  have bounded' : ∃ l h : ℤ, ∀ r : ℤ,
      r < l ∨ h < r → IsZero ((pulledCoefficient f R S c F).X r) := by
    obtain ⟨l, h, hb⟩ := bounded
    exact ⟨l, h, fun r hr ↦ L.map_isZero (hb r hr)⟩
  have hJ : (targetComplex f R S c I F).IsKInjective :=
    tensorAdjunctionTotal_target_isKInjective L j I hI F bounded
      package.N package.i package.p package.splitting
  let := hI
  let := hJ
  refine ⟨proEtaleStrictPerfect_flat R F package bounded,
    proEtaleStrictPerfect_flat S _ package' bounded', hJ, ?_, ?_⟩ <;>
    dsimp only [derivedComparison] <;>
    rw [Functor.rightDerivedFunctorUnitQ_eq] <;> infer_instance

variable (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (K : DerivedCategory (proEtaleRingModules X S))
  (P : DerivedCategory (proEtaleRingModules Y R))
  (I : CochainComplex (proEtaleRingModules X S) ℤ) (hI : I.IsKInjective)
  (alpha : K ≅ DerivedCategory.Q.obj I)
  (F : CochainComplex (proEtaleRingModules Y R) ℤ)
  (beta : DerivedCategory.Q.obj F ≅ P)
  (package : SheafOfModules.StrictPerfectCoefficientPackageOnSite
    ((sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R) F)
  (bounded : ∃ l h : ℤ, ∀ r : ℤ, r < l ∨ h < r → IsZero (F.X r))

/-- The specified S = m_Y ((eta_I^{-1} Rf_* alpha) tensor beta^{-1}).
Its mixed tensor factor is normalized on every flat K-flat resolution, including
when the complex f_* I itself is not K-flat. -/
def sourceModel :
    a.tensor.obj ((proEtaleRingDerivedDirectImage f R S c).obj K, P) ≅
      DerivedCategory.Q.obj (sourceComplex f R S c I F) :=
  a.tensor.mapIso (Iso.prod
    ((proEtaleRingDerivedDirectImage f R S c).mapIso alpha ≪≫
      (@asIso _ _ _ _ (derivedComparison f R S c I)
        (model_properties f R S c I hI F package bounded).2.2.2.1).symm) beta.symm) ≪≫
    proEtaleMixedTensor R a
      (((proEtaleRingModuleDirectImage f R S c).mapHomologicalComplex (.up ℤ)).obj I)
      F (model_properties f R S c I hI F package bounded).1

/-- The specified T, using exact pullback of beta^{-1}, then ell_F, mixed tensor on X,
and eta_J^{-1}. This is an isomorphism in the derived category. -/
def targetModel :
    (proEtaleRingDerivedDirectImage f R S c).obj
        (b.tensor.obj (K, (proEtaleRingDerivedPullback f R S c).obj P)) ≅
      DerivedCategory.Q.obj (pushTargetComplex f R S c I F) :=
  (proEtaleRingDerivedDirectImage f R S c).mapIso
    (b.tensor.mapIso (Iso.prod alpha
      ((proEtaleRingDerivedPullback f R S c).mapIso beta.symm ≪≫
        (proEtaleRingDerivedPullbackFactors f R S c).app F)) ≪≫
      proEtaleMixedTensor S b I (pulledCoefficient f R S c F)
        (model_properties f R S c I hI F package bounded).2.1) ≪≫
    (@asIso _ _ _ _ (derivedComparison f R S c (targetComplex f R S c I F))
      (model_properties f R S c I hI F package bounded).2.2.2.2).symm

/-- The ordinary signed total counit mate t, using the total construction. -/
def totalMate : sourceComplex f R S c I F ⟶ pushTargetComplex f R S c I F := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  exact CategoryTheory.tensorAdjunctionTotal
    (proEtaleRingModulePullback f R S c) (proEtaleRingModuleDirectImage f R S c)
    (proEtaleRingModuleAdjunction f R S c) (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z) I F

/-- The specified finite-total retract inverse s. The existing construction has
summand (1 tensor p_r) q_{I^a,N_r} f_*(1 tensor f^* i_r), by
tensorAdjunctionTotalInverse_summand, including rank zero. No i_r or p_r is a chain map. -/
def totalInverse : pushTargetComplex f R S c I F ⟶ sourceComplex f R S c I F := by
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  let j := Classical.choose (proEtaleProjectionUnit_existsUnique f R S c).exists
  let hj := Classical.choose_spec (proEtaleProjectionUnit_existsUnique f R S c).exists
  exact tensorAdjunctionTotalInverse
    (proEtaleRingModulePullback f R S c) (proEtaleRingModuleDirectImage f R S c)
    (proEtaleRingModuleAdjunction f R S c) (proEtaleOrdinaryTensorPullback f R S c)
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z)
    j hj I F bounded package.N package.i package.p package.splitting

/-- The inverse S^{-1} Q_Y(s) T, for the supplied representatives and splitting package. -/
def inverse :
    (proEtaleRingDerivedDirectImage f R S c).obj
        (b.tensor.obj (K, (proEtaleRingDerivedPullback f R S c).obj P)) ⟶
      a.tensor.obj ((proEtaleRingDerivedDirectImage f R S c).obj K, P) :=
  (targetModel f R S c b K P I hI alpha F beta package bounded).hom ≫
    DerivedCategory.Q.map (totalInverse f R S c I F package bounded) ≫
      (sourceModel f R S c a K P I hI alpha F beta package bounded).inv

private theorem transport_projection
    {C : Type*} [Category C] {D : Type*} [Category D]
    (L : C ⥤ D) (V : D ⥤ C) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (pi : ∀ (K : D) (Q : C), T.obj (V.obj K, Q) ⟶ V.obj (U.obj (K, L.obj Q)))
    (hn₁ : ∀ {K I : D} (k : K ⟶ I) (Q : C),
      pi K Q ≫ V.map (U.map (Prod.mkHom k (𝟙 _))) =
        T.map (Prod.mkHom (V.map k) (𝟙 Q)) ≫ pi I Q)
    (hn₂ : ∀ (K : D) {P Q : C} (q : P ⟶ Q),
      T.map (Prod.mkHom (𝟙 _) q) ≫ pi K Q =
        pi K P ≫ V.map (U.map (Prod.mkHom (𝟙 K) (L.map q))))
    {K I : D} {A F Q M B : C} (k : K ≅ I) (q : F ≅ Q) (s : A ≅ V.obj I)
    (t : V.obj (U.obj (I, L.obj F)) ⟶ B) (m : T.obj (A, F) ⟶ M) (z : M ⟶ B)
    (h : T.map (Prod.mkHom s.hom (𝟙 F)) ≫ pi I F ≫ t = m ≫ z) :
    pi K Q ≫ V.map (U.map (Prod.mkHom k.hom (L.map q.inv))) ≫ t =
      T.map (Prod.mkHom (V.map k.hom ≫ s.inv) q.inv) ≫ m ≫ z := by
  have hs := congrArg (fun v ↦ T.map (Prod.mkHom s.inv (𝟙 F)) ≫ v) h
  simp only [← Category.assoc, ← T.map_comp, prod_comp, Iso.inv_hom_id,
    Category.id_comp] at hs
  change (T.map (𝟙 (V.obj I, F)) ≫ pi I F) ≫ t = _ at hs
  rw [T.map_id, Category.id_comp, Category.assoc] at hs
  calc
    _ = T.map (Prod.mkHom (𝟙 _) q.inv) ≫ pi K F ≫
        V.map (U.map (Prod.mkHom k.hom (𝟙 _))) ≫ t := by
      rw [← Category.assoc (T.map _) (pi K F), hn₂ K q.inv, Category.assoc]
      simp only [← Category.assoc, ← V.map_comp, ← U.map_comp, prod_comp,
        Category.comp_id, Category.id_comp]
    _ = T.map (Prod.mkHom (V.map k.hom) q.inv) ≫ pi I F ≫ t := by
      rw [← Category.assoc (pi K F), hn₁ k.hom F, ← Category.assoc,
        ← Category.assoc, ← T.map_comp, Category.assoc]
      simp only [prod_comp, Category.comp_id, Category.id_comp]
    _ = _ := by
      have hh := congrArg (fun v ↦ T.map (Prod.mkHom (V.map k.hom) q.inv) ≫ v) hs
      simpa only [← Category.assoc, ← T.map_comp, prod_comp, Category.comp_id] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- On every chosen K-injective and bounded strict-perfect representative, the canonical
counit mate is T^{-1} Q_Y(t) S, and S^{-1} Q_Y(s) T is its two-sided inverse.
No boundedness of K or I, and no chain-map condition on the splittings, is imposed. -/
theorem normalization :
    derivedProjectionFormulaMate (proEtaleRingDerivedPullback f R S c)
      (proEtaleRingDerivedDirectImage f R S c) (proEtaleRingDerivedAdjunction f R S c)
      a.tensor b.tensor (proEtaleCanonicalTensorComparison f R S c a b) K P =
      (sourceModel f R S c a K P I hI alpha F beta package bounded).hom ≫
        DerivedCategory.Q.map (totalMate f R S c I F) ≫
          (targetModel f R S c b K P I hI alpha F beta package bounded).inv ∧
    derivedProjectionFormulaMate (proEtaleRingDerivedPullback f R S c)
      (proEtaleRingDerivedDirectImage f R S c) (proEtaleRingDerivedAdjunction f R S c)
      a.tensor b.tensor (proEtaleCanonicalTensorComparison f R S c a b) K P ≫
      inverse f R S c a b K P I hI alpha F beta package bounded =
        𝟙 (a.tensor.obj ((proEtaleRingDerivedDirectImage f R S c).obj K, P)) ∧
    inverse f R S c a b K P I hI alpha F beta package bounded ≫
      derivedProjectionFormulaMate (proEtaleRingDerivedPullback f R S c)
      (proEtaleRingDerivedDirectImage f R S c) (proEtaleRingDerivedAdjunction f R S c)
      a.tensor b.tensor (proEtaleCanonicalTensorComparison f R S c a b) K P =
        𝟙 ((proEtaleRingDerivedDirectImage f R S c).obj
          (b.tensor.obj (K, (proEtaleRingDerivedPullback f R S c).obj P))) := by
  have hf := model_properties f R S c I hI F package bounded
  let L := proEtaleRingDerivedPullback f R S c
  let V := proEtaleRingDerivedDirectImage f R S c
  let adj := proEtaleRingDerivedAdjunction f R S c
  let mu := proEtaleCanonicalTensorComparison f R S c a b
  let pi := derivedProjectionFormulaMate L V adj a.tensor b.tensor mu
  let si := @asIso _ _ _ _ (derivedComparison f R S c I) hf.2.2.2.1
  let ti := V.mapIso
    (b.tensor.mapIso (Iso.prod (Iso.refl (DerivedCategory.Q.obj I))
      ((proEtaleRingDerivedPullbackFactors f R S c).app F)) ≪≫
        proEtaleMixedTensor S b I (pulledCoefficient f R S c F) hf.2.1) ≪≫
    (@asIso _ _ _ _ (derivedComparison f R S c (targetComplex f R S c I F))
      hf.2.2.2.2).symm
  have h := proEtaleMixedProjectionMate f R S c a b I hI F hf.1
  have hnorm : a.tensor.map (Prod.mkHom si.hom (𝟙 (DerivedCategory.Q.obj F))) ≫
      pi (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj F) ≫ ti.hom =
      (proEtaleMixedTensor R a _ F hf.1).hom ≫
        DerivedCategory.Q.map (totalMate f R S c I F) := by
    change a.tensor.map (Prod.mkHom (derivedComparison f R S c I) (𝟙 _)) ≫
      pi (DerivedCategory.Q.obj I) (DerivedCategory.Q.obj F) ≫
      V.map (b.tensor.map (Prod.mkHom (𝟙 _)
          ((proEtaleRingDerivedPullbackFactors f R S c).hom.app F)) ≫
        (proEtaleMixedTensor S b I (pulledCoefficient f R S c F) hf.2.1).hom) =
      (proEtaleMixedTensor R a _ F hf.1).hom ≫
        DerivedCategory.Q.map (totalMate f R S c I F) ≫
          derivedComparison f R S c (targetComplex f R S c I F) at h
    have hh := congrArg (fun z ↦ z ≫
      (@asIso _ _ _ _ (derivedComparison f R S c (targetComplex f R S c I F))
        hf.2.2.2.2).inv) h
    simpa only [ti, si, Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id] using hh
  have ht := transport_projection L V a.tensor b.tensor pi
    (fun {_ _} q Q ↦ derivedProjectionFormulaMate_naturality
      L V adj a.tensor b.tensor mu _ _ Q q)
    (fun E {_ _} q ↦ by
      exact (((adj.rightAdjointProjectionMap
        (T_C := Functor.curry.obj b.tensor) (T_D := Functor.curry.obj a.tensor)
        (Functor.curry.map mu.hom ≫
          (Functor.curryObjProdComp L L b.tensor).hom)).app E).naturality q))
    alpha beta si ti.hom (proEtaleMixedTensor R a _ F hf.1).hom
    (DerivedCategory.Q.map (totalMate f R S c I F)) hnorm
  have hsource : (sourceModel f R S c a K P I hI alpha F beta package bounded).hom =
      a.tensor.map (Prod.mkHom (V.map alpha.hom ≫ si.inv) beta.inv) ≫
        (proEtaleMixedTensor R a _ F hf.1).hom := rfl
  have htarget : (targetModel f R S c b K P I hI alpha F beta package bounded).hom =
      V.map (b.tensor.map (Prod.mkHom alpha.hom (L.map beta.inv))) ≫ ti.hom := by
    simp only [targetModel, ti, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom, Iso.refl_hom, asIso_inv,
      Functor.map_comp, Category.assoc]
    conv_rhs => rw [← V.map_comp_assoc, ← b.tensor.map_comp]
    simp only [prod_comp, Category.comp_id]
    rfl
  have forward : pi K P =
      (sourceModel f R S c a K P I hI alpha F beta package bounded).hom ≫
        DerivedCategory.Q.map (totalMate f R S c I F) ≫
          (targetModel f R S c b K P I hI alpha F beta package bounded).inv := by
    apply (cancel_mono
      (targetModel f R S c b K P I hI alpha F beta package bounded).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [htarget, hsource]
    simpa only [Category.assoc] using ht
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.monoidalCategory S
  let j := Classical.choose (proEtaleProjectionUnit_existsUnique f R S c).exists
  have hj := Classical.choose_spec (proEtaleProjectionUnit_existsUnique f R S c).exists
  have htotal : IsIso (totalMate f R S c I F) :=
    tensorAdjunctionTotal_isIso
      (proEtaleRingModulePullback f R S c) (proEtaleRingModuleDirectImage f R S c)
      (proEtaleRingModuleAdjunction f R S c) (proEtaleOrdinaryTensorPullback f R S c)
      (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality f R S c _ _ _ _ v z)
      j hj I F bounded package.N package.i package.p package.splitting
  have hinv : totalInverse f R S c I F package bounded =
      inv (totalMate f R S c I F) := rfl
  dsimp only [pi, L, V, adj, mu] at forward
  refine ⟨forward, ?_, ?_⟩
  · rw [forward]
    dsimp only [inverse]
    rw [hinv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← DerivedCategory.Q.map_comp_assoc, IsIso.hom_inv_id,
      DerivedCategory.Q.map_id, Category.id_comp, Iso.hom_inv_id]
  · rw [forward]
    dsimp only [inverse]
    rw [hinv]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← DerivedCategory.Q.map_comp_assoc, IsIso.inv_hom_id,
      DerivedCategory.Q.map_id, Category.id_comp, Iso.hom_inv_id]

end AlgebraicGeometry.Scheme.SignedProjectionResolution
