/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedForgetTensorTransposition.RingedForgetTensorTranspositionData
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Normalized unit comparison for ringed tensor functors
Source: Stacks 0FPT (blueprint: lem-sf-ringed-forget-tensor-unit-representatives).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false

universe b vb a va c v r d vd s wb wa
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite WeilConjectures
-- Keep fixed derived-category constructions behind their APIs during elaboration.
attribute [local irreducible] homComplexFunctor homComplexπ derivedInternalHomOfUniverses
  coefficientHomResolutionIso Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  DerivedCategory instCategoryDerivedCategory DerivedCategory.Q
  SheafOfModules.IsFlatOnSite
  CochainComplex.IsKFlatIndependentCoefficients

namespace CategoryTheory.RingedForgetTensorTransposition

section TotalMap
variable {E : Type a} [Category.{va} E] [Preadditive E]
  (G : E ⥤ E ⥤ E) [G.PreservesZeroMorphisms]
  [∀ X, (G.obj X).PreservesZeroMorphisms]
  [∀ P Q : CochainComplex E ℤ, HomologicalComplex.HasMapBifunctor P Q G (.up ℤ)]
private theorem total_map_generic
    {P P' Q Q' : CochainComplex E ℤ} (f : P ⟶ P') (g : Q ⟶ Q') :
    (Functor.uncurry.obj (G.map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))).map
      (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom f g) =
      HomologicalComplex.mapBifunctorMap f g G (.up ℤ) := by
  change HomologicalComplex.mapBifunctorMap f (𝟙 Q) G (.up ℤ) ≫
    HomologicalComplex.mapBifunctorMap (𝟙 P') g G (.up ℤ) = _
  simp only [HomologicalComplex.mapBifunctorMap, Functor.map_id, NatTrans.id_app,
    Category.id_comp, Category.comp_id, ← HomologicalComplex₂.total.map_comp]
end TotalMap

section Generic
variable {B : Type b} [Category.{vb} B] {A : Type a} [Category.{va} A]
  {HB : Bᵒᵖ × B ⥤ B} {HA : Aᵒᵖ × A ⥤ A}
  (S : CoefficientClosedStructure HB) (T : CoefficientClosedStructure HA)
  (F : B ⥤ A) (μ : S.tensor ⋙ F ≅ (F.prod F) ⋙ T.tensor)

private theorem right_unit_of_models
    (P O X : B) (P' O' X' : A)
    (i : X ≅ S.tensor.obj (P, O)) (j : X' ≅ T.tensor.obj (P', O'))
    (aP : F.obj P ≅ P') (aO : F.obj O ≅ O') (c : F.obj X ≅ X')
    (uB : S.monoidal.tensorUnit ≅ O) (uA : T.monoidal.tensorUnit ≅ O')
    (b : X ⟶ P) (b' : X' ⟶ P')
    (hm : F.map i.hom ≫ μ.hom.app (P, O) ≫
      T.tensor.map (X := (F.obj P, F.obj O)) (Y := (P', O')) (aP.hom, aO.hom) =
      c.hom ≫ j.hom)
    (hb : i.hom ≫ S.tensor.map (X := (P, O)) (Y := (P, S.monoidal.tensorUnit))
      (𝟙 P, uB.inv) ≫ (S.monoidal.rightUnitor P).hom = b)
    (hb' : j.hom ≫ T.tensor.map (X := (P', O')) (Y := (P', T.monoidal.tensorUnit))
      (𝟙 P', uA.inv) ≫ (T.monoidal.rightUnitor P').hom = b')
    (hc : F.map b ≫ aP.hom = c.hom ≫ b') :
    μ.hom.app (P, S.monoidal.tensorUnit) ≫
      T.tensor.map (X := (F.obj P, F.obj S.monoidal.tensorUnit))
        (Y := (F.obj P, T.monoidal.tensorUnit))
        (𝟙 _, (F.mapIso uB ≪≫ aO ≪≫ uA.symm).hom) ≫
      (T.monoidal.rightUnitor (F.obj P)).hom =
        F.map (S.monoidal.rightUnitor P).hom := by
  let := S.monoidal
  let := T.monoidal
  have hi : IsIso (S.tensor.map (X := (P, O)) (Y := (P, S.monoidal.tensorUnit))
      (𝟙 P, uB.inv)) := by
    have : IsIso (Prod.mkHom (𝟙 P) uB.inv) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
    exact Functor.map_isIso _ _
  -- Test the unit square after the tensor-model and unit isomorphisms.
  apply (cancel_epi (F.map (i.hom ≫ S.tensor.map
    (X := (P, O)) (Y := (P, S.monoidal.tensorUnit)) (𝟙 P, uB.inv)))).mp
  apply (cancel_mono aP.hom).mp
  have hn : F.map (S.tensor.map (X := (P, O))
        (Y := (P, S.monoidal.tensorUnit)) (𝟙 P, uB.inv)) ≫
      μ.hom.app (P, S.monoidal.tensorUnit) =
    μ.hom.app (P, O) ≫ T.tensor.map (X := (F.obj P, F.obj O))
      (Y := (F.obj P, F.obj S.monoidal.tensorUnit)) (𝟙 (F.obj P), F.map uB.inv) := by
    simpa only [Functor.comp_map, Functor.prod_map, Functor.map_id] using
      μ.hom.naturality (X := (P, O)) (Y := (P, S.monoidal.tensorUnit)) (𝟙 P, uB.inv)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    CoefficientClosedStructure.tensor, tensor_map]
  rw [← MonoidalCategory.rightUnitor_naturality]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id_map_assoc, Category.comp_id, Category.id_comp]
  have hh := congrArg (fun f ↦ f ≫ (𝟙 P' ⊗ₘ uA.inv) ≫ (ρ_ P').hom) hm
  simp only [CoefficientClosedStructure.tensor, tensor_map, Category.assoc,
    tensorHom_comp_tensorHom_assoc, Category.comp_id] at hh
  erw [hh, hb', ← hc]
  rw [← F.map_comp_assoc, ← F.map_comp_assoc]
  simpa only [CoefficientClosedStructure.tensor, tensor_map, Category.assoc] using
    (congrArg (fun f ↦ F.map f ≫ aP.hom) hb).symm

end Generic

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})

private theorem summand_map
    {P P' Q Q' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') (p q n : ℤ) (h : p + q = n) :
    tensorSummand.{c, v, r} J R P Q p q n h ≫
      (((coefficientTotalTensor.{r, c, v} J R).map
        (X := (P, Q)) (Y := (P', Q')) (f, g)).f n) =
    (@MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R)).map
        (X := (P.X p, Q.X q)) (Y := (P'.X p, Q'.X q)) (f.f p, g.f q) ≫
      tensorSummand.{c, v, r} J R P' Q' p q n h := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  unfold coefficientTotalTensor
  rw [total_map_generic]
  exact HomologicalComplex.ι_mapBifunctorMap f g (curriedTensor _) (.up ℤ) p q n h

private theorem unit_flat : ∀ n : ℤ,
    SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r} (R := R)
      ((ringedTensorUnitComplex.{c, v, r} J R).X n) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  intro n
  unfold SheafOfModules.IsFlatOnSite
  by_cases hn : n = 0
  · subst n
    have h : ObjectProperty.flat (𝟙_ (RingedTensorModules.{c, v, r} J R)) :=
      ObjectProperty.flat_of_tensorIso (leftUnitor (𝟙_ (RingedTensorModules.{c, v, r} J R)))
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2
  · have hz := HomologicalComplex.isZero_single_obj_X (.up ℤ) 0
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) n hn
    have h : ObjectProperty.flat ((ringedTensorUnitComplex.{c, v, r} J R).X n) :=
      ObjectProperty.flat_of_isZero hz
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2

private theorem unit_kflat :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
      (ringedTensorUnitComplex.{c, v, r} J R) := by
  have : (ringedTensorUnitComplex.{c, v, r} J R).IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ n (by omega)
  exact SheafOfModules.isKFlatIndependentCoefficients_of_boundedAbove_flatOnSite
    R (ringedTensorUnitComplex.{c, v, r} J R) 0 (unit_flat.{c, v, r} J R)

private theorem pure_ext (M N L : RingedTensorModules.{c, v, r} J R)
    {f g : (SheafOfModules.monoidalCategory R).tensorObj M N ⟶ L}
    (h : ∀ V x y,
      f.val.app V (sheafTensorGenerator.{c, v, r} J R M N V x y) =
        g.val.app V (sheafTensorGenerator.{c, v, r} J R M N V x y)) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  let adj := PresheafOfModules.sheafificationAdjunction.{max c v r} (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R).obj)
  apply (adj.homEquiv (M.val ⊗ N.val) L).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h V x y

private theorem right_summand
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (b : (coefficientTotalTensor.{r, c, v} J R).obj
      (P, ringedTensorUnitComplex.{c, v, r} J R) ⟶ P)
    (hb : ∀ (n : ℤ) (h : n + 0 = n) (V : Cᵒᵖ) (a : R.obj.obj V)
      (x : (P.X n).val.obj V),
      (b.f n).val.app V (coefficientTensorGenerator.{r, c, v} J R P
        (ringedTensorUnitComplex.{c, v, r} J R) n 0 n h V x
        (ringedTensorUnitSection.{c, v, r} J R V a)) = a • x)
    (n : ℤ) :
    tensorSummand.{c, v, r} J R P (ringedTensorUnitComplex.{c, v, r} J R)
        n 0 n (add_zero n) ≫ b.f n =
      (@MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R)).map
        (X := (P.X n, (ringedTensorUnitComplex.{c, v, r} J R).X 0))
        (Y := (P.X n, (SheafOfModules.monoidalCategory R).tensorUnit))
        (𝟙 _, (HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
          (SheafOfModules.unit ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))).hom) ≫
      ((SheafOfModules.monoidalCategory R).rightUnitor (P.X n)).hom := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let e := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
    (SheafOfModules.unit ((sheafCompose J
      (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
  apply pure_ext.{c, v, r} J R (P.X n) _ _
  intro V x a
  have ha : e.inv.val.app V (e.hom.val.app V a) = a :=
    congrArg (fun f ↦ f.val.app V a) e.hom_inv_id
  have hh := hb n (add_zero n) V (e.hom.val.app V a) x
  change (b.f n).val.app V
    ((tensorSummand.{c, v, r} J R P (ringedTensorUnitComplex.{c, v, r} J R)
      n 0 n (add_zero n)).val.app V
        (sheafTensorGenerator.{c, v, r} J R (P.X n)
          ((ringedTensorUnitComplex.{c, v, r} J R).X 0) V x
            (e.inv.val.app V (e.hom.val.app V a)))) = _ at hh
  rw [ha] at hh
  refine hh.trans ?_
  symm
  change ((ρ_ (P.X n)).hom).val.app V
    (((𝟙 (P.X n)) ⊗ₘ e.hom).val.app V
      (CochainPullback.moduleTmul.{max c v r, c, v} _ _ V x a)) = _
  rw [CochainPullback.moduleTmul_map.{max c v r, c, v}]
  exact RingedDerivedNative.pureTensor_rightUnitor.{c, v, r} J R
    (P.X n) V (e.hom.val.app V a) x

private theorem total_hom_ext
    (P Q Z : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    {f g : (coefficientTotalTensor.{r, c, v} J R).obj (P, Q) ⟶ Z}
    (h : ∀ (n p q : ℤ) (hpq : p + q = n),
      tensorSummand.{c, v, r} J R P Q p q n hpq ≫ f.f n =
        tensorSummand.{c, v, r} J R P Q p q n hpq ≫ g.f n) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
    (K₁ := P) (K₂ := Q) (F := curriedTensor (RingedTensorModules.{c, v, r} J R))
    (c := .up ℤ)
  intro p q hpq
  exact h n p q hpq

-- Use totalization through the summand API in the remaining proofs.
attribute [local irreducible] coefficientTotalTensor tensorSummand

variable {D : Type d} [Category.{vd} D] (J' : GrothendieckTopology D)
  [HasSheafify J' AddCommGrpCat.{max d vd s}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{max d vd s}]
  (R' : Sheaf J' CommRingCat.{max d vd s})
  (U : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{d, vd, s} J' R')
  [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]

omit [PreservesFiniteLimits U] [PreservesFiniteColimits U] in
private theorem right_unit_chain
    (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (bB : (coefficientTotalTensor.{r, c, v} J R).obj
      (P, ringedTensorUnitComplex.{c, v, r} J R) ≅ P)
    (bA : (coefficientTotalTensor.{s, d, vd} J' R').obj
      ((U.mapHomologicalComplex (.up ℤ)).obj P,
        ringedTensorUnitComplex.{d, vd, s} J' R') ≅
      (U.mapHomologicalComplex (.up ℤ)).obj P)
    (hbB : ∀ (n : ℤ) (h : n + 0 = n) (V : Cᵒᵖ) (a : R.obj.obj V)
      (x : (P.X n).val.obj V),
      (bB.hom.f n).val.app V (coefficientTensorGenerator.{r, c, v} J R P
        (ringedTensorUnitComplex.{c, v, r} J R) n 0 n h V x
        (ringedTensorUnitSection.{c, v, r} J R V a)) = a • x)
    (hbA : ∀ (n : ℤ) (h : n + 0 = n) (V : Dᵒᵖ) (a : R'.obj.obj V)
      (x : (((U.mapHomologicalComplex (.up ℤ)).obj P).X n).val.obj V),
      (bA.hom.f n).val.app V (coefficientTensorGenerator.{s, d, vd} J' R'
        ((U.mapHomologicalComplex (.up ℤ)).obj P)
        (ringedTensorUnitComplex.{d, vd, s} J' R') n 0 n h V x
        (ringedTensorUnitSection.{d, vd, s} J' R' V a)) = a • x) :
    (U.mapHomologicalComplex (.up ℤ)).map bB.hom =
      chain.hom.app (P, ringedTensorUnitComplex.{c, v, r} J R) ≫
      (coefficientTotalTensor.{s, d, vd} J' R').map
        (X := ((U.mapHomologicalComplex (.up ℤ)).obj P,
          (U.mapHomologicalComplex (.up ℤ)).obj (ringedTensorUnitComplex.{c, v, r} J R)))
        (Y := ((U.mapHomologicalComplex (.up ℤ)).obj P,
          ringedTensorUnitComplex.{d, vd, s} J' R'))
        (𝟙 _, ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
          (SheafOfModules.unit ((sheafCompose J
            (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ≪≫
          (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit).hom) ≫
        bA.hom := by
  let F := U.mapHomologicalComplex (.up ℤ)
  let O := ringedTensorUnitComplex.{c, v, r} J R
  let O' := ringedTensorUnitComplex.{d, vd, s} J' R'
  let e : F.obj O ≅ O' :=
    (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ≪≫
    (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit
  change F.map bB.hom = chain.hom.app (P, O) ≫
    (coefficientTotalTensor.{s, d, vd} J' R').map
      (X := (F.obj P, F.obj O)) (Y := (F.obj P, O')) (𝟙 _, e.hom) ≫ bA.hom
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let := SheafOfModules.isMonoidal_W_independentCoefficients R'
  let := SheafOfModules.monoidalCategory R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients R'
  let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients R'
  -- Test target summands after the inverse comparison; U need not preserve their coproduct.
  apply (cancel_epi (chain.inv.app (P, O))).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  apply total_hom_ext.{d, vd, s} J' R' (F.obj P) (F.obj O) (F.obj P)
  intro n p q hpq
  have hi : tensorSummand.{d, vd, s} J' R' (F.obj P) (F.obj O) p q n hpq ≫
      (chain.inv.app (P, O)).f n =
    u.tensor.inv.app (P.X p, O.X q) ≫
      U.map (tensorSummand.{c, v, r} J R P O p q n hpq) := by
    apply (cancel_mono ((chain.hom.app (P, O)).f n)).mp
    have hh : (chain.inv.app (P, O)).f n ≫ (chain.hom.app (P, O)).f n = 𝟙 _ :=
      congrArg (fun f ↦ f.f n) (chain.app (P, O)).inv_hom_id
    simp only [Category.assoc, hh, summand, Iso.inv_hom_id_app_assoc]
    exact Category.comp_id _
  simp only [HomologicalComplex.comp_f]
  change tensorSummand.{d, vd, s} J' R' (F.obj P) (F.obj O) p q n hpq ≫
    (chain.inv.app (P, O)).f n ≫ U.map (bB.hom.f n) =
    tensorSummand.{d, vd, s} J' R' (F.obj P) (F.obj O) p q n hpq ≫
      (((coefficientTotalTensor.{s, d, vd} J' R').map
        (X := (F.obj P, F.obj O)) (Y := (F.obj P, O')) (𝟙 _, e.hom)).f n) ≫
          bA.hom.f n
  by_cases hq : q = 0
  · subst q
    have hn : p = n := by omega
    subst p
    rw [reassoc_of% hi, ← U.map_comp,
      right_summand.{c, v, r} J R P bB.hom hbB n,
      reassoc_of% (summand_map.{d, vd, s} J' R' (𝟙 (F.obj P)) e.hom
        n 0 n hpq),
      right_summand.{d, vd, s} J' R' (F.obj P) bA.hom hbA n]
    let sB := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))
    let sA := HomologicalComplex.singleObjXSelf (.up ℤ) (0 : ℤ)
      (SheafOfModules.unit ((sheafCompose J'
        (forget₂ CommRingCat.{max d vd s} RingCat.{max d vd s})).obj R'))
    -- The normalized chain unit has the prescribed underived degree-zero component.
    have he : e.hom.f 0 ≫ sA.hom = U.map sB.hom ≫ u.coherence.unit.hom := by
      dsimp only [e, Iso.trans_hom, Functor.mapIso_hom, HomologicalComplex.comp_f,
        Iso.app_hom, F, O, O', ringedTensorUnitComplex, sA, sB]
      rw [HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
        HomologicalComplex.single_map_f_self]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
        Category.comp_id]
    let tB := @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R)
    let tA := @MonoidalCategory.tensor _ _ (SheafOfModules.monoidalCategory R')
    let X := U.obj (P.X n)
    let I := (SheafOfModules.monoidalCategory R).tensorUnit
    let I' := (SheafOfModules.monoidalCategory R').tensorUnit
    change u.tensor.inv.app (P.X n, O.X 0) ≫
        U.map (tB.map (X := (P.X n, O.X 0)) (Y := (P.X n, I))
          (𝟙 _, sB.hom) ≫ (ρ_ (P.X n)).hom) =
      tA.map (X := (X, U.obj (O.X 0))) (Y := (X, O'.X 0)) (𝟙 _, e.hom.f 0) ≫
        tA.map (X := (X, O'.X 0)) (Y := (X, I')) (𝟙 _, sA.hom) ≫ (ρ_ X).hom
    have hn : U.map (tB.map (X := (P.X n, O.X 0)) (Y := (P.X n, I))
        (𝟙 _, sB.hom)) ≫ u.tensor.hom.app (P.X n, I) =
      u.tensor.hom.app (P.X n, O.X 0) ≫
        tA.map (X := (X, U.obj (O.X 0))) (Y := (X, U.obj I))
          (𝟙 _, U.map sB.hom) := by
      simpa only [tA, tB, X, Functor.comp_map, Functor.prod_map, Functor.map_id] using
        u.tensor.hom.naturality (X := (P.X n, O.X 0)) (Y := (P.X n, I))
          (Prod.mkHom (𝟙 (P.X n)) sB.hom)
    have hp : (Prod.mkHom (𝟙 X) (e.hom.f 0)) ≫ (Prod.mkHom (𝟙 X) sA.hom) =
        (Prod.mkHom (𝟙 X) (U.map sB.hom)) ≫ (Prod.mkHom (𝟙 X) u.coherence.unit.hom) := by
      apply Prod.ext
      · rfl
      · exact he
    have ht : tA.map (X := (X, U.obj (O.X 0))) (Y := (X, O'.X 0))
        (𝟙 _, e.hom.f 0) ≫ tA.map (X := (X, O'.X 0)) (Y := (X, I')) (𝟙 _, sA.hom) =
      tA.map (X := (X, U.obj (O.X 0))) (Y := (X, U.obj I)) (𝟙 _, U.map sB.hom) ≫
        tA.map (X := (X, U.obj I)) (Y := (X, I')) (𝟙 _, u.coherence.unit.hom) := by
      simpa only [Functor.map_comp] using
        congrArg (fun f : (X, U.obj (O.X 0)) ⟶ (X, I') ↦ tA.map f) hp
    apply (cancel_epi (u.tensor.hom.app (P.X n, O.X 0))).mp
    rw [Iso.hom_inv_id_app_assoc, Functor.map_comp, ← u.coherence.right_unit (P.X n)]
    rw [reassoc_of% hn]
    simpa only [Category.assoc] using
      congrArg (fun f ↦ u.tensor.hom.app (P.X n, O.X 0) ≫ f ≫ (ρ_ X).hom) ht.symm
  · apply IsZero.eq_of_src
    apply (tensorLeft ((F.obj P).X p)).map_isZero
    exact U.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ q hq)

variable [HasDerivedCategory.{wb} (RingedTensorModules.{c, v, r} J R)]
  [HasDerivedCategory.{wa} (RingedTensorModules.{d, vd, s} J' R')]
  [∀ I : Type (max c v r), PreservesLimitsOfShape (Discrete I) U]
  [U.PreservesKInjectiveComplexes]
  (u : Underived.{c, v, r, d, vd, s} J R J' R' U)
  (SB : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, wb} J R))
  (TB : CoefficientTensorModels.{r, c, v, wb} J R SB)
  (βB : @SymmetricCategory (DerivedCategory (RingedTensorModules.{c, v, r} J R))
    _ SB.monoidal)
  (cB : RingedDerivedTensorCoherence.{c, v, r, wb} J R SB TB βB)
  (SA : CoefficientClosedStructure (derivedInternalHomOfUniverses.{d, vd, s, wa} J' R'))
  (TA : CoefficientTensorModels.{s, d, vd, wa} J' R' SA)
  (βA : @SymmetricCategory (DerivedCategory (RingedTensorModules.{d, vd, s} J' R'))
    _ SA.monoidal)
  (cA : RingedDerivedTensorCoherence.{d, vd, s, wa} J' R' SA TA βA)

include u SB TB βB cB SA TA βA cA
-- Retain the inherited comparison parameters in the existing public signature.
set_option linter.unusedSectionVars false in
/--
The representative unit calculation for the right unitor is reduced to the
componentwise model equation for the normalized tensor comparison.
(blueprint: lem-sf-ringed-forget-tensor-right-representatives)
Proof in words: apply the representative model equation to the unit complex and
`P`. Naturality of the tensor-model comparisons, together with the exact-functor
localization factor, reduces the assertion to the unit square on total complexes.
In degree `n`, restrict to the only nonzero unit summand: `(0,n)` on the left
and `(n,0)` on the right. Use the summand formula and the single-complex comparison
in the displayed composite to obtain `u.coherence.right_unit`.
The corresponding unitor model equations of `cB` and `cA` transport this equality
back to the derived category. Local pure tensors and sheafification detect the
component maps, so no hypothesis of generation by global sections is needed.
Source: Stacks Project, sites-cohomology.tex, Tags 0FPT and 06YU.
-/
theorem ringed_forget_tensor_right_representatives
    (hU : ∀ P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ,
      P.IsKFlatIndependentCoefficients →
      (∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
        (R := R) (P.X p)) →
      CochainComplex.IsKFlatIndependentCoefficients (R := R')
        ((U.mapHomologicalComplex (.up ℤ)).obj P) ∧
      ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{d, vd, max d vd s, max d vd s}
        (R := R') (U.obj (P.X p)))
    (chain : coefficientTotalTensor.{r, c, v} J R ⋙ U.mapHomologicalComplex (.up ℤ) ≅
      ((U.mapHomologicalComplex (.up ℤ)).prod (U.mapHomologicalComplex (.up ℤ))) ⋙
        coefficientTotalTensor.{s, d, vd} J' R')
    (summand : ∀ (P Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (p q n : ℤ) (hpq : p + q = n),
      U.map (tensorSummand.{c, v, r} J R P Q p q n hpq) ≫ (chain.hom.app (P, Q)).f n =
        u.tensor.hom.app (P.X p, Q.X q) ≫
          tensorSummand.{d, vd, s} J' R' ((U.mapHomologicalComplex (.up ℤ)).obj P)
            ((U.mapHomologicalComplex (.up ℤ)).obj Q) p q n hpq)
    (μ : SB.tensor ⋙ U.mapDerivedCategory ≅
      (U.mapDerivedCategory.prod U.mapDerivedCategory) ⋙ SA.tensor)
    (hμ : RepresentativeModel.{c, v, r, d, vd, s, wb, wa}
      J R J' R' U SB TB SA TA chain μ.hom)
    (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    (hP : P.IsKFlatIndependentCoefficients)
    (fP : ∀ p : ℤ, SheafOfModules.IsFlatOnSite.{c, v, max c v r, max c v r}
      (R := R) (P.X p)) :
    μ.hom.app (DerivedCategory.Q.obj P, SB.monoidal.tensorUnit) ≫
        SA.tensor.map
          (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
            U.mapDerivedCategory.obj SB.monoidal.tensorUnit))
          (Y := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P), SA.monoidal.tensorUnit))
          (𝟙 _, (U.mapDerivedCategory.mapIso cB.unitIso ≪≫
              U.mapDerivedCategoryFactors.app (ringedTensorUnitComplex.{c, v, r} J R) ≪≫
              DerivedCategory.Q.mapIso
                ((HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
                  (SheafOfModules.unit ((sheafCompose J
                    (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R))) ≪≫
              DerivedCategory.Q.mapIso
                ((HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit) ≪≫
              cA.unitIso.symm).hom) ≫
        (SA.monoidal.rightUnitor (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P))).hom =
      U.mapDerivedCategory.map (SB.monoidal.rightUnitor (DerivedCategory.Q.obj P)).hom := by
  let F := U.mapHomologicalComplex (.up ℤ)
  let O := ringedTensorUnitComplex.{c, v, r} J R
  let O' := ringedTensorUnitComplex.{d, vd, s} J' R'
  let e : F.obj O ≅ O' :=
    (HomologicalComplex.singleMapHomologicalComplex U (.up ℤ) 0).app
      (SheafOfModules.unit ((sheafCompose J
        (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R)) ≪≫
    (HomologicalComplex.single _ (.up ℤ) (0 : ℤ)).mapIso u.coherence.unit
  have hO := unit_kflat.{c, v, r} J R
  have fO := unit_flat.{c, v, r} J R
  have hO' := unit_kflat.{d, vd, s} J' R'
  have hUP := (hU P hP fP).1
  have hUO := (hU O hO fO).1
  obtain ⟨bB, hbB, heB⟩ := cB.rightUnitor_model P hP
  obtain ⟨bA, hbA, heA⟩ := cA.rightUnitor_model (F.obj P) hUP
  rw [cB.tensorIso_both P O hP hO] at heB
  rw [cA.tensorIso_both (F.obj P) O' hUP hO'] at heA
  have hc := right_unit_chain.{c, v, r, d, vd, s}
    J R J' R' U u chain summand P bB bA hbB hbA
  let α := U.mapDerivedCategoryFactors
  let t := (coefficientTotalTensor.{s, d, vd} J' R').mapIso
    ((Iso.refl (F.obj P)).prod e)
  let c := α.app ((coefficientTotalTensor.{r, c, v} J R).obj (P, O)) ≪≫
    DerivedCategory.Q.mapIso (chain.app (P, O)) ≪≫ DerivedCategory.Q.mapIso t
  have hm : U.mapDerivedCategory.map (TB.iso J R SB P O hP hO).hom ≫
      μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj O) ≫
      SA.tensor.map
        (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
          U.mapDerivedCategory.obj (DerivedCategory.Q.obj O)))
        (Y := (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj O'))
        ((α.app P).hom, (α.app O ≪≫ DerivedCategory.Q.mapIso e).hom) =
    c.hom ≫ (TA.iso J' R' SA (F.obj P) O' hUP hO').hom := by
    have hm := hμ P O hP hO hUP hUO fP fO
    have hn := cA.tensorIso_naturality (F.obj P) (F.obj O) (F.obj P) O'
      (Or.inl hUP) (Or.inl hUP) (𝟙 _) e.hom
    rw [cA.tensorIso_both _ _ hUP hUO, cA.tensorIso_both _ _ hUP hO'] at hn
    let := SA.monoidal
    simp only [Functor.map_id] at hn
    calc
      _ = U.mapDerivedCategory.map (TB.iso J R SB P O hP hO).hom ≫
          μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj O) ≫
          SA.tensor.map (X := (U.mapDerivedCategory.obj (DerivedCategory.Q.obj P),
              U.mapDerivedCategory.obj (DerivedCategory.Q.obj O)))
            (Y := (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj (F.obj O)))
            ((α.app P).hom, (α.app O).hom) ≫
          SA.tensor.map (X := (DerivedCategory.Q.obj (F.obj P),
              DerivedCategory.Q.obj (F.obj O)))
            (Y := (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj O'))
            (𝟙 _, DerivedCategory.Q.map e.hom) := by
        simp only [Iso.trans_hom, Functor.mapIso_hom, CoefficientClosedStructure.tensor,
          tensor_map, tensorHom_comp_tensorHom, Category.comp_id]
      _ = (α.app _).hom ≫ DerivedCategory.Q.map (chain.hom.app (P, O)) ≫
          (TA.iso J' R' SA (F.obj P) (F.obj O) hUP hUO).hom ≫
          SA.tensor.map (X := (DerivedCategory.Q.obj (F.obj P),
              DerivedCategory.Q.obj (F.obj O)))
            (Y := (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj O'))
            (𝟙 _, DerivedCategory.Q.map e.hom) := by
        simpa only [Category.assoc, α, F, Iso.app_hom] using
          congrArg (fun f ↦ f ≫ SA.tensor.map
          (X := (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj (F.obj O)))
          (Y := (DerivedCategory.Q.obj (F.obj P), DerivedCategory.Q.obj O'))
          (𝟙 _, DerivedCategory.Q.map e.hom)) hm
      _ = _ := by
        erw [← hn]
        simp only [c, Iso.trans_hom, Functor.mapIso_hom, t, Iso.prod_hom,
          Iso.refl_hom, Iso.app_hom, Prod.mkHom, Category.assoc, F, O']
  have hf : U.mapDerivedCategory.map (DerivedCategory.Q.map bB.hom) ≫
      (α.app P).hom = c.hom ≫ DerivedCategory.Q.map bA.hom := by
    have hn := α.hom.naturality bB.hom
    change U.mapDerivedCategory.map (DerivedCategory.Q.map bB.hom) ≫ (α.app P).hom =
      (α.app _).hom ≫ DerivedCategory.Q.map (F.map bB.hom) at hn
    rw [hn, hc]
    simp only [Functor.map_comp, c, Iso.trans_hom, Functor.mapIso_hom,
      t, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom, Iso.app_hom,
      Prod.mkHom, Category.assoc, O, e, F]
  have hh := right_unit_of_models SB SA U.mapDerivedCategory μ
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj O)
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{r, c, v} J R).obj (P, O)))
    (DerivedCategory.Q.obj (F.obj P)) (DerivedCategory.Q.obj O')
    (DerivedCategory.Q.obj ((coefficientTotalTensor.{s, d, vd} J' R').obj (F.obj P, O')))
    (TB.iso J R SB P O hP hO) (TA.iso J' R' SA (F.obj P) O' hUP hO')
    (α.app P) (α.app O ≪≫ DerivedCategory.Q.mapIso e) c cB.unitIso cA.unitIso
    (DerivedCategory.Q.map bB.hom) (DerivedCategory.Q.map bA.hom) hm heB heA hf
  simpa only [e, Functor.mapIso_trans, Iso.trans_assoc] using hh

end CategoryTheory.RingedForgetTensorTransposition
