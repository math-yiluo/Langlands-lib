/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.KFlatFixedTensor.KFlatFixedTensorTriangulatedSupplement
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Combinatorics.SetFamily.FourFunctions

/-! # Normalized derived tensor with a flat degree-zero sheaf

Source: Stacks Project, sites-cohomology.tex, Tags 06YN and 06YU;
derived.tex, Tag 015F; homology.tex, Tag 010N; more-algebra.tex, Tag 0FNH.
(blueprint: lem-pur-flat-single-derived-normalization)

The derived tensor and its resolving comparisons are the published site descent data.
The normalization is imposed on every unbounded input complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.FlatSingleDerivedNormalization

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})

attribute [local instance 2000] KFlatFixedTensor.tensorHasMapBifunctor

/-- The existing single-summand totalization isomorphism, with no flatness needed.
Its component is the projection onto bidegree (i,0), using the identity of L.
Source: Stacks 06YU and the direct-sum totalization convention 012Z
(blueprint: lem-pur-flat-single-derived-normalization). -/
abbrev collapse (L : KFlatFixedTensor.Modules R) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso
    (KFlatFixedTensor.ordinaryTensor R) L

private theorem flat_tensor_exact (L : KFlatFixedTensor.Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L) :
    PreservesFiniteLimits (tensorRight L) ∧ PreservesFiniteColimits (tensorRight L) := by
  have h := hL
  change PreservesFiniteLimits (siteSheafTensorRight (A := R) L) ∧
    PreservesFiniteColimits (siteSheafTensorRight (A := R) L) at h
  have := h.1
  have := h.2
  exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R L),
    preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R L)⟩

private theorem flat_of_isZero (L : KFlatFixedTensor.Modules R) (hL : IsZero L) :
    IsFlatOnSite (J := J) (R := R) L := by
  have hT : IsZero (tensorRight L) := (tensorRight L).isZero (fun M ↦
    Functor.map_isZero (tensorLeft M) hL)
  have := (tensorRight L).preservesLimitsOfSize_of_isZero hT
  have := (tensorRight L).preservesColimitsOfSize_of_isZero hT
  have : PreservesFiniteLimits (siteSheafTensorRight (A := R) L) :=
    preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R L).symm
  have : PreservesFiniteColimits (siteSheafTensorRight (A := R) L) :=
    preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R L).symm
  change PreservesFiniteLimits (siteSheafTensorRight (A := R) L) ∧
    PreservesFiniteColimits (siteSheafTensorRight (A := R) L)
  exact ⟨inferInstance, inferInstance⟩

private theorem single_flat_terms (L : KFlatFixedTensor.Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L) :
    ∀ i : ℤ, IsFlatOnSite (J := J) (R := R)
      (((CochainComplex.singleFunctor _ 0).obj L).X i) := by
  intro i
  by_cases hi : i = 0
  · subst i
    have e := HomologicalComplex.singleObjXSelf (.up ℤ) 0 L
    obtain ⟨hl, hc⟩ := flat_tensor_exact R L hL
    have := hl
    have := hc
    have eT : tensorRight _ ≅ tensorRight L :=
      (KFlatFixedTensor.ordinaryTensor R).flip.mapIso e
    have : PreservesFiniteLimits (tensorRight (((CochainComplex.singleFunctor _ 0).obj L).X 0)) :=
      preservesFiniteLimits_of_natIso eT.symm
    have : PreservesFiniteColimits (tensorRight (((CochainComplex.singleFunctor _ 0).obj L).X 0)) :=
      preservesFiniteColimits_of_natIso eT.symm
    exact ⟨preservesFiniteLimits_of_natIso (siteSheafTensorRightIso R _).symm,
      preservesFiniteColimits_of_natIso (siteSheafTensorRightIso R _).symm⟩
  · exact flat_of_isZero R _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hi)

private theorem single_kFlat (L : KFlatFixedTensor.Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L) :
    CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor _ 0).obj L) := by
  obtain ⟨hl, hc⟩ := flat_tensor_exact R L hL
  have := hl
  have := hc
  intro E hE i
  apply HomologicalComplex.ExactAt.of_iso (L :=
    CochainComplex.mapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
      (KFlatFixedTensor.ordinaryTensor R)) (e := ((collapse R L).app E).symm)
  exact ShortComplex.Exact.map (hE i) (tensorRight L)

section GenericCollapse

variable {M : Type*} [Category* M] [Preadditive M] [HasZeroObject M]
  (T : M ⥤ M ⥤ M) [T.Additive] [∀ X, (T.obj X).Additive]
  [∀ A B : CochainComplex M ℤ, CochainComplex.HasMapBifunctor A B T]

private abbrev collapseGeneric (L : M) :=
  CochainComplex.map₂HomologicalComplexFlipObjSingleIso T L

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem collapse_ι_generic (L : M)
    (E : CochainComplex M ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
        T (.up ℤ) i 0 i (Int.add_zero i) ≫
      ((collapseGeneric T L).hom.app E).f i =
        (T.obj (E.X i)).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom := by
  dsimp [collapseGeneric, CochainComplex.map₂HomologicalComplexFlipObjSingleIso,
    CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    HomologicalComplex.Hom.isoOfComponents]
  erw [HomologicalComplex.ι_mapBifunctorFlipIso_inv_assoc]
  simp [CochainComplex.mapBifunctorSingle₁XIso, HomologicalComplex.singleObjXSelf]

variable [∀ X, (T.flip.obj X).Additive]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
private theorem collapse_shift_generic (L : M) :
    NatTrans.CommShift (collapseGeneric T L).hom ℤ := by
  constructor
  intro n
  apply NatTrans.ext
  funext E
  apply HomologicalComplex.Hom.ext
  funext i
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    HomologicalComplex.comp_f]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  by_cases hq : q = 0
  · subst q
    have hp : p = i := by simpa using hpq
    subst p
    simp only [CochainComplex.shiftFunctor_map_f',
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f, Category.comp_id]
    change _ ≫ (CochainComplex.mapBifunctorShift₁Iso E
      ((CochainComplex.singleFunctor _ 0).obj L) T n).hom.f i
      ≫ _ = _
    erw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f_assoc
      E ((CochainComplex.singleFunctor _ 0).obj L) T
      n i 0 i hpq (i + n) (i + n) rfl rfl]
    simp only [CochainComplex.shiftFunctorObjXIso]
    simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
      Category.id_comp]
    erw [collapse_ι_generic, collapse_ι_generic]
    simp
  · apply IsZero.eq_of_src
    exact Functor.map_isZero (T.obj _)
      (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

end GenericCollapse

private theorem collapse_ι (L : KFlatFixedTensor.Modules R)
    (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ) (i : ℤ) :
    HomologicalComplex.ιMapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
        (KFlatFixedTensor.ordinaryTensor R) (.up ℤ) i 0 i (Int.add_zero i) ≫
      ((collapse R L).hom.app E).f i =
        ((KFlatFixedTensor.ordinaryTensor R).obj (E.X i)).map
          (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom :=
  collapse_ι_generic (KFlatFixedTensor.ordinaryTensor R) L E i

private theorem collapse_shift (L : KFlatFixedTensor.Modules R) :
    NatTrans.CommShift (collapse R L).hom ℤ :=
  collapse_shift_generic (KFlatFixedTensor.ordinaryTensor R) L

private theorem localized_iso_commShift
    {A B D : Type*} [Category* A] [Category* B] [Category* D]
    [HasShift A ℤ] [HasShift B ℤ] [HasShift D ℤ]
    (Q : A ⥤ B) (W : MorphismProperty A) [Q.IsLocalization W] [Q.CommShift ℤ]
    (F G : B ⥤ D) [F.CommShift ℤ] [G.CommShift ℤ]
    (e : Q ⋙ F ≅ Q ⋙ G) [NatTrans.CommShift e.hom ℤ] :
    NatTrans.CommShift (Localization.liftNatIso Q W _ _ F G e).hom ℤ := by
  let eta := Localization.liftNatIso Q W _ _ F G e
  have he : Functor.whiskerLeft Q eta.hom = e.hom := by
    ext X
    simp [eta, Localization.liftNatTrans_app, Localization.Lifting.iso]
  have : NatTrans.CommShift (Functor.whiskerLeft Q eta.hom) ℤ := he.symm ▸ inferInstance
  have : Q.EssSurj := Localization.essSurj Q W
  exact NatTrans.CommShift.of_whiskerLeft eta.hom Q (fun X ↦
    ⟨Q.objPreimage X, (Q.objObjPreimageIso X).inv, inferInstance⟩)

set_option backward.isDefEq.respectTransparency false in
private def termwiseHomologyIso
    {M : Type*} [Category* M] [Abelian M]
    (F : M ⥤ M) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (i : ℤ) :
    F.mapHomologicalComplex (.up ℤ) ⋙ HomologicalComplex.homologyFunctor M (.up ℤ) i ≅
      HomologicalComplex.homologyFunctor M (.up ℤ) i ⋙ F :=
  NatIso.ofComponents (fun E ↦ (E.sc i).mapHomologyIso F) (fun f ↦
    ShortComplex.mapHomologyIso_hom_naturality
      ((HomologicalComplex.shortComplexFunctor M (.up ℤ) i).map f) F)

variable [HasDerivedCategory.{w} (KFlatFixedTensor.Modules R)]

/-- Tensor with Q(L[0]) using the specified site-derived tensor, with no new choice.
Source: Stacks 06YU (blueprint: lem-pur-flat-single-derived-normalization). -/
abbrev derived (L : KFlatFixedTensor.Modules R) :=
  (KFlatFixedTensor.derivedTensor R).flip.obj
    (DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj L))

/-- Flat degree-zero tensor is termwise on every unbounded complex, normalized by
fixed-factor descent, and compatible with integer shifts, triangles and cohomology.
Source: Stacks 06YN, 06YU, 015F, 010N and 0FNH
(blueprint: lem-pur-flat-single-derived-normalization).

Proof plan:
1. By def-pc-flat-sheaf-modules, tensorRight L is exact; the canonical
   siteSheafTensorRightIso identifies it with the defining site tensor. Additivity
   comes from lem-pc-sheaf-modules-tensor-closed. Tensor with zero is zero.
2. In the direct-sum total tensor with L[0] only (i,0) survives. Its projection
   and inclusion are inverse, natural on all complexes, and its differential is
   d tensor 1. This is collapse, the existing BifunctorSingle construction.
3. Apply lem-weil-pbc-exact-functor-complex-cohomology. Exact tensor preserves
   acyclicity, so the single complex is K-flat by def-pc-kflat-complex. Its terms
   are L and zero, hence flat.
4. Apply situation-conventions to tensorRight L.
   Its mapDerivedCategoryFactors is phi; its termwise shift is degreewise identity.
5. Apply lem-weil-pbc-kflat-fixed-tensor-triangulated to L[0]. Invert its right
   comparison to obtain chi on every complex, normalized by representativeIso on
   resolving inputs. Compose chi with Q(collapse), then phi inverse. Extend this
   natural isomorphism uniquely along Q by lem-weil-pbc-localization-universal-property.
   This defines eta and gives the displayed normalization for every input.
6. By lem-weil-pbc-total-tensor-integer-shifts, shifting the first total factor
   is unsigned. Both routes through collapse are identity on the surviving summand;
   the shifted differential is (-1)^n times d tensor 1 for every integer n.
   The shift square for eta follows on representatives and hence by localization.
7. Naturality at the third arrow of a distinguished triangle, together with this
   shift square, gives compatibility with its connecting morphism. Both functors
   are triangulated by the two factorization theorems.
8. Apply H^i to eta followed by phi, then the canonical cycle-and-boundary
   isomorphism ShortComplex.mapHomologyIso. The homologyFunctorFactors isomorphisms
   identify H^i(QE) with H^i(E). Localization extends this natural family and its
   inverse to D(R), with exactly the stated representative value. No bound is used. -/
theorem flat_single_derived_normalization (L : KFlatFixedTensor.Modules R)
    (hL : IsFlatOnSite (J := J) (R := R) L) :
    ∃ hK : CochainComplex.IsKFlatIndependentCoefficients
      ((CochainComplex.singleFunctor _ 0).obj L),
    ∃ hF : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R)
      (((CochainComplex.singleFunctor _ 0).obj L).X i),
    ∃ hLim : PreservesFiniteLimits (tensorRight L),
    ∃ hCol : PreservesFiniteColimits (tensorRight L),
    (fun [_lim : PreservesFiniteLimits (tensorRight L)]
      [_col : PreservesFiniteColimits (tensorRight L)] ↦
      NatTrans.CommShift (collapse R L).hom ℤ ∧
      (∀ (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ) (i : ℤ),
        HomologicalComplex.ιMapBifunctor E ((CochainComplex.singleFunctor _ 0).obj L)
            (KFlatFixedTensor.ordinaryTensor R) (.up ℤ) i 0 i (Int.add_zero i) ≫
          ((collapse R L).hom.app E).f i =
            ((KFlatFixedTensor.ordinaryTensor R).obj (E.X i)).map
              (HomologicalComplex.singleObjXSelf (.up ℤ) 0 L).hom) ∧
      (∀ (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ) (n i : ℤ),
        (((tensorRight L).mapCochainComplexShiftIso n).hom.app E).f i = 𝟙 _) ∧
      (∀ (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ) (n i j : ℤ),
        (((tensorRight L).mapHomologicalComplex (.up ℤ)).obj (E⟦n⟧)).d i j =
          n.negOnePow • (tensorRight L).map (E.d (i + n) (j + n))) ∧
      ∃ s : (derived R L).CommShift ℤ,
      (fun [_shift : (derived R L).CommShift ℤ] ↦
        (derived R L).IsTriangulated ∧
        ∃ chi : DerivedCategory.Q ⋙ derived R L ≅
            (KFlatFixedTensor.totalTensor R).flip.obj
              ((CochainComplex.singleFunctor _ 0).obj L) ⋙ DerivedCategory.Q,
          NatTrans.CommShift chi.hom ℤ ∧
          (∀ (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ)
            (hE : CochainComplex.IsKFlatIndependentCoefficients E)
            (hf : ∀ i : ℤ, IsFlatOnSite (J := J) (R := R) (E.X i)),
            chi.app E = (KFlatFixedTensor.representativeIso R E
              ((CochainComplex.singleFunctor _ 0).obj L) hE hK hf hF).symm) ∧
          ∃ eta : derived R L ≅ (tensorRight L).mapDerivedCategory,
            NatTrans.CommShift eta.hom ℤ ∧
            (∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
              eta.app (DerivedCategory.Q.obj E) ≪≫
                  (tensorRight L).mapDerivedCategoryFactors.app E =
                chi.app E ≪≫ DerivedCategory.Q.mapIso ((collapse R L).app E)) ∧
            (∀ i : ℤ, ∃ c : derived R L ⋙
                  DerivedCategory.homologyFunctor (KFlatFixedTensor.Modules R) i ≅
                DerivedCategory.homologyFunctor (KFlatFixedTensor.Modules R) i ⋙ tensorRight L,
              ∀ E : CochainComplex (KFlatFixedTensor.Modules R) ℤ,
                c.app (DerivedCategory.Q.obj E) ≪≫ (tensorRight L).mapIso
                    ((DerivedCategory.homologyFunctorFactors _ i).app E) =
                  (DerivedCategory.homologyFunctor _ i).mapIso
                      (chi.app E ≪≫ DerivedCategory.Q.mapIso ((collapse R L).app E)) ≪≫
                    (DerivedCategory.homologyFunctorFactors _ i).app
                      (((tensorRight L).mapHomologicalComplex (.up ℤ)).obj E) ≪≫
                    (E.sc i).mapHomologyIso (tensorRight L))) (_shift := s))
      (_lim := hLim) (_col := hCol) := by
  have hK := single_kFlat R L hL
  have hF := single_flat_terms R L hL
  obtain ⟨hLim, hCol⟩ := flat_tensor_exact R L hL
  have := hLim
  have := hCol
  refine ⟨hK, hF, hLim, hCol, collapse_shift R L, collapse_ι R L,
    (fun _ _ _ ↦ rfl), ?_, ?_⟩
  · intro E n i j
    change (tensorRight L).map ((E⟦n⟧).d i j) = _
    rw [CochainComplex.shiftFunctor_obj_d', Functor.map_units_smul]
  · obtain ⟨s, hs⟩ := KFlatFixedTensor.kFlat_fixed_tensor_triangulated R
    let := s
    obtain ⟨_, _, htri, _, ⟨cR, hcRs, hcR⟩, _⟩ :=
      hs ((CochainComplex.singleFunctor _ 0).obj L) hK hF
    have := hcRs
    let chi := cR.symm
    have hchi : NatTrans.CommShift chi.hom ℤ := by dsimp [chi]; infer_instance
    refine ⟨inferInstance, htri.2, chi, hchi, ?_, ?_⟩
    · intro E hE hf
      exact congrArg Iso.symm (hcR E hE hf)
    · have := collapse_shift R L
      let e : DerivedCategory.Q ⋙ derived R L ≅
          DerivedCategory.Q ⋙ (tensorRight L).mapDerivedCategory :=
        chi ≪≫ Functor.isoWhiskerRight (collapse R L) DerivedCategory.Q ≪≫
          (tensorRight L).mapDerivedCategoryFactors.symm
      have he : NatTrans.CommShift e.hom ℤ := by dsimp [e]; infer_instance
      let W := HomologicalComplex.quasiIso (KFlatFixedTensor.Modules R) (.up ℤ)
      let eta : derived R L ≅ (tensorRight L).mapDerivedCategory :=
        Localization.liftNatIso DerivedCategory.Q W _ _ _ _ e
      have heta (E : CochainComplex (KFlatFixedTensor.Modules R) ℤ) :
          eta.app (DerivedCategory.Q.obj E) = e.app E := by
        apply Iso.ext
        simp [eta, Localization.liftNatTrans_app, Localization.Lifting.iso]
      refine ⟨eta, localized_iso_commShift DerivedCategory.Q W _ _ e, ?_, ?_⟩
      · intro E
        rw [heta]
        apply Iso.ext
        simp [e]
      · intro i
        let H := DerivedCategory.homologyFunctor (KFlatFixedTensor.Modules R) i
        let h := DerivedCategory.homologyFunctorFactors (KFlatFixedTensor.Modules R) i
        let F := (tensorRight L).mapHomologicalComplex (.up ℤ)
        let b : DerivedCategory.Q ⋙ (derived R L ⋙ H) ≅
            DerivedCategory.Q ⋙ (H ⋙ tensorRight L) :=
          (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerRight
              (chi ≪≫ Functor.isoWhiskerRight (collapse R L) DerivedCategory.Q) H ≪≫
            Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F h ≪≫
            termwiseHomologyIso (tensorRight L) i ≪≫
            Functor.isoWhiskerRight h.symm (tensorRight L) ≪≫
            Functor.associator _ _ _
        let c : derived R L ⋙ H ≅ H ⋙ tensorRight L :=
          Localization.liftNatIso DerivedCategory.Q W _ _ _ _ b
        refine ⟨c, ?_⟩
        intro E
        have hc : c.app (DerivedCategory.Q.obj E) = b.app E := by
          apply Iso.ext
          simp [c, Localization.liftNatTrans_app, Localization.Lifting.iso]
        rw [hc]
        apply Iso.ext
        simp only [Functor.comp_obj, Functor.flip_obj_obj, Functor.curry_obj_obj_obj,
          curriedTensor_obj_obj, Functor.isoWhiskerRight_trans, Functor.isoWhiskerRight_twice,
          termwiseHomologyIso, Iso.trans_assoc, Iso.symm_self_id_assoc, NatIso.trans_app,
          NatIso.ofComponents.app, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
          Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
          Functor.associator_hom_app, CochainComplex.map₂HomologicalComplexFlipObjSingleIso_hom_app,
          Functor.comp_map, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
          Functor.flip_obj_map, curriedTensor_map_app, Functor.mapIso_hom, Category.id_comp,
          cancelIso, Category.comp_id, DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
          Functor.mapIso_trans, H, b, F, h]

end SheafOfModules.FlatSingleDerivedNormalization
