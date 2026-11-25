/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # K-flat tensor with a module in degree zero on a ringed site

Source: Stacks Project, sites-cohomology.tex, Tag 06YU, definition-derived-tor and
its preceding construction, specialized to a degree-zero second factor.
(auxiliary; not a blueprint node)

The tensor and its representative comparison are the published site-descent construction.
The termwise tensor is the existing tensor functor applied to a cochain complex.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped ZeroObject
open SheafOfModules.KFlatFixedTensor

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{r})
  [HasDerivedCategory.{w} (Modules R)]

attribute [local irreducible] siteDerivedTensorIndependentCoefficients representativeIso

attribute [local instance] hasSheafify_coefficientUniverse
  wEqualsLocallyBijective_coefficientUniverse isMonoidal_W_independentCoefficients
  monoidalCategory symmetricCategory cochainModulesPreadditive

private local instance (I : Type r) : HasColimitsOfShape (Discrete I)
    (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem functorial_resolution :
    ∃ (F : CochainComplex (Modules R) ℤ ⥤ CochainComplex (Modules R) ℤ)
      (π : F ⟶ 𝟭 _),
      (∀ P, QuasiIso (π.app P)) ∧
      (∀ P, CochainComplex.IsKFlatIndependentCoefficients (F.obj P)) ∧
      (∀ P n, IsFlatOnSite (J := J) (R := R) ((F.obj P).X n)) := by
  let := (nonempty_monoidalClosed_independentCoefficients (R := R)).some
  let := hasFunctorialFlatResolution_kfi R
  have (I : Type r) : HasColimitsOfShape (Discrete I) (Modules R) :=
    SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf
      _ _
  have : HasFiniteBiproducts (ObjectProperty.flat (A := Modules R)).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteCoproducts (ObjectProperty.flat (A := Modules R)).FullSubcategory :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  have : HasExactColimitsOfShape ℤ (Modules R) := by
    have := AB5OfSize_of_univLE.{0, 0, r, r} AddCommGrpCat.{r}
    have : HasExactColimitsOfShape ℤ (Sheaf J AddCommGrpCat.{r}) :=
      CategoryTheory.Sheaf.hasExactColimitsOfShape J
    exact HasExactColimitsOfShape.domain_of_functor ℤ (toSheaf.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  let Λ := (Classical.arbitrary (Abelian.LeftResolution
    (ObjectProperty.flat.ι : _ ⥤ Modules R))).reduced
  have hι : (ObjectProperty.flat.ι : _ ⥤ Modules R).essImage ≤ ObjectProperty.flat := by
    rintro X ⟨Y, ⟨e⟩⟩
    exact ObjectProperty.prop_of_iso _ e Y.property
  refine ⟨Λ.resolutionFunctor, Λ.resolutionNatTrans, fun P ↦ inferInstance, ?_, ?_⟩
  · intro P Z hZ
    have hk := Λ.kFlat_resolutionFunctor_obj hι P
    let T := tensorRight (Λ.resolutionFunctor.obj P)
    have hz : QuasiIso (0 : (0 : CochainComplex (Modules R) ℤ) ⟶ Z) := by
      rw [quasiIso_iff]
      intro i
      exact (quasiIsoAt_iff_exactAt _ i
        ((HomologicalComplex.acyclic_of_isZero _ (isZero_zero _)) i)).2 (hZ i)
    have ht : QuasiIso (T.map (0 : (0 : CochainComplex (Modules R) ℤ) ⟶ Z)) :=
      hk.2 _ hz
    have htzero : (T.obj (0 : CochainComplex (Modules R) ℤ)).Acyclic :=
      HomologicalComplex.acyclic_of_isZero _ (T.map_isZero (isZero_zero _))
    exact fun i ↦ (exactAt_iff_of_quasiIsoAt
      (T.map (0 : (0 : CochainComplex (Modules R) ℤ) ⟶ Z)) i).1 (htzero i)
  · intro P n
    have := CochainComplex.closedUnderColimitsOfShape_flat (Modules R) ℤ
    let c := Λ.colimitOfShapeResolutionFunctorObj P
    have hf := ObjectProperty.prop_of_isColimit ObjectProperty.flat
      (isColimitOfPreserves (HomologicalComplex.eval (Modules R) (.up ℤ) n) c.isColimit)
      (fun i ↦ hι _ ((c.prop_diag_obj i).1 n))
    exact (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso R _).symm hf.2

-- The fixed-tensor comparisons contain the published site localization data.
private theorem representative_naturality
    (A A' B B' : CochainComplex (Modules R) ℤ)
    (hA : A.IsKFlatIndependentCoefficients) (hA' : A'.IsKFlatIndependentCoefficients)
    (hB : B.IsKFlatIndependentCoefficients) (hB' : B'.IsKFlatIndependentCoefficients)
    (hAf : ∀ n, IsFlatOnSite (J := J) (R := R) (A.X n))
    (hAf' : ∀ n, IsFlatOnSite (J := J) (R := R) (A'.X n))
    (hBf : ∀ n, IsFlatOnSite (J := J) (R := R) (B.X n))
    (hBf' : ∀ n, IsFlatOnSite (J := J) (R := R) (B'.X n))
    (f : A ⟶ A') (g : B ⟶ B') :
    DerivedCategory.Q.map (((totalTensor R).map f).app B ≫ ((totalTensor R).obj A').map g) ≫
        (representativeIso R A' B' hA' hB' hAf' hBf').hom =
      (representativeIso R A B hA hB hAf hBf).hom ≫
        ((derivedTensor R).map (DerivedCategory.Q.map f)).app _ ≫
        ((derivedTensor R).obj (DerivedCategory.Q.obj A')).map (DerivedCategory.Q.map g) := by
  obtain ⟨s, hs⟩ := kFlat_fixed_tensor_triangulated R
  obtain ⟨cR, _, hcR⟩ := (hs B hB hBf).2.2.2.2.1
  obtain ⟨cL, _, hcL⟩ := (hs A' hA' hAf').2.2.2.1
  have hnR := cR.hom.naturality f
  change DerivedCategory.Q.map (((totalTensor R).map f).app B) ≫ (cR.app A').hom =
    (cR.app A).hom ≫ ((derivedTensor R).map (DerivedCategory.Q.map f)).app _ at hnR
  rw [hcR A' hA' hAf', hcR A hA hAf] at hnR
  have hnL := cL.hom.naturality g
  change DerivedCategory.Q.map (((totalTensor R).obj A').map g) ≫ (cL.app B').hom =
    (cL.app B).hom ≫
      ((derivedTensor R).obj (DerivedCategory.Q.obj A')).map (DerivedCategory.Q.map g) at hnL
  rw [hcL B' hB' hBf', hcL B hB hBf] at hnL
  rw [Functor.map_comp, Category.assoc, hnL, ← Category.assoc, hnR, Category.assoc]

private abbrev tensorSource :=
  ((DerivedCategory.Q : CochainComplex (Modules R) ℤ ⥤ DerivedCategory (Modules R)).prod
    DerivedCategory.Q) ⋙ Functor.uncurry.obj (derivedTensor R)

private abbrev tensorTarget := Functor.uncurry.obj (totalTensor R) ⋙ DerivedCategory.Q

private theorem tensorSource_map
    {P P' Y Y' : CochainComplex (Modules R) ℤ} (f : P ⟶ P') (g : Y ⟶ Y') :
    (tensorSource R).map (Prod.mkHom f g) =
      ((derivedTensor R).map (DerivedCategory.Q.map f)).app _ ≫
        ((derivedTensor R).obj (DerivedCategory.Q.obj P')).map (DerivedCategory.Q.map g) := rfl

private theorem tensorTarget_map
    {P P' Y Y' : CochainComplex (Modules R) ℤ} (f : P ⟶ P') (g : Y ⟶ Y') :
    (tensorTarget R).map (Prod.mkHom f g) =
      DerivedCategory.Q.map (((totalTensor R).map f).app Y ≫
        ((totalTensor R).obj P').map g) := rfl

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem left_tensor_quasiIso
    (P : CochainComplex (Modules R) ℤ) (hP : P.IsKFlatIndependentCoefficients)
    {X Y : CochainComplex (Modules R) ℤ} (f : X ⟶ Y) (hf : QuasiIso f) :
    QuasiIso (((totalTensor R).obj P).map f) := by
  change QuasiIso (P ◁ f)
  have hr : QuasiIso (f ▷ P) :=
    CategoryTheory.kFlatTensorPreservesQuasiIsoIndependentCoefficients R P hP f hf
  have hi : QuasiIso ((β_ P X).hom ≫ (f ▷ P)) := inferInstance
  rw [← BraidedCategory.braiding_naturality_right] at hi
  exact quasiIso_of_comp_right _ (β_ P Y).hom

private theorem total_comparison :
    ∃ m : tensorSource R ⟶ tensorTarget R,
      (∀ (P Y : CochainComplex (Modules R) ℤ), P.IsKFlatIndependentCoefficients →
        IsIso (m.app (P, Y))) ∧
      (∀ (A B : CochainComplex (Modules R) ℤ)
        (hA : A.IsKFlatIndependentCoefficients) (hB : B.IsKFlatIndependentCoefficients)
        (hAf : ∀ n, IsFlatOnSite (J := J) (R := R) (A.X n))
        (hBf : ∀ n, IsFlatOnSite (J := J) (R := R) (B.X n)),
        m.app (A, B) = (representativeIso R A B hA hB hAf hBf).inv) := by
  obtain ⟨F, π, hπ, hk, hf⟩ := functorial_resolution R
  let F₂ := F.prod F
  let π₂ : F₂ ⟶ 𝟭 _ :=
    { app X := (π.app X.1, π.app X.2)
      naturality X Y f := by
        apply Prod.hom_ext
        · exact π.naturality f.1
        · exact π.naturality f.2 }
  let b : F₂ ⋙ tensorTarget R ≅ F₂ ⋙ tensorSource R :=
    NatIso.ofComponents
      (fun X ↦ representativeIso R _ _ (hk X.1) (hk X.2) (hf X.1) (hf X.2))
      (fun {X Y} f ↦ representative_naturality R _ _ _ _
        (hk X.1) (hk Y.1) (hk X.2) (hk Y.2)
        (hf X.1) (hf Y.1) (hf X.2) (hf Y.2) (F.map f.1) (F.map f.2))
  let ε : F₂ ⋙ tensorSource R ⟶ tensorSource R := Functor.whiskerRight π₂ (tensorSource R)
  have hε (X) : IsIso (ε.app X) := by
    have := hπ X.1
    have := hπ X.2
    change IsIso (((derivedTensor R).map (DerivedCategory.Q.map (π.app X.1))).app _ ≫
      ((derivedTensor R).obj (DerivedCategory.Q.obj X.1)).map
        (DerivedCategory.Q.map (π.app X.2)))
    infer_instance
  have : IsIso ε := NatIso.isIso_of_isIso_app ε
  let m : tensorSource R ⟶ tensorTarget R :=
    inv ε ≫ b.inv ≫ Functor.whiskerRight π₂ (tensorTarget R)
  refine ⟨m, ?_, ?_⟩
  · intro P Y hP
    have h₁ : QuasiIso (((totalTensor R).map (π.app P)).app (F.obj Y)) :=
      CategoryTheory.kFlatTensorPreservesQuasiIsoIndependentCoefficients R _ (hk Y) _ (hπ P)
    have h₂ := left_tensor_quasiIso R P hP (π.app Y) (hπ Y)
    have ht : IsIso ((tensorTarget R).map (π₂.app (P, Y))) := by
      change IsIso (DerivedCategory.Q.map
        (((totalTensor R).map (π.app P)).app (F.obj Y) ≫
          ((totalTensor R).obj P).map (π.app Y)))
      infer_instance
    change IsIso ((inv ε).app (P, Y) ≫ b.inv.app (P, Y) ≫
      (tensorTarget R).map (π₂.app (P, Y)))
    infer_instance
  · intro A B hA hB hAf hBf
    have hn := representative_naturality R _ A _ B (hk A) hA (hk B) hB
      (hf A) hAf (hf B) hBf (π.app A) (π.app B)
    apply (cancel_epi (ε.app (A, B))).1
    change ε.app (A, B) ≫ ((inv ε).app (A, B) ≫ b.inv.app (A, B) ≫
      (tensorTarget R).map (π₂.app (A, B))) = _
    rw [← Category.assoc (ε.app (A, B)), ← NatTrans.comp_app,
      IsIso.hom_inv_id, NatTrans.id_app, Category.id_comp]
    change (b.app (A, B)).inv ≫ (tensorTarget R).map (π₂.app (A, B)) = _
    apply (cancel_mono (representativeIso R A B hA hB hAf hBf).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    change (b.app (A, B)).inv ≫
      DerivedCategory.Q.map (((totalTensor R).map (π.app A)).app (F.obj B) ≫
        ((totalTensor R).obj A).map (π.app B)) ≫ _ = _
    rw [hn]
    change (b.app (A, B)).inv ≫ ((b.app (A, B)).hom ≫ ε.app (A, B)) = _
    exact (b.app (A, B)).inv_hom_id_assoc _

omit [HasDerivedCategory.{w} (Modules R)] in
private theorem single_naturality (P Q : CochainComplex (Modules R) ℤ) (f : P ⟶ Q)
    {N N' : Modules R} (g : N ⟶ N') :
    (((totalTensor R).map f).app _ ≫ ((totalTensor R).obj Q).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map g)) ≫
        (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) N' Q).hom =
      (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) N P).hom ≫
        ((((ordinaryTensor R).flip.obj N).mapHomologicalComplex (.up ℤ)).map f ≫
          (NatTrans.mapHomologicalComplex
            ((ordinaryTensor R).flip.map g) (.up ℤ)).app Q) := by
  apply (cancel_epi
    (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) N P).inv).1
  apply (cancel_mono
    (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) N' Q).inv).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
  apply HomologicalComplex.hom_ext
  intro n
  simp only [CochainComplex.mapBifunctorSingle₂Iso, CochainComplex.mapBifunctorSingle₁Iso,
    CochainComplex.mapBifunctorSingle₁XIso, ComplexShape.π_def, Functor.flip_obj_obj,
    curriedTensor_obj_obj, Functor.flip_map_app, curriedTensor_obj_map, Functor.flip_obj_map,
    curriedTensor_map_app, eqToHom_whiskerRight, Iso.symm_mk, Iso.trans_inv, Iso.symm_inv,
    Category.comp_id, Category.assoc, HomologicalComplex.comp_f,
    HomologicalComplex.Hom.isoOfComponents_hom_f,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom_assoc,
    ComplexShape.σ_def, mul_zero, Int.negOnePow_zero, one_smul, NatTrans.naturality_assoc,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  change _ ≫ _ ≫
    (HomologicalComplex.mapBifunctorMap f (𝟙 _) (ordinaryTensor R) (.up ℤ)).f n ≫
    (HomologicalComplex.mapBifunctorMap (𝟙 Q)
      ((HomologicalComplex.single _ (.up ℤ) 0).map g) (ordinaryTensor R) (.up ℤ)).f n = _
  rw [HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap]
  simp [HomologicalComplex.single_map_f_self, ← tensorHom_id, ← id_tensorHom]

-- The comparison squares combine totalization and localization functor maps.
/-- The canonical comparison with termwise tensor, natural in both inputs and uniquely
normalized by every pair of flat-term K-flat resolutions. In the termwise functor the
objects, differentials and map components are respectively `P.X q tensor M`,
`P.d q q' tensor id`, and `u.f q tensor f`. The single-complex total identification is
`CochainComplex.mapBifunctorSingle₂Iso`, whose sole nonzero summand is `(q,0)`.
No boundedness, termwise flatness of P, or flatness of M is assumed.

Source: Stacks Project, Tag 06YU, definition-derived-tor and preceding construction
(auxiliary; not a blueprint node).

Proof plan (the node's seven steps):
1. Work on a coefficient-universe small model of the site (prose-01-10).
   Module sheaves are Grothendieck abelian (prop-pur-kinjective-resolutions-exist),
   their tensor is closed symmetric and additive (lem-pc-sheaf-modules-tensor-closed),
   and they have functorial flat resolutions (lem-trf-site-functorial-flat-resolution).
2. The acyclic-tensor K-flat predicate implies preservation of quasi-isomorphisms
   (lem-pur-kflat-tensor-quasiiso-independent). The signed swap on bidegree (i,j)
   has sign (-1)^(ij); its two differential coefficients are (-1)^(ij) and
   (-1)^(ij+j). It gives preservation in the other variable. Conversely test 0 to X
   for acyclic X. Thus it agrees with def-sfb-preserves-kflat-quasi-iso.
3. Apply prose-03-02. Its natural localization multiplication is invertible
   whenever one argument is K-flat, including the identity resolution of P.
4. Identify that tensor with the specified site-descent tensor by extending the
   comparison on flat-term K-flat pairs, and its inverse, uniquely
   (lem-weil-pbc-site-derived-tensor-descent). The resulting multiplication m has
   normalization m = representativeIso.inv on those pairs.
5. In total tensor with M[0], all summands except (q,0) vanish. Projection and
   inclusion give delta = mapBifunctorSingle₂Iso; the second differential vanishes,
   so the first is d_P tensor id. Compose m with Q(delta) to obtain c.
6. Naturality of m and delta gives precisely the displayed square, whose right edge
   is Q of the termwise tensor map. In degree q this map is u.f q tensor f.
7. For any flat-term K-flat resolutions p and b (lem-pc-kflat-resolution), naturality
   gives beta followed by tensor(Qp,Qb) followed by c = Q(total(p,b) followed by delta).
   The first two arrows are invertible. Thus this equation uniquely determines c,
   proves independence of both resolutions, and gives uniqueness of the whole family.
-/
theorem ringed_kFlat_single_tensor_comparison :
    ∃! c : ∀ (P : CochainComplex (Modules R) ℤ)
        (_ : CochainComplex.IsKFlatIndependentCoefficients P) (M : Modules R),
      ((derivedTensor R).obj (DerivedCategory.Q.obj P)).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (.up ℤ) 0).obj M)) ≅
        DerivedCategory.Q.obj
          ((((ordinaryTensor R).flip.obj M).mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (P P' : CochainComplex (Modules R) ℤ)
          (hP : CochainComplex.IsKFlatIndependentCoefficients P)
          (hP' : CochainComplex.IsKFlatIndependentCoefficients P')
          (M M' : Modules R) (u : P ⟶ P') (f : M ⟶ M'),
        ((derivedTensor R).map (DerivedCategory.Q.map u)).app _ ≫
            ((derivedTensor R).obj (DerivedCategory.Q.obj P')).map
              (DerivedCategory.Q.map ((HomologicalComplex.single _ (.up ℤ) 0).map f)) ≫
            (c P' hP' M').hom =
          (c P hP M).hom ≫ DerivedCategory.Q.map
            (((((ordinaryTensor R).flip.obj M).mapHomologicalComplex (.up ℤ)).map u) ≫
              (NatTrans.mapHomologicalComplex ((ordinaryTensor R).flip.map f) (.up ℤ)).app P')) ∧
      (∀ (P : CochainComplex (Modules R) ℤ)
          (hP : CochainComplex.IsKFlatIndependentCoefficients P) (M : Modules R)
          (A B : CochainComplex (Modules R) ℤ)
          (hA : CochainComplex.IsKFlatIndependentCoefficients A)
          (hB : CochainComplex.IsKFlatIndependentCoefficients B)
          (hAf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (A.X n))
          (hBf : ∀ n : ℤ, IsFlatOnSite (J := J) (R := R) (B.X n))
          (p : A ⟶ P) (b : B ⟶ (HomologicalComplex.single _ (.up ℤ) 0).obj M),
        QuasiIso p → QuasiIso b →
          (representativeIso R A B hA hB hAf hBf).hom ≫
              ((derivedTensor R).map (DerivedCategory.Q.map p)).app _ ≫
              ((derivedTensor R).obj (DerivedCategory.Q.obj P)).map
                (DerivedCategory.Q.map b) ≫ (c P hP M).hom =
            DerivedCategory.Q.map
              (((totalTensor R).map p).app B ≫ ((totalTensor R).obj P).map b ≫
                (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M P).hom)) := by
  obtain ⟨m, hm, hnorm⟩ := total_comparison R
  let S := HomologicalComplex.single (Modules R) (.up ℤ) 0
  let c := fun (P : CochainComplex (Modules R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (M : Modules R) ↦
    letI := hm P (S.obj M) hP
    asIso (m.app (P, S.obj M)) ≪≫
      DerivedCategory.Q.mapIso (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M P)
  have hn : ∀ (P P' : CochainComplex (Modules R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (hP' : P'.IsKFlatIndependentCoefficients)
      (M M' : Modules R) (u : P ⟶ P') (f : M ⟶ M'),
      (tensorSource R).map (Prod.mkHom u (S.map f)) ≫ (c P' hP' M').hom =
        (c P hP M).hom ≫ DerivedCategory.Q.map
          (((((ordinaryTensor R).flip.obj M).mapHomologicalComplex (.up ℤ)).map u) ≫
            (NatTrans.mapHomologicalComplex ((ordinaryTensor R).flip.map f) (.up ℤ)).app P') := by
    intro P P' hP hP' M M' u f
    dsimp only [c, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
    rw [← Category.assoc, m.naturality, Category.assoc, tensorTarget_map,
      ← DerivedCategory.Q.map_comp,
      single_naturality, DerivedCategory.Q.map_comp, Category.assoc]
  have hc : ∀ (P : CochainComplex (Modules R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) (M : Modules R)
      (A B : CochainComplex (Modules R) ℤ)
      (hA : A.IsKFlatIndependentCoefficients) (hB : B.IsKFlatIndependentCoefficients)
      (hAf : ∀ n, IsFlatOnSite (J := J) (R := R) (A.X n))
      (hBf : ∀ n, IsFlatOnSite (J := J) (R := R) (B.X n))
      (p : A ⟶ P) (b : B ⟶ S.obj M),
      (representativeIso R A B hA hB hAf hBf).hom ≫
          (tensorSource R).map (Prod.mkHom p b) ≫ (c P hP M).hom =
        DerivedCategory.Q.map
          (((totalTensor R).map p).app B ≫ ((totalTensor R).obj P).map b ≫
            (CochainComplex.mapBifunctorSingle₂Iso (ordinaryTensor R) M P).hom) := by
    intro P hP M A B hA hB hAf hBf p b
    dsimp only [c, Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
    rw [← Category.assoc ((tensorSource R).map _), m.naturality,
      hnorm A B hA hB hAf hBf, Category.assoc, Iso.hom_inv_id_assoc,
      tensorTarget_map, ← DerivedCategory.Q.map_comp]
    rw [Category.assoc]
  refine ⟨c, ⟨?_, ?_⟩, ?_⟩
  · intro P P' hP hP' M M' u f
    simpa only [tensorSource_map, Category.assoc] using hn P P' hP hP' M M' u f
  · intro P hP M A B hA hB hAf hBf p b hp hb
    simpa only [tensorSource_map, Category.assoc] using hc P hP M A B hA hB hAf hBf p b
  · intro c' hc'
    funext P hP M
    apply Iso.ext
    obtain ⟨F, π, hπ, hk, hf⟩ := functorial_resolution R
    have := hπ P
    have := hπ (S.obj M)
    let e := representativeIso R (F.obj P) (F.obj (S.obj M))
      (hk P) (hk (S.obj M)) (hf P) (hf (S.obj M))
    have hi : IsIso ((tensorSource R).map (Prod.mkHom (π.app P) (π.app (S.obj M)))) := by
      change IsIso (((derivedTensor R).map (DerivedCategory.Q.map (π.app P))).app _ ≫
        ((derivedTensor R).obj (DerivedCategory.Q.obj P)).map
          (DerivedCategory.Q.map (π.app (S.obj M))))
      infer_instance
    apply (cancel_epi (e.hom ≫
      (tensorSource R).map (Prod.mkHom (π.app P) (π.app (S.obj M))))).1
    have h₁ := hc'.2 P hP M _ _ (hk P) (hk (S.obj M)) (hf P) (hf (S.obj M))
      (π.app P) (π.app (S.obj M)) (hπ P) (hπ (S.obj M))
    have h₂ := hc P hP M _ _ (hk P) (hk (S.obj M)) (hf P) (hf (S.obj M))
      (π.app P) (π.app (S.obj M))
    simpa only [e, tensorSource_map, Functor.id_obj, Category.assoc] using h₁.trans h₂.symm

end SheafOfModules
