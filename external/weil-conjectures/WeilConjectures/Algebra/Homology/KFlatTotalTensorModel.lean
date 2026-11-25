/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Sites.Limits
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
/-!
# Flat-term K-flat total tensor models

Source: Stacks Project, Cohomology on Sites, Tags 07A2 and 07A4;
Modules on Sites, Tag 0G6Q (auxiliary; not a blueprint node).

The helpers below only specialize existing category and tensor constructions.
The derived tensor in the conclusion is exactly the localized bifunctor supplied by
`site_derived_tensor_descent_independentCoefficients`, characterized by its natural
representative comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u v r w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.KFlatTotalTensorModel

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{r})

/-- Use the recorded small-site sheafification in the coefficient universe.
Source: Stacks, Section 03DA (auxiliary; not a blueprint node). -/
instance smallSiteHasSheafify : HasSheafify J AddCommGrpCat.{r} :=
  SheafOfModules.hasSheafify_coefficientUniverse.{u, v, r}

/-- Use the recorded locally-bijective criterion in the coefficient universe.
Source: Stacks, Section 03DA (auxiliary; not a blueprint node). -/
instance smallSiteWEqualsLocallyBijective : J.WEqualsLocallyBijective AddCommGrpCat.{r} :=
  SheafOfModules.wEqualsLocallyBijective_coefficientUniverse.{u, v, r}

end SheafOfModules.KFlatTotalTensorModel

namespace SheafOfModules.KFlatTotalTensorModel

section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
open CategoryTheory CategoryTheory.Limits MonoidalCategory
variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{r})

/-- The existing category of module sheaves on the given small site.
Source: Stacks, Tag 07A2 (blueprint: lem-pur-kflat-total-tensor-model). -/
abbrev Modules := SheafOfModules.{r}
  ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R)

/-- The canonical monoidal structure with every universe-sensitive instance fixed explicitly.
Source: Stacks, Tag 03EK (blueprint: lem-pur-kflat-total-tensor-model). -/
@[instance_reducible]
def monoidal : MonoidalCategory (Modules R) :=
  @SheafOfModules.monoidalCategory.{v, u, r} C _ J
    (inferInstance : J.HasSheafCompose
      (forget₂ CommRingCat.{r} RingCat.{r})) R
    (smallSiteWEqualsLocallyBijective (J := J))
    (inferInstance : HasWeakSheafify J AddCommGrpCat.{r})
    (SheafOfModules.isMonoidal_W_independentCoefficients.{u, v, r} R)

/-- The existing sheaf tensor, with its canonical monoidal structure explicitly supplied.
Source: Stacks, Tags 03EK and 07A2 (blueprint: lem-pur-kflat-total-tensor-model). -/
def tensor : Modules R ⥤ Modules R ⥤ Modules R :=
  @curriedTensor (Modules R) _ (monoidal R)

/-- Reuse the existing zero-map preservation for the canonical tensor alias.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
instance tensor_preservesZeroMorphisms : (tensor R).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients.{u, v, r} R

/-- Reuse zero-map preservation in the second tensor variable.
Source: Stacks, Tag 03EK (auxiliary; not a blueprint node). -/
instance tensor_obj_preservesZeroMorphisms (M : Modules R) :
    ((tensor R).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients.{u, v, r} R M

private local instance (I : Type r) : HasColimitsOfShape (Discrete I)
    (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

private local instance (I : Type r) : HasColimitsOfShape (Discrete I) (Modules R) :=
  SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

private local instance (I : Type) : HasColimitsOfShape (Discrete I) (Modules R) := by
  let : HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  exact SheafOfModules.instHasColimitsOfShapeOfPresheafOfModulesObjFunctorOppositeRingCatIsSheaf _ _

/-- Reuse the coproduct totalization of the canonical tensor bicomplex.
Source: Stacks, Tag 06YM (auxiliary; not a blueprint node). -/
instance hasTotal (K L : CochainComplex (Modules R) ℤ) :
    CochainComplex.HasMapBifunctor K L (tensor R) := inferInstance

/-- The direct-sum total tensor bifunctor, with the usual cochain Koszul differential.
This is `CochainComplex.mapBifunctor` on objects, not a new totalization.
Source: Stacks, Tags 06YM and 07A2 (blueprint: lem-pur-kflat-total-tensor-model). -/
def total : CochainComplex (Modules R) ℤ × CochainComplex (Modules R) ℤ ⥤
    CochainComplex (Modules R) ℤ :=
  Functor.uncurry.obj ((tensor R).map₂CochainComplex)

private theorem total_map_f
    {P P' Q Q' : CochainComplex (Modules R) ℤ} (f : P ⟶ P') (g : Q ⟶ Q') (i : ℤ) :
    let := monoidal R
    ((total R).map (Prod.mkHom f g)).f i =
      GradedObject.Monoidal.tensorHom f.f g.f i := by
  let := monoidal R
  apply GradedObject.Monoidal.tensorObj_ext
  intro p q hpq
  rw [GradedObject.Monoidal.ι_tensorHom]
  change CochainComplex.ιMapBifunctor P Q (tensor R) p q i hpq ≫ _ = _
  simp only [total, Functor.uncurry_obj_map,
    Functor.map₂CochainComplex, Functor.map₂HomologicalComplex,
    HomologicalComplex.comp_f,
    HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f]
  simp [tensor, MonoidalCategory.tensorHom_def]
  rfl

private theorem flat_coproductOnSite {I : Type} (F : I → Modules R)
    (hF : ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (F i)) :
    SheafOfModules.IsFlatOnSite (J := J) (R := R) (∐ F) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := monoidal R
  let := SheafOfModules.symmetricCategory R
  have (M : Modules R) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : Modules R) : PreservesColimitsOfSize.{0, 0} (tensorRight M) :=
    preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  have (i : I) : PreservesFiniteLimits (tensorLeft (F i)) :=
    (SheafOfModules.flat_to_cat R (F i) (hF i)).1.1
  let : HasSheafify J AddCommGrpCat.{r} := smallSiteHasSheafify (J := J)
  let : HasWeakSheafify J AddCommGrpCat.{r} := HasSheafify.isRightAdjoint
  have : HasColimitsOfShape (Discrete I) AddCommGrpCat.{r} := inferInstance
  have : HasColimitsOfShape (Discrete I) (Sheaf J AddCommGrpCat.{r}) :=
    ⟨fun D ↦ HasColimit.mk ⟨
      Sheaf.sheafifyCocone (colimit.cocone (D ⋙ sheafToPresheaf J AddCommGrpCat.{r})),
      Sheaf.isColimitSheafifyCocone _ (colimit.isColimit _)⟩⟩
  have : HasExactColimitsOfShape (Discrete I) (Sheaf J AddCommGrpCat.{r}) :=
    CategoryTheory.Sheaf.hasExactColimitsOfShape J
  have : HasExactColimitsOfShape (Discrete I) (Modules R) :=
    HasExactColimitsOfShape.domain_of_functor (Discrete I) (SheafOfModules.toSheaf.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R))
  have : PreservesColimit (Discrete.functor F) (curriedTensor (Modules R)) :=
    MonoidalCategory.Limits.preservesColimit_curriedTensor _
  let e : tensorLeft (∐ F) ≅ (Discrete.functor F ⋙ curriedTensor (Modules R)).flip ⋙ colim :=
    preservesColimitIso (curriedTensor (Modules R)) (Discrete.functor F) ≪≫
      colimitIsoFlipCompColim _
  have : PreservesFiniteLimits ((Discrete.functor F ⋙ curriedTensor (Modules R)).flip) :=
    preservesFiniteLimits_of_evaluation _ (fun j ↦
      inferInstanceAs (PreservesFiniteLimits (tensorLeft (F j.as))))
  have : PreservesFiniteLimits (tensorLeft (∐ F)) := preservesFiniteLimits_of_natIso e.symm
  have hr : exactFunctor _ _ (tensorRight (∐ F)) :=
    ⟨preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight (∐ F)),
      (inferInstance : PreservesFiniteColimits (tensorRight (∐ F)))⟩
  exact (exactFunctor _ _).prop_of_iso
    (SheafOfModules.siteSheafTensorRightIso R (∐ F)).symm hr

private theorem totalFlat
    (P Q : CochainComplex (Modules R) ℤ)
    (hP : ∀ p, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p))
    (hQ : ∀ q, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X q)) :
    ∀ i, SheafOfModules.IsFlatOnSite (J := J) (R := R) (((total R).obj (P, Q)).X i) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := monoidal R
  have hf (p q : ℤ) : SheafOfModules.IsFlatOnSite (J := J) (R := R)
      ((tensor R).obj (P.X p) |>.obj (Q.X q)) := by
    have h : ObjectProperty.flat (P.X p ⊗ Q.X q) :=
      ObjectProperty.prop_tensor (SheafOfModules.flat_to_cat R _ (hP p))
        (SheafOfModules.flat_to_cat R _ (hQ q))
    exact (exactFunctor _ _).prop_of_iso
      (SheafOfModules.siteSheafTensorRightIso R _).symm h.2
  intro i
  change SheafOfModules.IsFlatOnSite (J := J) (R := R)
    (∐ fun pq : {pq : ℤ × ℤ // pq.1 + pq.2 = i} ↦
      ((tensor R).obj (P.X pq.val.1)).obj (Q.X pq.val.2))
  exact flat_coproductOnSite R _ (fun pq ↦ hf pq.val.1 pq.val.2)

private theorem derivedComparison
    [HasDerivedCategory.{w} (Modules R)]
    (P Q : CochainComplex (Modules R) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (hPflat : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p))
    (hQflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X q)) :
    Nonempty (DerivedCategory.Q.obj ((total R).obj (P, Q)) ≅
      (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let h := SheafOfModules.site_derived_tensor_descent_independentCoefficients.{u, v, r, w, 0, 0}
    J R
  let S := h.choose
  have hS := h.choose_spec.1
  let B := h.choose_spec.2.2.1.choose
  let c := h.choose_spec.2.2.1.choose_spec.1.some
  let d := h.choose_spec.2.2.1.choose_spec.2.choose_spec.some
  let p : S.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj P,
    (hS _).2 ⟨hP, hPflat⟩⟩
  let q : S.FullSubcategory := ⟨(HomotopyCategory.quotient _ _).obj Q,
    (hS _).2 ⟨hQ, hQflat⟩⟩
  exact ⟨((DerivedCategory.quotientCompQhIso (Modules R)).app ((total R).obj (P, Q))).symm ≪≫
    (DerivedCategory.Qh.mapIso (c.app (P, Q))).symm ≪≫ d.app (p, q) ≪≫
    (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).mapIso
      (((DerivedCategory.quotientCompQhIso (Modules R)).app P).prod
        ((DerivedCategory.quotientCompQhIso (Modules R)).app Q))⟩

/-- The total tensor of flat-term K-flat complexes is again a flat-term K-flat complex,
with its natural, summandwise inverse-associator chain isomorphism and its derived model.
All complexes are integer-indexed without any boundedness restriction. The termwise
flatness clause applies to the direct sum over all pairs of integers with the given sum.
The last bifunctor is the chosen descent of the total tensor from the cited resolving
subcategory; its natural comparison determines it up to compatible natural isomorphism.

Source: Stacks Project, Cohomology on Sites, Tags 07A2 and 07A4, and Modules on Sites,
Tag 0G6Q (blueprint: lem-pur-kflat-total-tensor-model).

Proof plan:
1. Given an acyclic H, K-flatness of P makes Tot(H tensor P) acyclic, and K-flatness
   of Q makes Tot(Tot(H tensor P) tensor Q) acyclic (def-pc-kflat-complex).
   The reassociation in step 4 transfers this acyclicity to Tot(H tensor Tot(P tensor Q)).
2. Each P^p tensor Q^q is flat: tensoring by it is the composite of the two exact
   tensor functors, identified by associativity (def-pc-flat-sheaf-modules and
   lem-pc-sheaf-modules-tensor-closed).
3. The pairs p+q=i are countable. Their coproduct is flat by lem-pc-kflat-closure.
   This is precisely the degree i term of the direct-sum total complex.
4. Distribute tensor through coproducts by the tensor/internal-Hom adjunction
   (lem-pc-sheaf-modules-tensor-closed), then use the inverse sheaf associator on
   each triple summand. The three differential components have signs 1, (-1)^a,
   and (-1)^(a+p) on both sides. Thus reassociation is a chain map with inverse
   given by the associator. Naturality follows on each summand from its naturality.
5. Apply the natural resolving-class comparison of lem-weil-pbc-site-derived-tensor-descent
   to P,Q. Their total is in the same resolving class by steps 1 and 3, so it is an
   admissible representative for subsequent derived tensor or derived pullback.
-/
theorem kFlat_total_tensor_model
    [HasDerivedCategory.{w} (Modules R)]
    (P Q : CochainComplex (Modules R) ℤ)
    (_hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
    (_hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q)
    (_hPflat : ∀ p : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (P.X p))
    (_hQflat : ∀ q : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R) (Q.X q)) :
    CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R)
        ((total R).obj (P, Q)) ∧
    (∀ i : ℤ, SheafOfModules.IsFlatOnSite (J := J) (R := R)
      (((total R).obj (P, Q)).X i)) ∧
    (∃ α : ∀ H : CochainComplex (Modules R) ℤ,
        (total R).obj (H, (total R).obj (P, Q)) ≅
          (total R).obj ((total R).obj (H, P), Q),
      (∀ (H : CochainComplex (Modules R) ℤ) (a p q b c i : ℤ)
          (hpq : p + q = c) (ha : a + c = i)
          (hap : a + p = b) (hb : b + q = i),
        ((tensor R).obj (H.X a)).map
            (CochainComplex.ιMapBifunctor P Q (tensor R) p q c hpq) ≫
          CochainComplex.ιMapBifunctor H ((total R).obj (P, Q)) (tensor R) a c i ha ≫
          (α H).hom.f i =
        (@MonoidalCategory.associator (Modules R) _
            (monoidal R).toMonoidalCategoryStruct
            (H.X a) (P.X p) (Q.X q)).inv ≫
          ((tensor R).map (CochainComplex.ιMapBifunctor H P (tensor R) a p b hap)).app
            (Q.X q) ≫
          CochainComplex.ιMapBifunctor ((total R).obj (H, P)) Q (tensor R) b q i hb) ∧
      ∀ (H H' : CochainComplex (Modules R) ℤ) (f : H ⟶ H'),
        (total R).map (CategoryTheory.Prod.mkHom f (𝟙 ((total R).obj (P, Q)))) ≫
            (α H').hom =
          (α H).hom ≫ (total R).map
            (CategoryTheory.Prod.mkHom ((total R).map (CategoryTheory.Prod.mkHom f (𝟙 P)))
              (𝟙 Q))) ∧
    Nonempty (DerivedCategory.Q.obj ((total R).obj (P, Q)) ≅
      (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u, v, r, w} J R).obj
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := monoidal R
  let := SheafOfModules.tensorPreadditive R
  have (M : Modules R) : PreservesColimitsOfSize.{0, 0} (tensorLeft M) := by
    have := SheafOfModules.tensorLeft_preservesColimits_independentCoefficients R M
    exact preservesColimitsOfSize_shrink (tensorLeft M)
  have (M : Modules R) : PreservesColimitsOfSize.{0, 0} (tensorRight M) := by
    let := SheafOfModules.symmetricCategory R
    exact preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  let α := fun H : CochainComplex (Modules R) ℤ ↦
    (HomologicalComplex.associator H P Q).symm
  refine ⟨?_, ?_, ⟨α, ?_, ?_⟩, derivedComparison R P Q _hP _hQ _hPflat _hQflat⟩
  · intro H hH
    exact fun i ↦ (_hQ _ (_hP H hH) i).of_iso (α H).symm
  · exact totalFlat R P Q _hPflat _hQflat
  · intro H a p q b c i hpq ha hap hb
    have h : a + p + q = i := by omega
    change (H.X a ◁ GradedObject.Monoidal.ιTensorObj P.X Q.X p q c hpq) ≫
      GradedObject.Monoidal.ιTensorObj H.X (GradedObject.Monoidal.tensorObj P.X Q.X) a c i ha ≫
        (GradedObject.Monoidal.associator H.X P.X Q.X).inv i =
      (α_ (H.X a) (P.X p) (Q.X q)).inv ≫
        (GradedObject.Monoidal.ιTensorObj H.X P.X a p b hap ▷ Q.X q) ≫
          GradedObject.Monoidal.ιTensorObj
            (GradedObject.Monoidal.tensorObj H.X P.X) Q.X b q i hb
    rw [← GradedObject.Monoidal.ιTensorObj₃_eq_assoc H.X P.X Q.X a p q i h c hpq,
      GradedObject.Monoidal.ιTensorObj₃_associator_inv,
      GradedObject.Monoidal.ιTensorObj₃'_eq H.X P.X Q.X a p q i h b hap]
  · intro H H' f
    ext i : 1
    have hff : ((total R).map (Prod.mkHom f (𝟙 P))).f =
        GradedObject.Monoidal.tensorHom f.f (𝟙 P.X) := by
      funext j
      exact total_map_f R f (𝟙 P) j
    simp only [HomologicalComplex.comp_f, total_map_f]
    rw [hff]
    change GradedObject.Monoidal.tensorHom f.f (𝟙 (GradedObject.Monoidal.tensorObj P.X Q.X)) i ≫
      (GradedObject.Monoidal.associator H'.X P.X Q.X).inv i =
        (GradedObject.Monoidal.associator H.X P.X Q.X).inv i ≫
          GradedObject.Monoidal.tensorHom (GradedObject.Monoidal.tensorHom f.f (𝟙 P.X)) (𝟙 Q.X) i
    have h := GradedObject.Monoidal.associator_naturality f.f (𝟙 P.X) (𝟙 Q.X)
    have hi := congrFun h i
    change GradedObject.Monoidal.tensorHom
        (GradedObject.Monoidal.tensorHom f.f (𝟙 P.X)) (𝟙 Q.X) i ≫
          (GradedObject.Monoidal.associator H'.X P.X Q.X).hom i =
      (GradedObject.Monoidal.associator H.X P.X Q.X).hom i ≫
        GradedObject.Monoidal.tensorHom f.f
          (GradedObject.Monoidal.tensorHom (𝟙 P.X) (𝟙 Q.X)) i at hi
    rw [GradedObject.Monoidal.id_tensorHom_id] at hi
    symm
    simpa only [Category.assoc,
      Iso.inv_hom_id_eval_assoc, Iso.hom_inv_id_eval,
      Category.comp_id, Category.id_comp, GradedObject.Monoidal.id_tensorHom_id] using
      congrArg (fun t ↦ (GradedObject.Monoidal.associator H.X P.X Q.X).inv i ≫ t ≫
        (GradedObject.Monoidal.associator H'.X P.X Q.X).inv i) hi

end

end SheafOfModules.KFlatTotalTensorModel
