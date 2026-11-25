/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization
public import WeilConjectures.AlgebraicGeometry.SiteDerivedTensorRestriction
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import all WeilConjectures.AlgebraicGeometry.ResolvingRepresentativeWhiskering
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Specified K-flat tensor comparison under the section equivalence

Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 0FPT;
internal/section model identification, Steps 1–7 of the blueprint proof
(auxiliary; not a blueprint node).

The helper predicates spell out resolving membership, the prescribed representative
square, native localization normalization, and the three constraint diagrams.
-/

@[expose] public noncomputable section
-- Avoid repeated normalization of the large tensor types during asynchronous elaboration.
set_option Elab.async false
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u e z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)]

attribute [local irreducible] tensorComparison qTensor totalComparison

namespace KFlatSectionComparison

/-- The termwise functor of the fixed section equivalence.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def complexes (T : Scheme.{u}) :=
  (equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)

/-- Internal resolving membership: the acyclic total test and flatness of every term.
Source: Stacks 06YN, 06YS (auxiliary; not a blueprint node). -/
def internalResolving (T : Scheme.{u}) :
    ObjectProperty (CochainComplex (internalModules Λ T) ℤ) :=
  fun P ↦ (∀ A : CochainComplex (internalModules Λ T) ℤ, A.Acyclic →
    (CochainComplex.mapBifunctor A P (curriedTensor (internalModules Λ T))).Acyclic) ∧
      ∀ n : ℤ, exactFunctor _ _ (tensorRight (P.X n))

/-- The existing section resolving property, specialized without changing universes.
Source: Stacks 06YS (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def sectionResolving (T : Scheme.{u}) :
    ObjectProperty (CochainComplex (modules Λ T) ℤ) :=
  CategoryTheory.TensorFlatRepresentative
    (J := Scheme.ProEt.topology T) (R := ring Λ T)

/-- The independently constructed ringed derived tensor, not the conjugate bifunctor.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
@[implicit_reducible]
def nativeTensor (T : Scheme.{u}) :=
  SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 1}
    (Scheme.ProEt.topology T) (ring Λ T)

/-- The native localization map is inverse to its given representative comparison.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def NativeLocalizationCondition (T : Scheme.{u})
    (q : ((DerivedCategory.Q (C := modules Λ T)).prod
        (DerivedCategory.Q (C := modules Λ T))) ⋙
        nativeTensor Λ T ⟶ totalTensor Λ T ⋙ DerivedCategory.Q) : Prop :=
  ∀ X : (sectionResolving Λ T).FullSubcategory ×
      (sectionResolving Λ T).FullSubcategory,
    (CategoryTheory.tensorDescentPair (J := Scheme.ProEt.topology T) (R := ring Λ T)
      X.1.obj X.2.obj X.1.property X.2.property).hom ≫ q.app (X.1.obj, X.2.obj) = 𝟙 _

/-- The displayed representative equation, written with the inverse resolution maps.
The internal lax map goes from the derived tensor to the localized total; the
section qTensor has the same orientation. Thus this is the node's equation after
multiplication by the two invertible resolution comparisons.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def RepresentativeCondition (T : Scheme.{u})
    (θ : Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
        (derivedEquivalence Λ T).functor ≅
      ((derivedEquivalence Λ T).functor.prod (derivedEquivalence Λ T).functor) ⋙
        tensor Λ T) : Prop :=
  ∀ P Q : (internalResolving Λ T).FullSubcategory,
    θ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (tensor Λ T).map (Prod.mkHom
          (sectionLocalizationComparison Λ T P.obj).hom
          (sectionLocalizationComparison Λ T Q.obj).hom) ≫
        (qTensor Λ T).app ((complexes Λ T).obj P.obj, (complexes Λ T).obj Q.obj) =
      (derivedEquivalence Λ T).functor.map
          (Functor.LaxMonoidal.μ (DerivedCategory.Q (C := internalModules Λ T))
            P.obj Q.obj) ≫ localizedTotalComparison Λ T P.obj Q.obj

/-- The fixed comparison preserves the associator and both unitors.
Mathlib's OplaxMonoidal structure is exactly these three equations together with
naturality. Its unit is the identity into the transported unit; identifying that
unit with the section regular module by the explicitly localized e below gives
precisely the diagrams with e as unit comparison.
Source: Stacks 0FPT (auxiliary; not a blueprint node). -/
def ConstraintCondition (T : Scheme.{u}) : Prop :=
  ∃ o : @Functor.OplaxMonoidal (DerivedCategory (internalModules Λ T)) _ _
      (DerivedCategory (modules Λ T)) _
      (Monoidal.transport (derivedEquivalence Λ T)) (derivedEquivalence Λ T).functor,
    o.η = 𝟙 _ ∧ ∀ M N : DerivedCategory (internalModules Λ T),
      o.δ M N = (tensorComparison Λ T).hom.app (M, N)

/-- Equivalence localization and arbitrary-target descent on internal resolving pairs.
Source: Stacks 06YS, 06YU, 04VK
(auxiliary; not a blueprint node). -/
def ResolvingLocalizationCondition (T : Scheme.{u}) : Prop :=
  ∃ P : ObjectProperty (HomotopyCategory (internalModules Λ T) (.up ℤ)),
      (∀ K, P K ↔ internalResolving Λ T K.as) ∧
      (∃ F : ((HomotopyCategory.quasiIso (internalModules Λ T) (.up ℤ)).inverseImage
          P.ι).Localization ⥤ DerivedCategory (internalModules Λ T),
        F.IsEquivalence ∧ Nonempty
          (((HomotopyCategory.quasiIso (internalModules Λ T) (.up ℤ)).inverseImage
            P.ι).Q ⋙ F ≅ P.ι ⋙ DerivedCategory.Qh)) ∧
      (∀ (A : Type e) (_ : Category.{z} A)
        (U V : DerivedCategory (internalModules Λ T) ×
          DerivedCategory (internalModules Λ T) ⥤ A),
        Function.Bijective (fun τ : U ⟶ V ↦ Functor.whiskerLeft
          ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) τ))

/-- The conjugate and independent tensors agree with their localization maps on all complexes.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
def NativeComparisonCondition (T : Scheme.{u}) : Prop :=
  ∃ q : ((DerivedCategory.Q (C := modules Λ T)).prod
          (DerivedCategory.Q (C := modules Λ T))) ⋙
          nativeTensor Λ T ⟶ totalTensor Λ T ⋙ DerivedCategory.Q,
      NativeLocalizationCondition Λ T q ∧
      ∃ v : tensor Λ T ≅ nativeTensor Λ T,
        Functor.whiskerLeft ((DerivedCategory.Q (C := modules Λ T)).prod
          (DerivedCategory.Q (C := modules Λ T))) v.hom ≫ q = qTensor Λ T

/-- The regular-unit identification is the localized specified ordinary comparison;
the fixed comparison satisfies the derived constraints.
Source: Stacks 06YU, 0FPT (auxiliary; not a blueprint node). -/
def UnitCondition (T : Scheme.{u}) : Prop :=
  ∃ e₀ : tensorUnit Λ T ≅
        (DerivedCategory.singleFunctor (modules Λ T) 0).obj (𝟙_ (modules Λ T)),
      e₀ = sectionLocalizationComparison Λ T
          ((HomologicalComplex.single (internalModules Λ T) (.up ℤ) 0).obj
            (𝟙_ (internalModules Λ T))) ≪≫
        DerivedCategory.Q.mapIso
          ((HomologicalComplex.singleMapHomologicalComplex
            (equivalence Λ T).functor (.up ℤ) 0).app (𝟙_ (internalModules Λ T))) ≪≫
        (DerivedCategory.singleFunctor (modules Λ T) 0).mapIso (ordinaryUnitComparison Λ T) ∧
      ConstraintCondition Λ T

attribute [local irreducible] CategoryTheory.tensorDescentPair localizedTotalComparison

omit [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ X)] in
private theorem resolving_iff (T : Scheme.{u})
    (P : CochainComplex (internalModules Λ T) ℤ) :
    internalResolving Λ T P ↔ sectionResolving Λ T ((complexes Λ T).obj P) := by
  have h := (InternalAbelianSheafModule.internal_section_tensor_comparison
    (Scheme.ProEt.topology T) (condensedRingObj Λ T)).2.choose_spec.choose_spec
  constructor
  · intro hP
    exact ⟨(h.2.2.2.2.2.2.2.2.2.2 P).mp hP.1,
      fun n ↦ (h.2.2.2.2.2.2.2.2.2.1 (P.X n)).mp (hP.2 n)⟩
  · intro hP
    exact ⟨(h.2.2.2.2.2.2.2.2.2.2 P).mpr hP.1,
      fun n ↦ (h.2.2.2.2.2.2.2.2.2.1 (P.X n)).mpr (hP.2 n)⟩

private theorem internal_test_of_kflat (T : Scheme.{u})
    (P : CochainComplex (internalModules Λ T) ℤ)
    (hP : (HomologicalComplex.quasiIso (internalModules Λ T) (.up ℤ)).kFlat P) :
    ∀ A : CochainComplex (internalModules Λ T) ℤ, A.Acyclic →
      (CochainComplex.mapBifunctor A P (curriedTensor (internalModules Λ T))).Acyclic := by
  intro A hA
  have h := ((HomotopyCategory.kFlat_iff_preserves_acyclic _).mp
    ((HomotopyCategory.kFlat_quotient_obj_iff P).mpr hP)
    ((HomotopyCategory.quotient _ _).obj A)
    ((HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic A).mpr hA)).2
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).mp h

private theorem resolving_resolution (T : Scheme.{u})
    (P : CochainComplex (internalModules Λ T) ℤ) :
    ∃ (R : CochainComplex (internalModules Λ T) ℤ) (r : R ⟶ P),
      QuasiIso r ∧ internalResolving Λ T R := by
  obtain ⟨R, r, hr, hf, hk⟩ := CochainComplex.exists_quasiIso_flat_kFlat P
  exact ⟨R, r, hr, internal_test_of_kflat Λ T R hk, fun n ↦ (hf n).2⟩

private theorem representative_fixed (T : Scheme.{u}) :
    RepresentativeCondition Λ T (tensorComparison Λ T) := by
  have h : TensorRepresentativeCondition Λ T (qTensor Λ T) := by
    unfold qTensor
    exact (tensor_representatives Λ T).exists.choose_spec
  intro P Q
  dsimp only [complexes]
  rw [h.1 P.obj Q.obj, internalLocalizationTensorMap_app]
  simp only [← Functor.map_comp, ← Category.assoc]
  simp only [Category.assoc]
  simp

section

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
private theorem transported_oplax {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] (E : C ≌ D)
    (θ : Functor.uncurry.obj (curriedTensor C) ⋙ E.functor ≅
      E.functor.prod E.functor ⋙
        (E.inverse.prod E.inverse ⋙ Functor.uncurry.obj (curriedTensor C) ⋙ E.functor))
    (hθ : ∀ M N, θ.hom.app (M, N) =
      E.functor.map (E.unitIso.hom.app M ⊗ₘ E.unitIso.hom.app N)) :
    ∃ o : @Functor.OplaxMonoidal C _ _ D _ (Monoidal.transport E) E.functor,
      o.η = 𝟙 _ ∧ ∀ M N, o.δ M N = θ.hom.app (M, N) := by
  let := Monoidal.transport E
  let : E.inverse.Monoidal :=
    inferInstanceAs (Monoidal.equivalenceTransported E).inverse.Monoidal
  let o : E.functor.OplaxMonoidal := E.toAdjunction.leftAdjointOplaxMonoidal
  have hη : o.η = 𝟙 _ := by
    change E.functor.map (E.unitIso.hom.app _) ≫ E.counitIso.hom.app _ = 𝟙 _
    exact E.functor_unit_comp _
  have hδ (M N : C) : o.δ M N = θ.hom.app (M, N) := by
    change E.functor.map ((E.unitIso.hom.app M ⊗ₘ E.unitIso.hom.app N) ≫
      E.unitIso.hom.app _) ≫ E.counitIso.hom.app _ = _
    rw [Functor.map_comp, Category.assoc, E.functor_unit_comp, Category.comp_id]
    exact (hθ M N).symm
  exact ⟨o, hη, hδ⟩

end

private theorem representative_unique (T : Scheme.{u})
    (θ : Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
        (derivedEquivalence Λ T).functor ≅
      ((derivedEquivalence Λ T).functor.prod (derivedEquivalence Λ T).functor) ⋙
        tensor Λ T)
    (hθ : RepresentativeCondition Λ T θ) : θ = tensorComparison Λ T := by
  have hq : TensorRepresentativeCondition Λ T (qTensor Λ T) := by
    unfold qTensor
    exact (tensor_representatives Λ T).exists.choose_spec
  have hc (P Q : (internalResolving Λ T).FullSubcategory) :
      θ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) =
        (tensorComparison Λ T).hom.app
          (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) := by
    have hP := (resolving_iff Λ T P.obj).mp P.property
    have : IsIso ((qTensor Λ T).app ((complexes Λ T).obj P.obj,
      (complexes Λ T).obj Q.obj)) := hq.2.1 _ _ (Or.inl hP.1)
    have : IsIso (Prod.mkHom (sectionLocalizationComparison Λ T P.obj).hom
        (sectionLocalizationComparison Λ T Q.obj).hom) :=
      (isIso_prod_iff (f := Prod.mkHom (sectionLocalizationComparison Λ T P.obj).hom
        (sectionLocalizationComparison Λ T Q.obj).hom)).mpr ⟨inferInstance, inferInstance⟩
    apply (cancel_mono ((tensor Λ T).map (Prod.mkHom
      (sectionLocalizationComparison Λ T P.obj).hom
      (sectionLocalizationComparison Λ T Q.obj).hom) ≫
      (qTensor Λ T).app ((complexes Λ T).obj P.obj, (complexes Λ T).obj Q.obj))).mp
    simpa only [Category.assoc] using
      (hθ P Q).trans (representative_fixed Λ T P Q).symm
  apply Iso.ext
  apply NatTrans.ext
  funext ⟨M, N⟩
  obtain ⟨P, p, hp, hP⟩ := resolving_resolution Λ T (DerivedCategory.Q.objPreimage M)
  obtain ⟨Q, q, hq', hQ⟩ := resolving_resolution Λ T (DerivedCategory.Q.objPreimage N)
  have := hp
  have := hq'
  let i := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso M
  let j := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso N
  let F := Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
    (derivedEquivalence Λ T).functor
  apply (cancel_epi (F.map (Iso.prod i j).hom)).mp
  rw [θ.hom.naturality, (tensorComparison Λ T).hom.naturality]
  rw [hc ⟨P, hP⟩ ⟨Q, hQ⟩]

private theorem lift_native_comparison
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (i : B ⥤ A) (L : A ⥤ D) (U V : D ⥤ E) (S : A ⥤ E)
    (q : L ⋙ U ⟶ S) (r : i ⋙ S ≅ (i ⋙ L) ⋙ V)
    (hq : ∀ X, IsIso (q.app (i.obj X)))
    (hf : ((Functor.whiskeringLeft _ _ E).obj (i ⋙ L)).FullyFaithful) :
    ∃ q' : L ⋙ V ⟶ S,
      (∀ X, r.hom.app X ≫ q'.app (i.obj X) = 𝟙 _) ∧
      ∃ v : U ≅ V, Functor.whiskerLeft L v.hom ≫ q' = q := by
  let a := Functor.whiskerLeft i q
  have ha (X : B) : IsIso (a.app X) := hq X
  have : IsIso a := NatIso.isIso_of_isIso_app a
  let F := (Functor.whiskeringLeft _ _ E).obj (i ⋙ L)
  let v : U ≅ V := hf.preimageIso (asIso a ≪≫ r)
  have hv (X : B) : v.hom.app (L.obj (i.obj X)) = a.app X ≫ r.hom.app X := by
    have hvmap : F.map v.hom = (asIso a ≪≫ r).hom := hf.map_preimage _
    exact congrArg (fun t ↦ t.app X) hvmap
  let q' := Functor.whiskerLeft L v.inv ≫ q
  refine ⟨q', ?_, v, ?_⟩
  · intro X
    have h := congrArg (fun f ↦ inv (a.app X) ≫ f ≫
      v.inv.app (L.obj (i.obj X)) ≫ a.app X) (hv X)
    change r.hom.app X ≫ (v.inv.app (L.obj (i.obj X)) ≫ a.app X) = 𝟙 _
    simpa only [Category.assoc, IsIso.inv_hom_id_assoc, IsIso.inv_hom_id,
      Iso.hom_inv_id_app_assoc] using h.symm
  · apply NatTrans.ext
    funext X
    change v.hom.app _ ≫ (v.inv.app _ ≫ q.app X) = _
    rw [Iso.hom_inv_id_app_assoc]

private theorem native_model_data (T : Scheme.{u}) :
    let P := sectionResolving Λ T
    let L := (DerivedCategory.Q (C := modules Λ T)).prod
      (DerivedCategory.Q (C := modules Λ T))
    let S := totalTensor Λ T ⋙ DerivedCategory.Q
    ∃ r : (P.ι.prod P.ι) ⋙ S ≅ ((P.ι.prod P.ι) ⋙ L) ⋙ nativeTensor Λ T,
      (∀ X : P.FullSubcategory × P.FullSubcategory,
        r.hom.app X = (CategoryTheory.tensorDescentPair
          (J := Scheme.ProEt.topology T) (R := ring Λ T)
          X.1.obj X.2.obj X.1.property X.2.property).hom) ∧
      Nonempty (((Functor.whiskeringLeft _ _ (DerivedCategory (modules Λ T))).obj
        ((P.ι.prod P.ι) ⋙ L)).FullyFaithful) := by
  classical
  let J := Scheme.ProEt.topology T
  let R := ring Λ T
  obtain ⟨r, hr, _, hf⟩ := SheafOfModules.cochain_tensor_model_rigidity.{u + 1, u,
    u + 1, u + 1, u + 2, u + 1} J R
  refine ⟨r, ?_, ?_⟩
  · intro X
    rw [hr]
    simp only [CategoryTheory.tensorDescentPair, Iso.trans_hom]
    rfl
  · exact (Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
      (hf (DerivedCategory (modules Λ T)) inferInstance)

/-- The specified internal/section comparison, including native model identification.
Source: Stacks Project, sites-cohomology.tex, Tags 06YU and 0FPT
(auxiliary; not a blueprint node).

Proof.
1. Exactness and reflection of isomorphisms give the quasi-isomorphism equivalence.
   The ordinary internal/section comparison identifies the acyclic K-flat tests
   and the degreewise flatness tests.
2. Abstract flat-term K-flat resolutions give resolving internal representatives.
   Restrict the homotopy localization by the resolving calculus of fractions;
   its comparison from the model localization is an equivalence. Two-variable
   localization gives the arbitrary-target transformation bijection.
3. The defining normalization of qTensor gives its representative condition.
   Cancel the equivalence-unit comparison and the two localization factors to
   obtain the required square for the fixed tensorComparison.
4. Restrict qTensor to flat-term K-flat pairs, where it is invertible. Compose
   with the canonical cochain model comparison and lift this composite through
   the fully faithful resolving-pair restriction to obtain v. Define the native
   localization map as v inverse followed by qTensor on all complexes. On the
   resolving pairs the cochain model comparison is exactly tensorDescentPair;
   the lifted equation and cancellation give the required native normalization.
5. On resolving pairs the square determines theta by cancellation. Resolve
   arbitrary derived objects, and use naturality along those isomorphisms to
   prove uniqueness on all derived pairs.
6. The unit is flat; its single complex is K-flat and has flat terms. Compose
   kappa with the specified ordinary single-complex unit comparison to get e.
7. Give the inverse equivalence its induced monoidal structure. Its left adjoint
   is oplax monoidal; the triangle identities identify its unit with the identity
   and its tensor maps with the fixed equivalence-unit formula for tensorComparison.
   These are precisely the required associator and two unitor constraints.
-/
theorem section_kflat_tensor_comparison (T : Scheme.{u}) :
    (∀ (P Q : CochainComplex (internalModules Λ T) ℤ) (f : P ⟶ Q),
      QuasiIso f ↔ QuasiIso ((complexes Λ T).map f)) ∧
    (∀ P : CochainComplex (internalModules Λ T) ℤ,
      internalResolving Λ T P ↔ sectionResolving Λ T ((complexes Λ T).obj P)) ∧
    ResolvingLocalizationCondition.{u, e, z} Λ T ∧
    TensorRepresentativeCondition Λ T (qTensor Λ T) ∧
    NativeComparisonCondition Λ T ∧
    (∃! θ : Functor.uncurry.obj (CondensedRing.derivedTensor Λ T) ⋙
          (derivedEquivalence Λ T).functor ≅
        ((derivedEquivalence Λ T).functor.prod (derivedEquivalence Λ T).functor) ⋙
          tensor Λ T,
      RepresentativeCondition Λ T θ) ∧
    RepresentativeCondition Λ T (tensorComparison Λ T) ∧
    internalResolving Λ T
      ((HomologicalComplex.single (internalModules Λ T) (.up ℤ) 0).obj
        (𝟙_ (internalModules Λ T))) ∧
    UnitCondition Λ T := by
  refine ⟨?_, resolving_iff Λ T, ?_, ?_, ?_, ?_,
    representative_fixed Λ T, ?_, ?_⟩
  · intro P Q f
    exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology f
      (equivalence Λ T).functor).symm
  · let P : ObjectProperty (HomotopyCategory (internalModules Λ T) (.up ℤ)) :=
      fun K ↦ internalResolving Λ T K.as
    have hres : ∀ K : HomotopyCategory (internalModules Λ T) (.up ℤ),
        ∃ (R : P.FullSubcategory) (r : R.obj ⟶ K),
          HomotopyCategory.quasiIso (internalModules Λ T) (.up ℤ) r := by
      intro K
      obtain ⟨R, r, hr, hR⟩ := resolving_resolution Λ T K.as
      exact ⟨⟨(HomotopyCategory.quotient _ _).obj R, hR⟩,
        (HomotopyCategory.quotient _ _).map r,
        (HomotopyCategory.quotient_map_mem_quasiIso_iff r).mpr hr⟩
    let W := (HomotopyCategory.quasiIso (internalModules Λ T) (.up ℤ)).inverseImage P.ι
    have : (P.ι ⋙ DerivedCategory.Qh).IsLocalization W :=
      CategoryTheory.restriction_localization _ DerivedCategory.Qh P hres
    refine ⟨P, fun _ ↦ Iff.rfl, ?_, ?_⟩
    · exact ⟨Localization.Construction.lift (P.ι ⋙ DerivedCategory.Qh)
          (Localization.inverts (P.ι ⋙ DerivedCategory.Qh) W),
        inferInstance,
        ⟨eqToIso (Localization.Construction.fac _ _)⟩⟩
    · intro A hA U V
      exact (Localization.fullyFaithfulWhiskeringLeft
        ((P.ι ⋙ DerivedCategory.Qh).prod (P.ι ⋙ DerivedCategory.Qh)) (W.prod W) A).map_bijective U V
  · unfold qTensor
    exact (tensor_representatives Λ T).exists.choose_spec
  · classical
    let P := sectionResolving Λ T
    let L := (DerivedCategory.Q (C := modules Λ T)).prod
      (DerivedCategory.Q (C := modules Λ T))
    let S := totalTensor Λ T ⋙ DerivedCategory.Q
    obtain ⟨r, hr, ⟨hf⟩⟩ := native_model_data Λ T
    have hc : TensorRepresentativeCondition Λ T (qTensor Λ T) := by
      unfold qTensor
      exact (tensor_representatives Λ T).exists.choose_spec
    obtain ⟨q, hq, v, hv⟩ := lift_native_comparison (P.ι.prod P.ι) L
      (tensor Λ T) (nativeTensor Λ T) S (qTensor Λ T) r
      (fun X ↦ hc.2.1 X.1.obj X.2.obj (Or.inl X.1.property.1)) hf
    refine ⟨q, ?_, v, hv⟩
    intro X
    change (CategoryTheory.tensorDescentPair
      (J := Scheme.ProEt.topology T) (R := ring Λ T)
      X.1.obj X.2.obj X.1.property X.2.property).hom ≫ q.app (X.1.obj, X.2.obj) =
        𝟙 ((P.ι.prod P.ι ⋙ S).obj X)
    rw [← hr]
    exact hq X
  · exact ⟨tensorComparison Λ T, representative_fixed Λ T,
      fun θ hθ ↦ representative_unique Λ T θ hθ⟩
  · have hu : ObjectProperty.flat (𝟙_ (internalModules Λ T)) := ObjectProperty.prop_unit _
    refine ⟨internal_test_of_kflat Λ T _
      ((CochainComplex.kFlat_single_obj_iff_flat _ 0).mpr hu), ?_⟩
    intro n
    by_cases hn : n = 0
    · subst n
      simpa only [HomologicalComplex.single_obj_X_self] using hu.2
    · exact (ObjectProperty.flat_of_isZero
        (HomologicalComplex.isZero_single_obj_X _ _ _ _ hn)).2
  · refine ⟨_, rfl, ?_⟩
    apply transported_oplax (derivedEquivalence Λ T) (tensorComparison Λ T)
    intro M N
    unfold tensorComparison
    exact (tensorComparison_existsUnique Λ T).exists.choose_spec M N

end KFlatSectionComparison
end AlgebraicGeometry.ProEtale.ModuleRingedComparison
