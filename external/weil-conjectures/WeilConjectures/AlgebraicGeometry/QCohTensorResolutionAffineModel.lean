/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.Algebra.Homology.BoundedFlatKFlat
public import WeilConjectures.AlgebraicGeometry.Modules.IsKFlatTilde
public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.AffineTildeTotalTensor
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
public import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison

@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

local instance tildeZero (A : Type u) [CommRing A] :
    (tilde.functor (.of A)).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩

noncomputable local instance affineMonoidal (A : Type u) [CommRing A] :
    MonoidalCategory (Spec (.of A)).Modules :=
  SheafOfModules.monoidalCategory (Spec (.of A)).sheaf

noncomputable local instance affinePreadditive (A : Type u) [CommRing A] :
    MonoidalPreadditive (Spec (.of A)).Modules :=
  (SheafOfModules.tensorClosed (Spec (.of A)).sheaf).1.some

local instance affineTensorZero (A : Type u) [CommRing A] :
    (curriedTensor (Spec (.of A)).Modules).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor (Spec (.of A)).sheaf

local instance affineTensorObjZero (A : Type u) [CommRing A]
    (F : (Spec (.of A)).Modules) :
    ((curriedTensor _).obj F).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (Spec (.of A)).sheaf F

/-- Mapping an extension by zero is extension by zero of the mapped complex. -/
noncomputable def tensorResolutionMapExtendIso
    {C : Type u} {D : Type v} [Category C] [Category D]
    [HasZeroObject C] [HasZeroObject D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex C c) :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e := by
  let eX (o : Option ι) :
      F.obj (HomologicalComplex.extend.X K o) ≅
        HomologicalComplex.extend.X ((F.mapHomologicalComplex c).obj K) o :=
    match o with
    | none => (F.map_isZero (isZero_zero C)).iso (isZero_zero D)
    | some _ => Iso.refl _
  refine HomologicalComplex.Hom.isoOfComponents (fun i ↦ eX (e.r i)) ?_
  intro i j hij
  change (eX (e.r i)).hom ≫
      HomologicalComplex.extend.d ((F.mapHomologicalComplex c).obj K) (e.r i) (e.r j) =
    F.map (HomologicalComplex.extend.d K (e.r i) (e.r j)) ≫ (eX (e.r j)).hom
  cases e.r i <;> cases e.r j <;>
    simp [eX, HomologicalComplex.extend.d]

-- Sheaf totalization introduces large inferred coproduct and module structures.
/-- The nonpositive cochain model of an ordinary projective resolution is K-flat. -/
theorem tensorResolution_isKFlat (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    CochainComplex.IsKFlatTensor (R := (Spec (.of A)).sheaf)
      (((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).obj
        (P.complex.extend ComplexShape.embeddingDownNat)) := by
  apply isKFlat_tilde A
  apply CochainComplex.acyclic_mapBifunctor_of_boundedAbove_flat
  · refine ⟨0, fun i hi ↦ ?_⟩
    exact P.complex.isZero_extend_X _ i (by
      intro n
      simp only [ComplexShape.embeddingDownNat_f]
      omega)
  · intro i
    by_cases hi : ∃ n, ComplexShape.embeddingDownNat.f n = i
    · obtain ⟨n, hn⟩ := hi
      let e := P.complex.extendXIso ComplexShape.embeddingDownNat hn
      have : Module.Projective A (P.complex.X n) :=
        ModuleCat.projective_of_module_projective _
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    · have hz := P.complex.isZero_extend_X ComplexShape.embeddingDownNat i (by
        simpa using hi)
      let := ModuleCat.isZero_iff_subsingleton.mp hz
      infer_instance


/-- The ordinary augmentation, with chain degree j placed in cochain degree -j. -/
noncomputable def tensorResolutionAugmentation (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    P.complex.extend ComplexShape.embeddingDownNat ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M :=
  HomologicalComplex.extendMap P.π ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat M 0 0 rfl).hom

instance tensorResolutionAugmentation_quasiIso (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    QuasiIso (tensorResolutionAugmentation A M P) := by
  unfold tensorResolutionAugmentation
  infer_instance

open scoped TensorProduct

/-- The affine tensor morphism fixed by its pure-section formula. -/
noncomputable def tensorResolutionTildeTensorHom (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) :
    tilde (R := .of A) (M ⊗ N) ⟶ tilde (R := .of A) M ⊗ tilde (R := .of A) N :=
  (affine_tilde_tensor (.of A) M N).choose_spec.2.2.choose

instance tensorResolutionTildeTensorHom_isIso (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) : IsIso (tensorResolutionTildeTensorHom A M N) :=
  (affine_tilde_tensor (.of A) M N).choose_spec.2.2.choose_spec.2.1

@[simp] theorem tensorResolutionTildeTensorHom_tmul (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) (m : M) (n : N) :
    (tensorResolutionTildeTensorHom A M N).app ⊤
        (tilde.toOpen (R := .of A) (M ⊗ N) ⊤ (m ⊗ₜ[A] n)) =
      Scheme.Modules.tmulSection (tilde.toOpen (R := .of A) M ⊤ m)
        (tilde.toOpen (R := .of A) N ⊤ n) :=
  ((affine_tilde_tensor (.of A) M N).choose_spec.2.2.choose_spec.1 _).trans
    ((affine_tilde_tensor (.of A) M N).choose_spec.1 m n)

/-- Tensor-right comparison, normalized on pure sections and natural in the first module. -/
noncomputable def tensorResolutionTildeTensorRightIso (A : Type u) [CommRing A]
    (N : ModuleCat.{u} A) :
    tensorRight N ⋙ tilde.functor (.of A) ≅
      tilde.functor (.of A) ⋙ tensorRight (tilde (R := .of A) N) :=
  NatIso.ofComponents (fun M ↦ asIso (tensorResolutionTildeTensorHom A M N)) (by
    intro M M' f
    apply ((tilde.adjunction (R := .of A)).homEquiv (M ⊗ N) _).injective
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m n
    change (tensorResolutionTildeTensorHom A M' N).app ⊤
        ((tilde.map (f ▷ N)).app ⊤ (tilde.toOpen (R := .of A) (M ⊗ N) ⊤ (m ⊗ₜ[A] n))) =
      (tilde.map f ▷ tilde (R := .of A) N).app ⊤
        ((tensorResolutionTildeTensorHom A M N).app ⊤
          (tilde.toOpen (R := .of A) (M ⊗ N) ⊤ (m ⊗ₜ[A] n)))
    have ht := congr($(tilde.toOpen_map_app (R := .of A)
      (M := M ⊗ N) (N := M' ⊗ N) (f ▷ N) ⊤) (m ⊗ₜ[A] n))
    change (tilde.map (f ▷ N)).app ⊤
        (tilde.toOpen (R := .of A) (M ⊗ N) ⊤ (m ⊗ₜ[A] n)) =
      tilde.toOpen (R := .of A) (M' ⊗ N) ⊤ (f m ⊗ₜ[A] n) at ht
    rw [ht, tensorResolutionTildeTensorHom_tmul, tensorResolutionTildeTensorHom_tmul,
      Scheme.Modules.whiskerRight_app_tmulSection]
    congr 1
    exact (congr($(tilde.toOpen_map_app (R := .of A) f ⊤) m)).symm)

-- Exact homology and total tensor carry large inferred module-category instances.
/-- The affine total-tensor homology is the associated sheaf of ordinary resolution
homology. Both the extension and the exact-tilde homology comparisons are canonical. -/
noncomputable def tensorResolutionHomologyTildeIso (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) (P : ProjectiveResolution M) (n : ℕ) :
    tilde (R := .of A)
      ((((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P.complex).homology n) ≅
      (CochainComplex.mapBifunctor
        (((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).obj
          (P.complex.extend ComplexShape.embeddingDownNat))
        ((CochainComplex.singleFunctor (Spec (.of A)).Modules 0).obj (tilde (R := .of A) N))
        (curriedTensor _)).homology (-(n : ℤ)) := by
  let X := Spec (.of A)
  let T : ModuleCat.{u} A ⥤ X.Modules := tilde.functor (.of A)
  letI : T.Additive := ⟨by intros; exact tilde.map_add _ _⟩
  letI : T.PreservesHomology := tilde_preservesHomology A
  let E := P.complex.extend ComplexShape.embeddingDownNat
  let L := ((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P.complex
  let TC := T.mapHomologicalComplex (.up ℤ)
  let c := tensorResolutionMapExtendIso (tensorRight N)
    ComplexShape.embeddingDownNat P.complex
  let d := (Functor.mapHomologicalComplexCompIso
    (tensorResolutionTildeTensorRightIso A N) (.up ℤ)).app E
  let t := (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
    (tilde (R := .of A) N) (TC.obj E)).symm
  let H := HomologicalComplex.homologyFunctor X.Modules (.up ℤ) (-(n : ℤ))
  exact T.mapIso (L.extendHomologyIso ComplexShape.embeddingDownNat rfl).symm ≪≫
    (((L.extend ComplexShape.embeddingDownNat).sc (-(n : ℤ))).mapHomologyIso T).symm ≪≫
      H.mapIso (TC.mapIso c.symm ≪≫ d ≪≫ t)


/-- Sheafify the nonpositive projective-resolution augmentation. -/
noncomputable def tensorResolutionTildeAugmentation (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    (((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).obj
      (P.complex.extend ComplexShape.embeddingDownNat)) ⟶
        (CochainComplex.singleFunctor (Spec (.of A)).Modules 0).obj
          (tilde (R := .of A) M) :=
  ((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).map
      (tensorResolutionAugmentation A M P) ≫
    ((HomologicalComplex.singleMapHomologicalComplex (tilde.functor (.of A))
      (.up ℤ) 0).app M).hom

-- Resolving the exact-tilde functor through the scheme module synonym needs this budget.
instance tensorResolutionTildeAugmentation_quasiIso (A : Type u) [CommRing A]
    (M : ModuleCat.{u} A) (P : ProjectiveResolution M) :
    QuasiIso (tensorResolutionTildeAugmentation A M P) := by
  have : (tilde.functor (.of A)).PreservesHomology := tilde_preservesHomology A
  unfold tensorResolutionTildeAugmentation
  infer_instance

-- The tensor representatives and localization comparisons unfold large instances.
/-- On a spectrum, any supplied K-flat resolution of tilde M computes the ordinary
projective-resolution tensor homology. -/
theorem exists_tensorResolutionSections (A : Type u) [CommRing A]
    (M N : ModuleCat.{u} A) (P : ProjectiveResolution M)
    (K : CochainComplex (Spec (.of A)).Modules ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor (Spec (.of A)).Modules 0).obj
      (tilde (R := .of A) M))
    (hK : CochainComplex.IsKFlatTensor (R := (Spec (.of A)).sheaf) K)
    (hq : QuasiIso q) (n : ℕ) :
    Nonempty (
      ((((tensorRight N).mapHomologicalComplex (.down ℕ)).obj P.complex).homology n) ≃ₗ[A]
        (moduleSpecΓFunctor (R := .of A)).obj
          ((CochainComplex.mapBifunctor K
            ((CochainComplex.singleFunctor (Spec (.of A)).Modules 0).obj (tilde (R := .of A) N))
            (curriedTensor _)).homology (-(n : ℤ)))) := by
  classical
  let X := Spec (.of A)
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let := HasDerivedCategory.standard C
  let : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard C
  let E := (((tilde.functor (.of A)).mapHomologicalComplex (.up ℤ)).obj
    (P.complex.extend ComplexShape.embeddingDownNat))
  let N0 := (CochainComplex.singleFunctor X.Modules 0).obj (tilde (R := .of A) N)
  let p := tensorResolutionTildeAugmentation A M P
  have hp : QuasiIso p := tensorResolutionTildeAugmentation_quasiIso A M P
  have : QuasiIso q := hq
  have : QuasiIso p := hp
  obtain ⟨comparisonE⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const PUnit.{1}).obj E) ((Functor.const PUnit.{1}).obj N0)
    (fun _ ↦ tensorResolution_isKFlat A M P)
  obtain ⟨comparisonK⟩ := kFlat_derivedTensor_comparison_natIso X
    ((Functor.const PUnit.{1}).obj K) ((Functor.const PUnit.{1}).obj N0) (fun _ ↦ hK)
  let eE := (comparisonE.app PUnit.unit).app PUnit.unit
  let eK := (comparisonK.app PUnit.unit).app PUnit.unit
  let d := asIso (DerivedCategory.Q.map p) ≪≫ (asIso (DerivedCategory.Q.map q)).symm
  let e := eE.symm ≪≫ tensorIso d (Iso.refl _) ≪≫ eK
  let H := DerivedCategory.homologyFunctor C (-(n : ℤ))
  let factors := DerivedCategory.homologyFunctorFactors C (-(n : ℤ))
  let h := (factors.app _).symm ≪≫ H.mapIso e ≪≫ factors.app _
  let e' := tensorResolutionHomologyTildeIso A M N P n ≪≫ h
  let Γ := moduleSpecΓFunctor (R := .of A)
  exact ⟨(tilde.isoTop (R := .of A) _ ≪≫ Γ.mapIso e').toLinearEquiv⟩

end AlgebraicGeometry
