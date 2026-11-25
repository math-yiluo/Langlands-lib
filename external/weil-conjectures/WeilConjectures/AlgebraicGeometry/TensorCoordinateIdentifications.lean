/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.PinnedTensorSquareLeftSummand

import WeilConjectures.Algebra.Homology.KFlatTensorProduct
import WeilConjectures.Algebra.Homology.KFlatPullback

/-! # Derived identifications for a specified tensor chain map

Source: Stacks Project, perfect.tex, Tag 0DJA(1), using Tag 0BYJ.
(blueprint: lem-pc-tensor-coordinate-identifications).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace AlgebraicGeometry

local instance tensorCoordinateIdentificationsInstance1 (Y : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  pullbackDescentModuleTensor Y

local instance tensorCoordinateIdentificationsInstance2 (Y : Scheme.{u}) :
    MonoidalPreadditive (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :=
  modulePreadditive Y

attribute [local instance] pinnedTensorSquareLeftSummandInstance3
  pinnedTensorSquareLeftSummandInstance4

private theorem counit_isIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) :
    IsIso ((SingleComplexBaseChange.counit f).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) := by
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
    (derivedPullback_spec f)
  have h : E = Scheme.Modules.tensorPullback f :=
    CategoryTheory.Functor.ext hE (fun _ _ a ↦ hEmap a)
  subst E
  have hL' : (derivedPullback f).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso _ (.up ℤ)) := hL
  have hε := (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition)).1 f
  let δ := (derivedPullback f).leftDerivedLift ε
    (HomotopyCategory.quasiIso _ (.up ℤ)) (derivedPullback f)
    (SingleComplexBaseChange.counit f)
  have : IsIso δ := (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift
    (derivedPullback f) ε (HomotopyCategory.quasiIso _ (.up ℤ))
    (derivedPullback f) (SingleComplexBaseChange.counit f)).mp hε
  have := hK P hP
  have fac := (derivedPullback f).leftDerived_fac_app ε
    (HomotopyCategory.quasiIso _ (.up ℤ)) (derivedPullback f)
    (SingleComplexBaseChange.counit f) ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [← fac]
  change IsIso (δ.app _ ≫ _)
  infer_instance

private theorem modelMap_isIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : P.IsKFlatTensor) : IsIso (pullbackTensorModelMap X P N) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let : MonoidalCategory C := SheafOfModules.monoidalCategory X.sheaf
  let : SymmetricCategory C := SheafOfModules.symmetricCategory X.sheaf
  have : MonoidalPreadditive C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  let : MonoidalClosed C := Classical.choice (SheafOfModules.tensorClosed X.sheaf).2.1
  have : IsGrothendieckAbelian.{u} C :=
    SheafOfModules.isGrothendieckAbelian (moduleRings X.toRingedSpace)
  have : HasColimitsOfSize.{0, 0} C := hasColimitsOfSizeShrink.{0, 0, u, u} C
  have := schemeModule_hasFunctorialFlatResolution X
  have := DerivedCategory.hasDerivedMonoidalCategory C
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj M) :=
    preservesColimitsOfShape_of_natIso (F := tensorLeft M)
      (NatIso.ofComponents (fun N ↦ β_ M N) (by intros; simp [curriedTensor]))
  have (M : C) : PreservesColimitsOfShape ℤ ((curriedTensor C).obj M) := inferInstance
  have : HasExactColimitsOfShape ℤ C := inferInstance
  have (j : ℤ) : HasColimitsOfShape
      (Discrete ((ComplexShape.up ℤ).π (.up ℤ) (.up ℤ) ⁻¹' {j})) C := inferInstance
  have : (HomotopyCategory.quasiIso C (.up ℤ)).localizerMorphismKFlat.IsLeftDerivabilityStructure :=
    inferInstance
  have hk : (HomotopyCategory.quasiIso C (.up ℤ)).kFlat
      ((HomotopyCategory.quotient C (.up ℤ)).obj P) := by
    rw [HomotopyCategory.kFlat_iff_preserves_acyclic]
    intro N hN
    obtain ⟨N, rfl⟩ := N.quotient_obj_surjective
    rw [HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at hN
    have hright : HomotopyCategory.subcategoryAcyclic C
        ((HomotopyCategory.quotient C (.up ℤ)).obj N ⊗
          (HomotopyCategory.quotient C (.up ℤ)).obj P) :=
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _).2 (hP N hN)
    exact ⟨(HomotopyCategory.subcategoryAcyclic C).prop_of_iso (β_ _ _) hright, hright⟩
  have hq := DerivedMonoidal.isIso_counit_app_app_of_kFlat_left
    (DerivedCategory.Qh (C := C)) (HomotopyCategory.quasiIso C (.up ℤ))
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
    ((HomotopyCategory.quotient C (.up ℤ)).obj N) hk
  have : IsIso (Functor.LaxMonoidal.μ (DerivedCategory.Qh (C := C))
      ((HomotopyCategory.quotient C (.up ℤ)).obj P)
      ((HomotopyCategory.quotient C (.up ℤ)).obj N)) := hq
  change IsIso (_ ≫ _ ≫ _)
  change IsIso (_ ≫ (_ ≫ _) ≫ _)
  infer_instance


private theorem modelMap_natural
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (X : Scheme.{u})
    (P G P' G' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (r : P ⟶ P') (s : G ⟶ G') :
    let := SheafOfModules.monoidalCategory X.sheaf
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
    let := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
    (DerivedCategory.Q.map r ⊗ₘ DerivedCategory.Q.map s) ≫
        pullbackTensorModelMap X P' G' =
      pullbackTensorModelMap X P G ≫ DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap r s (curriedTensor _) (.up ℤ)) := by
  let := pullbackDescentModuleTensor X
  let := moduleSymmetric X
  let := modulePreadditive X
  let := moduleClosed X
  let := moduleGrothendieck X
  let := moduleResolutions X
  let := moduleDerivedMonoidal X
  have (A B : GradedObject ℤ (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
      GradedObject.HasTensor A B := inferInstance
  let := HomologicalComplex.monoidalCategory
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)
  let := pullbackDescentQLax X
  exact Functor.LaxMonoidal.μ_natural DerivedCategory.Q r s

private theorem tensor_representation_algebra
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (L : C ⥤ D)
    {A B E K T : C} {V W N AP BP NP K' : D}
    (m : A ⊗ B ≅ T) (eA : A ≅ E) (eB : B ≅ K)
    (εT : L.obj T ⟶ V) (a : V ⟶ W) (b : W ⟶ N)
    (ν : AP ⊗ BP ≅ W) (ν' : AP ⊗ NP ≅ N)
    (εA : L.obj A ≅ AP) (εB : L.obj B ⟶ BP) (t : BP ⟶ NP)
    (eN : NP ≅ K') (φ : L.obj K ⟶ K')
    (τ : ∀ A B : C, L.obj (A ⊗ B) ⟶ L.obj A ⊗ L.obj B)
    (hχ : L.map m.hom ≫ εT ≫ a = τ A B ≫ (εA.hom ⊗ₘ εB) ≫ ν.hom)
    (hν : (𝟙 AP ⊗ₘ t) ≫ ν'.hom = ν.hom ≫ b)
    (hrep : εB ≫ t ≫ eN.hom = L.map eB.hom ≫ φ)
    (hnat : L.map (eA.hom ⊗ₘ eB.hom) ≫ τ E K =
      τ A B ≫ (L.map eA.hom ⊗ₘ L.map eB.hom)) :
    εT ≫ (a ≫ b) ≫ ν'.inv ≫ ((εA.inv ≫ L.map eA.hom) ⊗ₘ eN.hom) =
      L.map (m.inv ≫ (eA.hom ⊗ₘ eB.hom)) ≫ τ E K ≫ (L.obj E ◁ φ) := by
  apply (cancel_epi (L.map m.hom)).1
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hχ, ← reassoc_of% hν]
  simp only [ν'.hom_inv_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom]
  simp only [Category.id_comp, Category.assoc, εA.hom_inv_id_assoc]
  rw [hrep]
  rw [← L.map_comp_assoc, m.hom_inv_id, L.map_id, Category.id_comp,
    reassoc_of% hnat]
  rw [tensorHom_comp_whiskerLeft]

/-- Derived identifications for a specified tensor chain map.

Proof: Use the inverse localization tensor map followed by eP tensor c.e for e.
For e', invert the localization tensor map on the pulled-back P and c.N,
then tensor the inverse pullback counit followed by derivedPullback(eP) with c.e'.
The localization maps are invertible since P and its pullback are K-flat.
The total source is K-flat by associativity and K-flatness of both factors.
Its counit is invertible by the K-flat counit theorem. To check the displayed
representation identity, precompose with derivedPullback of the source localization
map, use hχ, and apply naturality of the target localization tensor map.
The second-factor counit followed by Q(c.t) and c.e' is replaced using c.represents.
Naturality hnat with eP and c.e finishes the identity, after canceling the
invertible localization maps. No target K-flatness or stalk assertion is used.
Source: Stacks Project, perfect.tex, Tag 0DJA(1), Tag 0BYJ and
equation-bc before Tag 0DJ8; Cohomology, Tags 079R and 06YB.
(blueprint: lem-pc-tensor-coordinate-identifications). -/
theorem exists_tensor_coordinate_identifications
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (E K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K')
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback g').obj (A ⊗ B) ⟶
        (derivedPullback g').obj A ⊗ (derivedPullback g').obj B)
    (hnat : ∀ (A A' B B' : schemeDerivedCategory X) (a : A ⟶ A') (b : B ⟶ B'),
      (derivedPullback g').map (a ⊗ₘ b) ≫ τ A' B' =
        τ A B ≫ ((derivedPullback g').map a ⊗ₘ (derivedPullback g').map b))
    (c : SingleComplexBaseChange.Coordinates g' K K' φ)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ E) (hP : P.IsKFlatTensor)
    (χ : ((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj
        (pullbackTensorTotal X P c.P) ≅
      pullbackTensorTotal X'
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
        (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P))
    (hχ : (derivedPullback g').map (pullbackTensorModelMap X P c.P) ≫
        cast (by rfl) ((SingleComplexBaseChange.counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P c.P))) ≫
        DerivedCategory.Q.map χ.hom =
      τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj c.P) ≫
        cast (by rfl) ((SingleComplexBaseChange.counit g').app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj P) ⊗ₘ
          (SingleComplexBaseChange.counit g').app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P)) ≫
        pullbackTensorModelMap X'
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P)
          (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj c.P)) :
    let T := pullbackTensorTotal X P c.P
    let N := pullbackTensorTotal X'
      (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj P) c.N
    let d := χ.hom ≫
      HomologicalComplex.mapBifunctorMap (𝟙 _) c.t (curriedTensor _) (.up ℤ)
    ∃ (e : DerivedCategory.Q.obj T ≅ E ⊗ K)
      (e' : DerivedCategory.Q.obj N ≅ (derivedPullback g').obj E ⊗ K'),
      T.IsKFlatTensor ∧
      IsIso ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj T)) ∧
      (cast (by rfl) ((SingleComplexBaseChange.counit g').app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj T)) :
        (derivedPullback g').obj (DerivedCategory.Q.obj T) ⟶
          (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))).obj
            (((Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)).obj T)) ≫
        (DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X'.toRingedSpace))).map d ≫
          e'.hom =
      (derivedPullback g').map e.hom ≫ (τ E K ≫ ((derivedPullback g').obj E ◁ φ)) := by
  classical
  dsimp only
  let H : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ :=
    (Scheme.Modules.tensorPullback g').mapHomologicalComplex (.up ℤ)
  have hPull : CochainComplex.IsKFlatTensor (R := X'.sheaf) (H.obj P) := by
    convert CochainComplex.isKFlat_pullback g'.base X'.sheaf X.sheaf ⟨g'.c⟩ P hP using 1
    rfl
  have hflat : (pullbackTensorTotal X P c.P).IsKFlatTensor :=
    CochainComplex.IsKFlatTensor.mapBifunctor P c.P hP c.isKFlat
  have := modelMap_isIso X P c.P hP
  have := modelMap_isIso X' (H.obj P) c.N hPull
  have := modelMap_isIso X' (H.obj P) (H.obj c.P) hPull
  have := counit_isIso g' P hP
  have := counit_isIso g' (pullbackTensorTotal X P c.P) hflat
  let εP : (derivedPullback g').obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj (H.obj P) := (SingleComplexBaseChange.counit g').app
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let e := (asIso (pullbackTensorModelMap X P c.P)).symm ≪≫ (eP ⊗ᵢ c.e)
  let e' := (asIso (pullbackTensorModelMap X' (H.obj P) c.N)).symm ≪≫
    (((asIso εP).symm ≪≫ (derivedPullback g').mapIso eP) ⊗ᵢ c.e')
  refine ⟨e, e', hflat, inferInstance, ?_⟩
  have hmodel := modelMap_natural X' (H.obj P) (H.obj c.P) (H.obj P) c.N
    (𝟙 (H.obj P)) c.t
  dsimp only at hmodel
  erw [CategoryTheory.Functor.map_id] at hmodel
  have hnat' := hnat _ _ _ _ eP.hom c.e.hom
  simpa only [cast_eq, e, e', Iso.trans_hom, Iso.symm_hom, asIso_hom, asIso_inv,
    tensorIso_hom, Functor.mapIso_hom, Functor.map_comp] using
    tensor_representation_algebra (derivedPullback g')
      (asIso (pullbackTensorModelMap X P c.P)) eP c.e
      ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj (pullbackTensorTotal X P c.P)))
      (DerivedCategory.Q.map χ.hom)
      (DerivedCategory.Q.map
        (HomologicalComplex.mapBifunctorMap (𝟙 _) c.t (curriedTensor _) (.up ℤ)))
      (asIso (pullbackTensorModelMap X' (H.obj P) (H.obj c.P)))
      (asIso (pullbackTensorModelMap X' (H.obj P) c.N)) (asIso εP)
      ((SingleComplexBaseChange.counit g').app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj c.P))
      (DerivedCategory.Q.map c.t) c.e' φ τ
      (by simpa only [cast_eq, asIso_hom, εP, H] using hχ)
      (by convert hmodel using 1 <;> rfl) c.represents hnat'

end AlgebraicGeometry
