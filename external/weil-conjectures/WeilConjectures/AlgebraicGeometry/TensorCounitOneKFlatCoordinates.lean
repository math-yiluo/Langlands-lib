/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CanonicalPullbackTensorComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorProduct
import WeilConjectures.Algebra.Homology.KFlatPullback
import WeilConjectures.AlgebraicGeometry.TensorCounitCoordinateEquation
import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.DerivedPullback
import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.ModulePullbackTensor
import WeilConjectures.AlgebraicGeometry.SingleComplexBaseChangeStalkCondition

/-! # Tensor pullback counit in one K-flat coordinate

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
(blueprint: lem-pc-tensor-counit-one-kflat-coordinates).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
noncomputable section
namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.isGrothendieckAbelian


private theorem cancel_coordinate_tensor
    {D : Type*} [Category* D] [MonoidalCategory D] {V A B P C H : D}
    (l : V ⟶ H) (τ : V ⟶ A ⊗ B) (ep : A ⟶ P) [IsIso ep]
    (eg : B ⟶ C) (ν : P ⊗ C ⟶ H) [IsIso ν]
    (h : l = τ ≫ (ep ⊗ₘ eg) ≫ ν) :
    l ≫ inv ν ≫ (inv ep ⊗ₘ 𝟙 C) = τ ≫ A ◁ eg := by
  rw [h]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  rw [tensorHom_comp_tensorHom,
    IsIso.hom_inv_id, Category.comp_id, id_tensorHom]

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


-- Elaborating the tensor representatives and their canonical counits needs this budget.
-- The `HasMapBifunctor` instances of the K-flat tensor statement exceed the default
-- instance-search budget against the current slopmaster2.
/-- With one K-flat tensor factor, the total-complex counit and the derived
 tensor comparison agree up to the canonical representative isomorphisms.

Source: Stacks Project, cohomology.tex, Tag 079U; perfect.tex, Tag 0DJA(1).
Proof: the localization tensor map Q(P) tensor Q(G) -> Q(Tot(P tensor G))
is invertible because P is K-flat; let a be its associated isomorphism.
Termwise module tensor pullback commutes with sums and has its canonical
tensor isomorphism, so it gives a chain isomorphism from the pullback of the total
complex to Tot(g^*P tensor g^*G). Pullback preserves K-flatness of P; hence the
localization tensor map at g^*P and g^*G is invertible. The universal counit at P
is invertible as well. Compose these isomorphisms to obtain b.
For K-flat G the required equation is the characterizing coordinate equation of
hτ, after canceling the counit at P and the target localization tensor map.
For general G take a K-flat resolution
N -> G. Tensoring it with P preserves quasi-isomorphisms. Naturality
of the universal counits, the localization tensor maps, and the termwise tensor
pullback comparison gives the same equation after precomposing with the induced
isomorphism on derived tensor products. Cancel that isomorphism. This proves the
equation for arbitrary G, without imposing flatness over X or any base scheme.
(blueprint: lem-pc-tensor-counit-one-kflat-coordinates). -/
theorem tensorCounit_oneKFlat_coordinates
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X T : Scheme.{u}} (k : T ⟶ X)
    [@MonoidalPreadditive _ _ _ (SheafOfModules.monoidalCategory X.sheaf)]
    (P G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlatTensor (R := X.sheaf) P)
    (τ : ∀ A B : schemeDerivedCategory X,
      (derivedPullback k).obj (A ⊗ B) ⟶
        (derivedPullback k).obj A ⊗ (derivedPullback k).obj B)
    (hτ : IsCanonicalPullbackTensorComparison k τ) :
    ∃ a : DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj G ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P G
          (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf))),
      ∃ b : (DerivedCategory.Q
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj
            (CochainComplex.mapBifunctor P G
              (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)))) ≅
        (derivedPullback k).obj (DerivedCategory.Q.obj P) ⊗ (DerivedCategory.Q
          (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))).obj
          (((Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)).obj G),
        (derivedPullback k).map a.hom ≫
          cast (by rfl) ((SingleComplexBaseChange.counit k).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj (CochainComplex.mapBifunctor P G
              (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf))))) ≫ b.hom =
          τ (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj G) ≫
            (derivedPullback k).obj (DerivedCategory.Q.obj P) ◁
            cast (by rfl) ((SingleComplexBaseChange.counit k).app
              ((HomotopyCategory.quotient _ (.up ℤ)).obj G)) := by
  classical
  let := SheafOfModules.monoidalCategory X.sheaf
  let := SheafOfModules.monoidalCategory T.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings T.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed T.sheaf).1
  have : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  have : HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) :=
    hasColimitsOfSizeShrink.{0, 0, u, u} _
  obtain ⟨F, hF, hmap, hAdd, ε, hε, φ, hφ, hnat, _⟩ := derivedPullback_tensorProduct k
  have hF' : F = Scheme.Modules.tensorPullback k :=
    CategoryTheory.Functor.ext hF (fun M N f ↦ hmap f)
  subst F
  have hFzero : hF = fun M ↦ rfl := Subsingleton.elim _ _
  rw [hFzero] at hφ
  let : (curriedTensor (SheafOfModules.{u}
      (moduleRings X.toRingedSpace))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let : (curriedTensor (SheafOfModules.{u}
      (moduleRings T.toRingedSpace))).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor T.sheaf
  let : ∀ M : SheafOfModules.{u} (moduleRings X.toRingedSpace),
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M
  let : ∀ M : SheafOfModules.{u} (moduleRings T.toRingedSpace),
      ((curriedTensor _).obj M).PreservesZeroMorphisms :=
    fun M ↦ SheafOfModules.preservesZeroMorphisms_curriedTensor_obj T.sheaf M
  have hgeneral := tensorCounit_coordinateEquation k P G τ hτ (φ P G) (by
    simpa only [eqToHom_refl, tensorHom_id, MonoidalCategory.id_whiskerRight,
      Category.id_comp] using hφ P G)
  let Q := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
  let QT := DerivedCategory.Q (C := SheafOfModules.{u} (moduleRings T.toRingedSpace))
  let K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings T.toRingedSpace)) ℤ :=
    (Scheme.Modules.tensorPullback k).mapHomologicalComplex (.up ℤ)
  have hPull : CochainComplex.IsKFlatTensor (R := T.sheaf) (K.obj P) := by
    convert CochainComplex.isKFlat_pullback k.base T.sheaf X.sheaf ⟨k.c⟩ P hP using 1
    rfl
  have := modelMap_isIso X P G hP
  have := modelMap_isIso T (K.obj P) (K.obj G) hPull
  let ep : (derivedPullback k).obj (Q.obj P) ⟶ QT.obj (K.obj P) :=
    (SingleComplexBaseChange.counit k).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  let eg : (derivedPullback k).obj (Q.obj G) ⟶ QT.obj (K.obj G) :=
    (SingleComplexBaseChange.counit k).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj G)
  have : IsIso ep := counit_isIso k P hP
  let ν := pullbackTensorModelMap T (K.obj P) (K.obj G)
  let a : Q.obj P ⊗ Q.obj G ≅ Q.obj (pullbackTensorTotal X P G) :=
    asIso (pullbackTensorModelMap X P G)
  let b : QT.obj (K.obj (pullbackTensorTotal X P G)) ≅
      (derivedPullback k).obj (Q.obj P) ⊗ QT.obj (K.obj G) :=
    QT.mapIso (φ P G) ≪≫ (asIso ν).symm ≪≫ ((asIso ep).symm ⊗ᵢ Iso.refl _)
  refine ⟨a, b, ?_⟩
  simp only [cast_eq] at hgeneral
  have h := cancel_coordinate_tensor _ (τ (Q.obj P) (Q.obj G)) ep eg ν hgeneral
  simpa only [cast_eq, a, b, Q, QT, K, ep, eg, pullbackTensorTotal, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv, Functor.mapIso_hom, tensorIso_hom, Iso.refl_hom, Category.assoc] using h

end AlgebraicGeometry
