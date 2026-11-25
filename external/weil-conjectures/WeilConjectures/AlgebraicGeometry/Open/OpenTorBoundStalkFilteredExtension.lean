/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor

import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedTensorStalk
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.Algebra.Colimit.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Stalk and filtered-colimit extension of finite Tor tests
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Exact filtered module colimits preserve short-complex homology. -/
private theorem shortComplexHomologyPreserves
    (S : Type u) [CommRing S] (I : Type u) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I (ShortComplex.homologyFunctor (ModuleCat.{u} S)) := by
  classical
  refine ⟨fun {F} ↦ ?_⟩
  have : (colim (J := I) (C := ModuleCat.{u} S)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  let K := (ShortComplex.functorEquivalence I (ModuleCat.{u} S)).inverse.obj F
  let e : K.homology ≅ F ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} S) :=
    NatIso.ofComponents
      (fun i ↦ (K.mapHomologyIso ((evaluation I (ModuleCat.{u} S)).obj i)).symm)
      (by
        intro i j f
        have h := K.homologyMap_mapNatTrans ((evaluation I (ModuleCat.{u} S)).map f)
        change ShortComplex.homologyMap (F.map f) = _ at h
        change K.homology.map f ≫
          (K.mapHomologyIso ((evaluation I (ModuleCat.{u} S)).obj j)).inv =
          (K.mapHomologyIso ((evaluation I (ModuleCat.{u} S)).obj i)).inv ≫
            ShortComplex.homologyMap (F.map f)
        rw [h]
        simp)
  let a : colimit (F ⋙ ShortComplex.homologyFunctor (ModuleCat.{u} S)) ≅
      (ShortComplex.colimitCocone F).pt.homology :=
    (colim.mapIso e).symm ≪≫ (K.mapHomologyIso colim).symm
  refine preservesColimit_of_preserves_colimit_cocone
    (ShortComplex.isColimitColimitCocone F) ?_
  apply IsColimit.ofIsoColimit (colimit.isColimit _)
  refine Cocone.ext a ?_
  intro i
  have h := K.homologyMap_mapNatTrans (colim.ι (C := ModuleCat.{u} S) i)
  change ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i) = _ at h
  change colimit.ι _ i ≫ a.hom =
    ShortComplex.homologyMap ((ShortComplex.colimitCocone F).ι.app i)
  rw [h]
  simp [a, e]

/-- Compute complex homology through its three-term short complex. -/
private theorem complexHomologyPreserves
    (S : Type u) [CommRing S] (I : Type u) [SmallCategory I] [IsFiltered I] (n : ℤ) :
    PreservesColimitsOfShape I
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (.up ℤ) n) := by
  have := shortComplexHomologyPreserves S I
  have : PreservesColimitsOfShape I
      (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} S) (.up ℤ) n) := by
    refine ⟨fun {F} ↦ ⟨fun {s} hs ↦ ⟨?_⟩⟩⟩
    apply ShortComplex.isColimitOfIsColimitπ
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
    · exact isColimitOfPreserves (HomologicalComplex.eval _ _ _) hs
  exact preservesColimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso (ModuleCat.{u} S) (.up ℤ) n).symm

/-- A K-flat representative computes tensor cohomology and its filtered colimits. -/
private theorem tensorHomologyPreserves
    (S : Type u) [CommRing S] (I : Type u) [SmallCategory I] [IsFiltered I]
    (Q : _root_.DerivedCategory (ModuleCat.{u} S)) (n : ℤ) :
    PreservesColimitsOfShape I
      (_root_.DerivedCategory.singleFunctor (ModuleCat.{u} S) 0 ⋙
        tensorLeft Q ⋙ _root_.DerivedCategory.homologyFunctor _ n) := by
  obtain ⟨P, hP, ⟨eP⟩⟩ := _root_.DerivedCategory.exists_kFlat_iso Q
  obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  have := _root_.DerivedCategory.isIso_tensorLeftCounit _ hP
  let π := HomotopyCategory.quotient (ModuleCat.{u} S) (.up ℤ)
  let H := _root_.DerivedCategory.homologyFunctor (ModuleCat.{u} S) n
  let s := HomologicalComplex.single (ModuleCat.{u} S) (.up ℤ) 0
  let a : _root_.DerivedCategory.Q ⋙ tensorLeft Q ≅
      tensorLeft J ⋙ _root_.DerivedCategory.Q :=
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso eP.symm) ≪≫
    Functor.isoWhiskerRight (_root_.DerivedCategory.quotientCompQhIso _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft π (asIso (_root_.DerivedCategory.tensorLeftCounit _)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (asIso ((Functor.OplaxMonoidal.δNatTrans π).app J)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (_root_.DerivedCategory.quotientCompQhIso _)
  let b : _root_.DerivedCategory.singleFunctor (ModuleCat.{u} S) 0 ⋙ tensorLeft Q ⋙ H ≅
      s ⋙ tensorLeft J ⋙ HomologicalComplex.homologyFunctor (ModuleCat.{u} S) (.up ℤ) n :=
    Functor.isoWhiskerRight (_root_.DerivedCategory.singleFunctorIsoCompQ _ 0) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft s ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight a H ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (_root_.DerivedCategory.homologyFunctorFactors _ n))
  have := complexHomologyPreserves S I n
  have : PreservesColimitsOfShape I (tensorLeft J) := by
    exact inferInstanceAs (PreservesColimitsOfShape I
      ((curriedTensor (ModuleCat.{u} S)).map₂CochainComplex.obj J))
  have : PreservesColimitsOfShape I s := by infer_instance
  exact preservesColimitsOfShape_of_natIso b.symm

/-- Every module is the filtered colimit of finite submodules over a finite ring. -/
private theorem module_vanish_of_finite_tests
    (S : Type u) [CommRing S] [Finite S]
    (Q : _root_.DerivedCategory (ModuleCat.{u} S)) (n : ℤ)
    (h : ∀ M : ModuleCat.{u} S, Finite M → IsZero
      ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (Q ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj M)))
    (M : ModuleCat.{u} S) : IsZero
      ((_root_.DerivedCategory.homologyFunctor _ n).obj
        (Q ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj M)) := by
  classical
  let I := {N : Submodule S M // N.FG}
  let G : I → Type u := fun N ↦ N.1
  let f := Module.fgSystem S M
  have : Nonempty I := ⟨⟨⊥, Submodule.fg_bot⟩⟩
  let H := _root_.DerivedCategory.singleFunctor (ModuleCat.{u} S) 0 ⋙
    tensorLeft Q ⋙ _root_.DerivedCategory.homologyFunctor _ n
  have := tensorHomologyPreserves S I Q n
  have hc := isColimitOfPreserves H (ModuleCat.directLimitIsColimit G f)
  have hz : IsZero (H.obj (ModuleCat.of S (Module.DirectLimit G f))) :=
    hc.isZero_pt (Functor.isZero _ (fun N ↦ by
      have := Module.Finite.of_fg N.2
      exact h (ModuleCat.of S N.1) (Module.finite_of_finite S)))
  exact hz.of_iso (H.mapIso (Module.fgSystem.equiv S M).toModuleIso.symm)

/-- Exact derived stalks commute with tensoring by a degree-zero sheaf. -/
private theorem stalk_tensor_single_iso
    (A : Type (u + 1)) [CommRing A] {T : Scheme.{u}}
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (t : Spec (.of Ω) ⟶ T)
    (Q : DerivedCategoryModule A T)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (q : ℤ) :
    let S := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)
    Nonempty (S.obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (((derivedTensor (ModuleCat.{u + 1} A) T).obj Q).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≅
      (_root_.DerivedCategory.homologyFunctor _ q).obj
        (S.mapDerivedCategory.obj Q ⊗
          (_root_.DerivedCategory.singleFunctor _ 0).obj (S.obj F))) := by
  dsimp only
  let S := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)
  let M := (_root_.DerivedCategory.singleFunctor _ 0).obj F
  have ht : derivedTensor (ModuleCat.{u + 1} A) T =
      curriedTensor (DerivedCategoryModule A T) := rfl
  have h := congrArg (fun H ↦ (H.obj Q).obj M) ht
  obtain ⟨e⟩ := exactFunctor_tensor_iso Q M S
  let e₀ := S.mapDerivedCategory.mapIso (eqToIso h) ≪≫ e
  exact ⟨(S.mapDerivedCategoryHomologyFunctorIso q).app _ ≪≫
    (_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (e₀ ≪≫ tensorIso (Iso.refl _) ((S.mapDerivedCategorySingleFunctor 0).app F))⟩

/-- Finite constant-module Tor tests extend to arbitrary module sheaves. -/
theorem open_tor_bound_stalk_filtered_extension
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {T : Scheme.{u}} (a b : ℤ) (Q : DerivedCategoryModule A T)
    (hfinite : ∀ (M : ModuleCat.{u + 1} A), Finite M → ∀ (q : ℤ),
      q < a ∨ b < q → IsZero
        ((_root_.DerivedCategory.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) q).obj
          (((derivedTensor (ModuleCat.{u + 1} A) T).obj Q).obj
            ((_root_.DerivedCategory.singleFunctor
              (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0).obj
              ((constantSheaf T.smallEtaleTopology
                (ModuleCat.{u + 1} A)).obj M))))) :
    DerivedCategory.hasTorAmplitudeIn A T a b Q := by
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} A)) :=
    preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
  intro F q hq
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Scheme.sheafHom_ext_of_sheafFiber_map_algClosurePoint
  intro x
  let t := T.algClosurePoint x
  let S := (Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} A)
  let C := S.mapDerivedCategory.obj Q
  have ht (M : ModuleCat.{u + 1} A) (hM : Finite M) :
      IsZero ((_root_.DerivedCategory.homologyFunctor _ q).obj
        (C ⊗ (_root_.DerivedCategory.singleFunctor _ 0).obj M)) := by
    obtain ⟨i⟩ := stalk_tensor_single_iso A t Q
      ((constantSheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)).obj M) q
    have hz := (S.map_isZero (hfinite M hM q hq)).of_iso i.symm
    let c := (Scheme.pointSmallEtale t).sheafFiberConstantSheafIso
      (A := ModuleCat.{u + 1} A) M
    exact hz.of_iso ((_root_.DerivedCategory.homologyFunctor _ q).mapIso
      (tensorIso (Iso.refl _) ((_root_.DerivedCategory.singleFunctor _ 0).mapIso c.symm)))
  have hz := module_vanish_of_finite_tests A C q ht (S.obj F)
  obtain ⟨i⟩ := stalk_tensor_single_iso A t Q F q
  have hs := hz.of_iso i
  change S.map (𝟙 _) = S.map 0
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact hs.eq_of_src
    (𝟙 (S.obj ((_root_.DerivedCategory.homologyFunctor _ q).obj
      (((derivedTensor (ModuleCat.{u + 1} A) T).obj Q).obj
        ((_root_.DerivedCategory.singleFunctor _ 0).obj F))))) 0

end AlgebraicGeometry.Etale
