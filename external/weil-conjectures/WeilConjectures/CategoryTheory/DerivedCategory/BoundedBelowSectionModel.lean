/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import
  WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjectiveResolution
public import Mathlib.Algebra.Homology.CochainComplexPlus
import WeilConjectures.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex

/-!
# Comparing a bounded-below section model with the right derived functor

Source: Stacks Project, Tag 09A2, proof by a bounded-below injective resolution.
-/

@[expose] public section

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

private noncomputable def chainRightDerivedUnit
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    [Abelian.HasKInjectiveResolutions A] (F : A ⥤ B) [F.Additive] :
    F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ F.rightDerivedFunctor where
  app K :=
    (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
      F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
        F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K)
  naturality K L f := by
    have h := F.rightDerivedFunctorUnit.naturality
      ((HomotopyCategory.quotient A (.up ℤ)).map f)
    simp only [Functor.comp_map, Functor.mapHomotopyCategory_map] at h
    simp only [Functor.comp_map,
      DerivedCategory.quotientCompQhIso_inv_naturality_assoc, Category.assoc]
    rw [reassoc_of% h, ← F.rightDerivedFunctor.map_comp, ← F.rightDerivedFunctor.map_comp,
      DerivedCategory.quotientCompQhIso_hom_naturality]

/-- A section-total model which inverts bounded-below quasi-isomorphisms and whose
augmentation is a quasi-isomorphism on injective complexes computes the derived functor.
Source: Stacks Project, Tag 09A2, injective-resolution comparison.
(auxiliary; not a blueprint node).
Proof: choose a bounded-below injective resolution of each input. Both the model of
the resolution map and the augmentation on its injective target become invertible
in the derived category. Compose their inverses with the derived unit at that target.
For naturality, lift each coefficient map to its injective resolutions up to homotopy.
The derived functor and the model identify homotopic bounded-below maps: a cylinder
stays bounded below and its quasi-isomorphic projection becomes invertible. Naturality
of the augmentation and of the derived unit then proves the desired square. -/
theorem boundedBelow_sectionModel
    {A : Type v} [Category.{w} A] [Abelian A] [HasDerivedCategory.{w} A]
    {B : Type u} [Category.{z} B] [Abelian B] [HasDerivedCategory.{z} B]
    [Abelian.HasKInjectiveResolutions A] [EnoughInjectives A]
    (F : A ⥤ B) [F.Additive] (H : CochainComplex A ℤ ⥤ CochainComplex B ℤ)
    (α : F.mapHomologicalComplex (.up ℤ) ⟶ H)
    (hH : ∀ (K L : CochainComplex.Plus A) (f : K ⟶ L),
      QuasiIso f.hom → QuasiIso (H.map f.hom))
    (hα : ∀ (J : CochainComplex.Plus A), (∀ n : ℤ, Injective (J.obj.X n)) →
      QuasiIso (α.app J.obj)) (a : ℤ) :
    ∃ e : ∀ (K : CochainComplex A ℤ) (_ : K.IsStrictlyGE a),
        F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj (H.obj K),
      ∀ (K L : CochainComplex A ℤ) (hK : K.IsStrictlyGE a) (hL : L.IsStrictlyGE a)
        (f : K ⟶ L),
        F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫ (e L hL).hom =
          (e K hK).hom ≫ DerivedCategory.Q.map (H.map f) := by
  classical
  let S := {K : CochainComplex A ℤ // K.IsStrictlyGE a}
  have res (K : S) : ∃ (J : CochainComplex A ℤ) (j : K.val ⟶ J),
      ∃ (_ : QuasiIso j) (_ : ∀ n : ℤ, Injective (J.X n)), J.IsStrictlyGE a := by
    have := K.property
    exact CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K.val a
  choose J j hj hJ hJa using res
  have (K : S) : QuasiIso (j K) := hj K
  have (K : S) : (J K).IsStrictlyGE a := hJa K
  have (K : S) (n : ℤ) : Injective ((J K).X n) := hJ K n
  have (K : S) : (J K).IsKInjective := CochainComplex.isKInjective_of_injective (J K) a
  let R (K : S) : K.val.KInjectiveResolution := { I := J K, ι := j K }
  let ν := chainRightDerivedUnit F
  have hν (K : S) : IsIso (ν.app (J K)) := by
    dsimp [ν, chainRightDerivedUnit]
    infer_instance
  have hαJ (K : S) : QuasiIso (α.app (J K)) := hα ⟨J K, a, hJa K⟩ (hJ K)
  have hHj (K : S) : QuasiIso (H.map (j K)) :=
    hH ⟨K.val, a, K.property⟩ ⟨J K, a, hJa K⟩ ⟨j K⟩ (hj K)
  let e (K : S) : F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K.val) ≅
      DerivedCategory.Q.obj (H.obj K.val) :=
    asIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map (j K))) ≪≫
      (asIso (ν.app (J K))).symm ≪≫ asIso (DerivedCategory.Q.map (α.app (J K))) ≪≫
        (asIso (DerivedCategory.Q.map (H.map (j K)))).symm
  have he (K : S) : (e K).hom ≫ DerivedCategory.Q.map (H.map (j K)) =
      F.rightDerivedFunctor.map (DerivedCategory.Q.map (j K)) ≫
        CategoryTheory.inv (ν.app (J K)) ≫ DerivedCategory.Q.map (α.app (J K)) := by
    simp [e]
  refine ⟨fun K hK ↦ e ⟨K, hK⟩, ?_⟩
  intro K L hK hL f
  let K' : S := ⟨K, hK⟩
  let L' : S := ⟨L, hL⟩
  let g := (R K').map (R L') f
  have hhom : Homotopy (j K' ≫ g) (f ≫ j L') := (R K').mapHomotopy (R L') f
  have hR : F.rightDerivedFunctor.map (DerivedCategory.Q.map (j K')) ≫
      F.rightDerivedFunctor.map (DerivedCategory.Q.map g) =
      F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map (j L')) := by
    simpa only [Functor.comp_map, Functor.map_comp] using
      AlgebraicGeometry.Scheme.ProEt.map_eq_of_boundedBelow_homotopy
        (DerivedCategory.Q ⋙ F.rightDerivedFunctor)
        (fun E G φ hφ ↦ by
          have := hφ
          change IsIso (F.rightDerivedFunctor.map (DerivedCategory.Q.map φ.hom))
          infer_instance)
        ⟨K, a, hK⟩ ⟨J L', a, hJa L'⟩ _ _ hhom
  have hT : DerivedCategory.Q.map (H.map (j K')) ≫ DerivedCategory.Q.map (H.map g) =
      DerivedCategory.Q.map (H.map f) ≫ DerivedCategory.Q.map (H.map (j L')) := by
    simpa only [Functor.comp_map, Functor.map_comp] using
      AlgebraicGeometry.Scheme.ProEt.map_eq_of_boundedBelow_homotopy (H ⋙ DerivedCategory.Q)
        (fun E G φ hφ ↦ by
          have := hH E G φ hφ
          change IsIso (DerivedCategory.Q.map (H.map φ.hom))
          infer_instance)
        ⟨K, a, hK⟩ ⟨J L', a, hJa L'⟩ _ _ hhom
  have hνg : F.rightDerivedFunctor.map (DerivedCategory.Q.map g) ≫
      CategoryTheory.inv (ν.app (J L')) =
      CategoryTheory.inv (ν.app (J K')) ≫ DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map g) := by
    apply (cancel_mono (ν.app (J L'))).mp
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    have hn := ν.naturality g
    change DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) ≫
      ν.app (J L') = ν.app (J K') ≫
        F.rightDerivedFunctor.map (DerivedCategory.Q.map g) at hn
    rw [hn]
    simp
  have hαg : DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) ≫
      DerivedCategory.Q.map (α.app (J L')) =
      DerivedCategory.Q.map (α.app (J K')) ≫ DerivedCategory.Q.map (H.map g) := by
    rw [← Functor.map_comp, ← Functor.map_comp, α.naturality]
  apply (cancel_mono (DerivedCategory.Q.map (H.map (j L')))).mp
  change (F.rightDerivedFunctor.map (DerivedCategory.Q.map f) ≫ (e L').hom) ≫ _ =
    ((e K').hom ≫ DerivedCategory.Q.map (H.map f)) ≫ _
  simp only [Category.assoc]
  rw [he]
  rw [← Category.assoc, ← hR]
  simp only [Category.assoc]
  rw [reassoc_of% hνg, hαg]
  rw [← reassoc_of% (he K'), hT]

end CategoryTheory.Functor
