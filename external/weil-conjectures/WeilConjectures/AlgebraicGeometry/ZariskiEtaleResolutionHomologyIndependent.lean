/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Resolution comparison bridge -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction

/-- Comparisons with equal augmentations induce equal maps of section homology.

Proof: exactness of inverse image makes its right adjoint preserve injectives.
The difference of a and b vanishes on the augmentation of R. Inductively factor
this difference through successive differentials of R and extend to the injective
terms of the pushed complex. This constructs a null homotopy. Evaluation is additive,
so preserves this homotopy, and homotopic maps induce equal homology maps.

Source: Stacks Project, Tags 01FB, 013P and 015B.
(blueprint: lem-weil-pbc-zariski-etale-resolution-homology-independent) -/
theorem zariski_etale_resolution_homology_independent
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt
      (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1})]
    [HasExt (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [(sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).Additive]
    [PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F)
    (R : InjectiveResolution ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).obj F))
    (a : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (ha : R.ι.f 0 ≫ a.f 0 = (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map (I.ι.f 0))
    (b : R.cocomplex ⟶
      ((i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj I.cocomplex)
    (hb : R.ι.f 0 ≫ b.f 0 = (i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology).map (I.ι.f 0))
    (q : ℕ) (V : X.Opens) :
    (HomologicalComplex.homologyMap
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).map a) q) =
      (HomologicalComplex.homologyMap
          (((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
            (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomologicalComplex
               (ComplexShape.up ℕ)).map b) q) := by
  classical
  let G := i.sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology
  let K := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let : G.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (sheafAdjunctionContinuous i AddCommGrpCat.{u + 1}
        (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology)
  have (n : ℕ) : Injective (K.X n) := G.injective_obj (I.cocomplex.X n)
  let f : R.cocomplex ⟶ K := a - b
  have hf : R.ι.f 0 ≫ f.f 0 = 0 := by
    simp only [f, HomologicalComplex.sub_f_apply, Preadditive.comp_sub, ha, hb, sub_self]
  let h₀ := R.exact₀.descToInjective (f.f 0) hf
  have hh₀ : R.cocomplex.d 0 1 ≫ h₀ = f.f 0 :=
    R.exact₀.comp_descToInjective _ _
  have hz : R.cocomplex.d 0 1 ≫ (f.f 1 - h₀ ≫ K.d 0 1) = 0 := by
    rw [Preadditive.comp_sub, ← Category.assoc, hh₀, f.comm, sub_self]
  let h₁ := (R.exact_succ 0).descToInjective (f.f 1 - h₀ ≫ K.d 0 1) hz
  have hh₁ : R.cocomplex.d 1 2 ≫ h₁ = f.f 1 - h₀ ≫ K.d 0 1 :=
    (R.exact_succ 0).comp_descToInjective _ _
  have hnull : Homotopy f 0 := by
    refine Homotopy.mkCoinductive f h₀ ?_ h₁ ?_ ?_
    · simpa using hh₀.symm
    · exact (eq_add_of_sub_eq hh₁.symm).trans (add_comm _ _)
    · intro n data
      rcases data with ⟨g, g', w⟩
      have hz' : R.cocomplex.d (n + 1) (n + 2) ≫
          (f.f (n + 2) - g' ≫ K.d (n + 1) (n + 2)) = 0 := by
        rw [Preadditive.comp_sub, ← f.comm, ← Category.assoc, w,
          Preadditive.add_comp, Category.assoc, Category.assoc,
          HomologicalComplex.d_comp_d, comp_zero, zero_add, sub_self]
      refine ⟨(R.exact_succ (n + 1)).descToInjective _ hz', ?_⟩
      have hh := (R.exact_succ (n + 1)).comp_descToInjective _ hz'
      exact (eq_add_of_sub_eq hh.symm).trans (add_comm _ _)
  have hab : Homotopy a b := Homotopy.equivSubZero.invFun hnull
  exact ((sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1} ⋙
    (evaluation X.Opensᵒᵖ AddCommGrpCat.{u + 1}).obj (op V)).mapHomotopy hab).homologyMap_eq q

