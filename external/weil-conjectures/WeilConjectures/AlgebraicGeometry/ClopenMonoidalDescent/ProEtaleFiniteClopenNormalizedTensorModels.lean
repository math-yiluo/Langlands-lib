/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenMonoidalNormalization
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenKFlatMonoidalDescent
import WeilConjectures.AlgebraicGeometry.ClopenMonoidalDescent.ProEtaleClopenKFlatModelNormalization

/-! # Normalized tensor models for a finite clopen partition

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YU and 0FPT.
(blueprint: lem-pur-finite-clopen-normalized-tensor-models)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.modulesAbelian
attribute [-instance] AlgebraicGeometry.Scheme.ProEt.ClopenLocalization.hasDerived
attribute [local irreducible] DerivedCategory.Q Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors HasDerivedCategory.standard
  SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
  RingedDerivedNative.monoidal RingedDerivedNative.symmetric coefficientTotalTensor
  AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent.ModelNormalization
namespace AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent

-- The existential comparison types include dependent monoidal localization structures.
/-- Produce the normalized ordinary, total and derived tensor witnesses of each component.
Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YU and 0FPT
(blueprint: lem-pur-finite-clopen-normalized-tensor-models).

Proof: obtain normalized braided structures and total comparisons from the finite-clopen
monoidal descent theorem. Its model square is initially normalized on flat-term K-flat
pairs. Componentwise K-flat detection supplies preservation by restriction. Identify the
derived comparison with the inverse braided tensorator inside the normalization predicate,
then apply the proved extension of model normalization to all K-flat pairs. The ordinary
pure-tensor and total-generator equalities are the supplied normalization clauses. -/
theorem finite_clopen_normalized_tensor_models
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    ∀ i, ∃ (h : (clopenTensorRestriction.{t, u} (j i) R).Braided)
      (c : coefficientTotalTensor.{u, t + 1, t} (topology X) R ⋙
          (clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ) ≅
        (((clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).prod
          ((clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ))) ⋙
            coefficientTotalTensor.{u, t + 1, t} (topology (Y i))
              ((clopenTensorRings.{t, u} (j i)).obj R))
      (d : (derivedRestriction.{t, u} (j i) R).Braided),
      (∀ (F H : clopenTensorModules.{t, u} R) (U : (Y i).ProEt) (x : F.val.obj
          (op ((MorphismProperty.Over.map ⊤
            (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : H.val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        ((clopenTensorComparison (j i) R h F H).hom.val.app (op U))
          (clopenTensorPure R F H _ x y) =
        clopenTensorPure ((clopenTensorRings.{t, u} (j i)).obj R)
          ((clopenTensorRestriction.{t, u} (j i) R).obj F)
          ((clopenTensorRestriction.{t, u} (j i) R).obj H) (op U) x y) ∧
      (∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ) (p q n : ℤ) (hpq : p + q = n)
        (U : (Y i).ProEt)
        (x : (P.X p).val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U)))
        (y : (Q.X q).val.obj (op ((MorphismProperty.Over.map ⊤
          (inferInstance : WeaklyEtale (j i))).obj U))),
        (((c.hom.app (P, Q)).f n).val.app (op U))
          (coefficientTensorGenerator.{u, t + 1, t} (topology X) R P Q p q n hpq _ x y) =
        coefficientTensorGenerator.{u, t + 1, t} (topology (Y i))
          ((clopenTensorRings.{t, u} (j i)).obj R)
          (((clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)
          (((clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)
          p q n hpq (op U) x y) ∧
      (∀ (P Q : CochainComplex (clopenTensorModules.{t, u} R) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) P)
        (_hQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology X) (R := R) Q)
        (hiP : CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (clopenTensorRings.{t, u} (j i)).obj R)
          (((clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P))
        (_hiQ : CochainComplex.IsKFlatIndependentCoefficients (J := topology (Y i))
          (R := (clopenTensorRings.{t, u} (j i)).obj R)
          (((clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)),
        (derivedRestriction.{t, u} (j i) R).map
            (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology X) R P Q
              (Or.inl hP)).hom ≫
          (braidedComparison (j i) R d).hom.app
            (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
          ((clopenTensorRestriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app P ⊗ₘ
            (clopenTensorRestriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app Q) =
        (clopenTensorRestriction.{t, u} (j i) R).mapDerivedCategoryFactors.hom.app
            ((coefficientTotalTensor.{u, t + 1, t} (topology X) R).obj (P, Q)) ≫
          DerivedCategory.Q.map (c.hom.app (P, Q)) ≫
          (RingedDerivedNative.tensorIso.{t + 1, t, u} (topology (Y i))
            ((clopenTensorRings.{t, u} (j i)).obj R)
            (((clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj P)
            (((clopenTensorRestriction.{t, u} (j i) R).mapHomologicalComplex (.up ℤ)).obj Q)
            (Or.inl hiP)).hom) := by
  have hk := (clopen_total_tensor_kflat_detection
    X I Y j hdisjoint hcover R).2.1
  obtain ⟨_, d, ht⟩ := clopen_kflat_monoidal_descent
    X I Y j hdisjoint hcover R
  intro i
  obtain ⟨h, b, c, hn, hm, _, hc, _⟩ := ht i
  refine ⟨h, b, d i, hn.1, hn.2, ?_⟩
  intro P Q hP hQ hiP _
  have hm' : ModelNormalization (j i) R b
      (braidedComparison (j i) R (d i)) := by
    rw [hc]
    exact hm
  exact clopen_kflat_model_normalization
    (j i) R (fun P hp ↦ (hk P).mp hp i) b _ hm' P Q hP hQ hiP

end AlgebraicGeometry.Scheme.ProEt.ClopenMonoidalDescent
