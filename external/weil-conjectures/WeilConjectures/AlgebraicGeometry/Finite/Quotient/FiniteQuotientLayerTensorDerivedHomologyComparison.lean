/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModelData

import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorDerivedSliceComparison

/-! # Derived chart homology comparison for the finite quotient layer

Source: Stacks Project, sites-cohomology.tex, Tags 094I and 06YU.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-derived-homology-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

private theorem homology_iso_of_derived_iso
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] [HasDerivedCategory C] [HasDerivedCategory D]
    {K L : DerivedCategory C} (e : Nonempty (F.mapDerivedCategory.obj K ≅
      F.mapDerivedCategory.obj L)) (q : ℤ) :
    Nonempty (F.obj ((DerivedCategory.homologyFunctor C q).obj K) ≅
      F.obj ((DerivedCategory.homologyFunctor C q).obj L)) := by
  obtain ⟨e⟩ := e
  exact ⟨(F.mapDerivedCategoryHomologyFunctorIso q).app K ≪≫
    (DerivedCategory.homologyFunctor D q).mapIso e ≪≫
      ((F.mapDerivedCategoryHomologyFunctorIso q).app L).symm⟩

/--
The chartwise homology of the actual layer agrees with the chartwise homology of
its derived constant tensor model.  This is the derived-tensor and exact-slice
part of the comparison; the final identification with ordinary algebraic
homology is recorded separately.

Source: Stacks Project, sites-cohomology.tex, Tag 094I (balancing identity)
and Tag 06YU (bounded-above flat-complex calculation).
Proof: resolve the residue reduction by the bounded-above projective complex,
apply derived tensor descent to the kernel defining the actual layer, restrict
to the slice over Z, and transport along the supplied residue-model
isomorphism. Exact slice restriction and the homology functor carry the
resulting derived isomorphism to the displayed chart homology isomorphism.
The remaining replacement of the derived constant model by ordinary homology
is deliberately isolated in the companion identification theorem.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-derived-homology-comparison).
-/
theorem finiteQuotient_layer_tensor_derived_homology_comparison
    (X : Scheme.{t})
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (b : ℤ) (n : ℕ) (Z : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ)
    (hPb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (0 + 1)) (P.X i))
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj Z) ((completedAdicQuotientReduction X d 0).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj Z) ((completedAdicDerivedChange X (φ 0)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    ∀ q : ℤ, Nonempty
      ((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            (finiteQuotientLayerObject X d M n)) ≅
        (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
          ((DerivedCategory.homologyFunctor _ q).obj
            ((completedAdicDerivedChange X (φ (n + 1))).obj
              (DerivedCategory.Q.obj
                (finiteModelConstantComplex X _
                  (finiteQuotientLayerTensorComplex d.ideal n P)))))) := by
  intro q
  let R := completedAdicFiniteRing X d (n + 1)
  let U := (toProEt X).obj Z
  let F := SheafOfModules.overFunctor.{t + 1} R U
  let _ : F.Additive := (ringedOverFunctor_exactGeneral R U).1
  let _ : PreservesFiniteLimits F := (ringedOverFunctor_exactGeneral R U).2.1
  let _ : PreservesFiniteColimits F := (ringedOverFunctor_exactGeneral R U).2.2
  let K := finiteQuotientLayerObject X d M n
  let L := (completedAdicDerivedChange X (φ (n + 1))).obj
    (DerivedCategory.Q.obj
      (finiteModelConstantComplex X _
        (finiteQuotientLayerTensorComplex d.ideal n P)))
  have hKL : Nonempty (F.mapDerivedCategory.obj K ≅ F.mapDerivedCategory.obj L) := by
    simpa only [F, R, U, ringedDerivedRestrictionGeneral] using
      finiteQuotient_layer_tensor_derived_slice_comparison X d φ hφ hcompat M b n Z P
        hPb hP e
  exact homology_iso_of_derived_iso F hKL q

end AlgebraicGeometry.Scheme
