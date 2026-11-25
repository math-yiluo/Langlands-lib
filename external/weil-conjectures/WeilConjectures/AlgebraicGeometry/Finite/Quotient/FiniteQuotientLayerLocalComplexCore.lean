/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorHomologyComparison

/-! # Chartwise comparison for finite quotient coefficient layers
Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-local-complex-core).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- The residue perfect complex admits a finite local model for the coefficient layer.

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-local-complex-core).

Proof: Let Q=I^(n+1)/I^(n+2), regarded as a finite module over A/I. The
compatibility squares identify the layer object with the residue reduction
balanced-tensored with Q and restricted to the successor coefficient ring. On the
specified chart, tensor the given bounded finite-projective residue complex with
Q. Projectivity computes the derived tensor by ordinary tensor, while the
finite quotient and the annihilation by I make every term finite over the
successor ring. Exact constant realization and exact slice restriction transport
the resulting homology identifications to the layer object. The support bounds
are inherited termwise; empty charts use the zero complex.
-/
theorem finiteQuotient_layer_local_complex_core
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n))
    (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d))
    (a b : ℤ) (n : ℕ) (Z : X.Etale)
    (P : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (0 + 1))) ℤ)
    (hPa : P.IsStrictlyGE a) (hPb : P.IsStrictlyLE b)
    (hP : ∀ i : ℤ, Module.Projective (A ⧸ d.ideal ^ (0 + 1)) (P.X i) ∧
      Module.Finite (A ⧸ d.ideal ^ (0 + 1)) (P.X i))
    (e : Nonempty
      (ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj Z) ((completedAdicQuotientReduction X d 0).obj M) ≅
        ringedSiteDerivedRestrictionOfUniverses (completedAdicFiniteRing X d 0)
          ((toProEt X).obj Z) ((completedAdicDerivedChange X (φ 0)).obj
            (DerivedCategory.Q.obj (finiteModelConstantComplex X _ P))))) :
    ∃ Q : CochainComplex (ModuleCat.{t} (A ⧸ d.ideal ^ (n + 1 + 1))) ℤ,
      Q.IsStrictlyGE a ∧ Q.IsStrictlyLE b ∧
        (∀ i : ℤ, Module.Finite (A ⧸ d.ideal ^ (n + 1 + 1)) (Q.X i)) ∧
        ∀ q : ℤ, Nonempty
          ((SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
              ((DerivedCategory.homologyFunctor _ q).obj
                (finiteQuotientLayerObject X d M n)) ≅
            (SheafOfModules.overFunctor _ ((toProEt X).obj Z)).obj
              ((finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (n + 1 + 1))
                (φ (n + 1))).obj (Q.homology q))) := by
  refine ⟨finiteQuotientLayerTensorComplex d.ideal n P,
    finiteQuotientLayerTensorComplex_ge d.ideal n P a hPa,
    finiteQuotientLayerTensorComplex_le d.ideal n P b hPb,
    finiteQuotientLayerTensorComplex_finite d n P (fun i ↦ (hP i).2), ?_⟩
  exact finiteQuotient_layer_tensor_homology_comparison X d φ hφ hcompat M b n Z P hPb
    (fun i ↦ (hP i).1) e

end AlgebraicGeometry.Scheme
