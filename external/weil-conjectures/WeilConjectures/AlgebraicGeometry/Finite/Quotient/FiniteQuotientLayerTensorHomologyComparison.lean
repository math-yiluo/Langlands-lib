/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorComplex
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorDerivedHomologyComparison
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerTensorModelHomologyIdentification

/-! # The homology comparison for the explicit ideal-layer tensor complex

Source: Stacks Project, sites-cohomology.tex, Tag 094I, the displayed balancing identity,
and Tags 094H and 06YU.
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-homology-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Compute the layer homology from the specified residue projective complex.
This statement concerns the already constructed tensor complex; it does not assert
existence of a finite model or any bound on its homology. Only an upper bound and
projectivity are needed, with no finite-generation or lower-bound hypothesis.

Source: Stacks Project, sites-cohomology.tex, Tag 094I, the displayed balancing identity,
Tag 094H, and the bounded-above flat-complex calculation of derived tensor (06YU).
(blueprint: lem-weil-pbc-finite-quotient-layer-tensor-homology-comparison).

Proof: put L=I^(n+1)/(I I^(n+1)), with its residue-ring action. The standard
ideal-power quotient equivalence identifies L with the kernel of the algebraic
successor-to-previous quotient map. Exact constant realization identifies its
constant sheaf, after the specified successor coefficient isomorphism, with the
kernel of finiteQuotientUnitMap. The transition square in hcompat identifies
the action through the residue ring, and its scalar square identifies that action
with the completed scalar action. Derived tensor associativity therefore writes
the layer, on the slice over Z, as the residue reduction tensored over the residue
coefficient sheaf with the constant sheaf L, retaining the successor-ring action.
Slice restriction is exact and commutes with this tensor calculation. Apply e to
replace the residue reduction by the given constant complex P. A bounded-above
complex of projectives is K-flat; its constant realization is likewise K-flat.
Consequently its derived tensor with L is the ordinary termwise tensor, with
differential 1 tensor d_P. This is exactly finiteQuotientLayerTensorComplex,
including restriction of scalars from the residue ring to the successor ring.
Finally exact constant realization, coefficient transport along the isomorphism
phi, and exact slice restriction commute with homology, giving the displayed
isomorphism in every degree. All constructions respect zero modules, zero ideal
layers, zero coefficient rings, and the empty chart. No basis or finite generation
is used in this comparison. -/
theorem finiteQuotient_layer_tensor_homology_comparison
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
          ((finiteCoefficientConstantFunctor X (A ⧸ d.ideal ^ (n + 1 + 1))
            (φ (n + 1))).obj ((finiteQuotientLayerTensorComplex d.ideal n P).homology q))) := by
  intro q
  obtain ⟨e₁⟩ :=
    finiteQuotient_layer_tensor_derived_homology_comparison X d φ hφ hcompat M b n Z P hPb hP e q
  obtain ⟨e₂⟩ := finiteQuotient_layer_tensor_model_homology_identification X d φ hφ n Z P q
  exact ⟨e₁ ≪≫ e₂⟩

end AlgebraicGeometry.Scheme
