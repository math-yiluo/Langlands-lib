/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientCoefficientLayerData
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientLocalHomologyModels
import WeilConjectures.AlgebraicGeometry.Finite.Quotient.FiniteQuotientLayerLocalComplexCore

/-! # Local algebraic complexes for a coefficient-filtration outer term
Source: Stacks Project, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-local-complexes).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectModelsAbLocallyBijective

set_option linter.unusedVariables false in
/-- The residue complex computes the coefficient layer after ordinary tensor.

Source: Stacks Project, sites-cohomology.tex, Tags 0942, 094H and 094I.
(blueprint: lem-weil-pbc-finite-quotient-layer-local-complexes).

Proof: Put Q=I^(n+1)/I^(n+2), a submodule of the finite ring A/I^(n+2).
Thus Q has a finite underlying set. The ideal I annihilates Q, so Q is a finite
module over A/I. The quotient compatibility squares identify the actual sheaf kernel
with constant Q over the
successor ring. Derived tensor balancing identifies the layer object with the
residue reduction tensored over A/I with Q, followed by scalar restriction. On
each residue-model chart use the given bounded finite-projective complex P.
Its flat terms compute the derived tensor with Q by ordinary tensor. Each term
P^i tensor Q is finite over A/I and hence over the successor ring, and it is zero
outside [a,b]. Regard this as a complex of successor modules. Exact constant
realization and exact scalar and slice restriction identify its algebraic
homology with the slice of the actual layer's homology. Pull back the original
cover along each W -> V to obtain all charts in the stated predicate. On empty
charts and for the zero coefficient ring the same complexes and identifications
apply. This uses only residue models, without any model or homology hypothesis
on the successor reduction. -/
theorem finiteQuotient_layer_local_complexes
    (X : Scheme.{t}) [IsLocallyNoetherian X] [CompactSpace X]
    {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    [∀ n : ℕ, (koszulConstantFunctor X (A ⧸ d.ideal ^ (n + 1))).PreservesZeroMorphisms]
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hφ : ∀ n : ℕ, IsIso (φ n)) (hcompat : FinitePerfectModelsCompatible X d φ)
    (M : DerivedCategory (CompletedAdicModules X d)) (V : X.Etale)
    (a b : ℤ) (hab : a ≤ b) (n : ℕ)
    (hresidue : FinitePerfectModelsOn X d φ M 0 V a b) :
    FiniteCoefficientLocalHomologyModels X (A ⧸ d.ideal ^ (n + 1 + 1))
      (φ (n + 1)) (finiteQuotientLayerObject X d M n) V a b := by
  classical
  obtain ⟨T, hT, hlocal⟩ := hresidue
  intro W g
  refine ⟨T.pullback g, X.smallEtaleTopology.pullback_stable g hT, ?_⟩
  intro Z f hf
  obtain ⟨P, hPa, hPb, hP, ⟨e⟩⟩ := hlocal Z (f ≫ g) hf
  obtain ⟨Q, hQa, hQb, hQfin, hQiso⟩ :=
    finiteQuotient_layer_local_complex_core X d φ hφ hcompat M a b n Z P
      hPa hPb hP ⟨e⟩
  refine ⟨Q, ?_, hQfin, hQiso⟩
  intro q hq
  rcases hq with hq | hq
  · exact (Q.isStrictlyGE_iff a).1 hQa q hq
  · exact (Q.isStrictlyLE_iff b).1 hQb q hq

end AlgebraicGeometry.Scheme
