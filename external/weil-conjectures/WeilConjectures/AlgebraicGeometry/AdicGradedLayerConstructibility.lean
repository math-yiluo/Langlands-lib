/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientFiltration
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
import WeilConjectures.AlgebraicGeometry.AdicGradedResidueTensorComparison
import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleConstructibleIso
import WeilConjectures.AlgebraicGeometry.CoefficientSurjectiveRestrictionConstructible

/-! # Constructible cohomology of the graded coefficient layer
Source: Stacks Project, Tags 09BR and 094H.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

/-- Only the graded layer, rather than a higher reduction, has constructible cohomology.

Source: Stacks Project, proetale.tex, Tag 09BR, second displayed isomorphism and tensor
step; sites-cohomology.tex, Tag 094H, lemma-locally-constant-tensor-product.
(auxiliary; not a blueprint node).

Proof: The kernel of A/J^(n+2) -> A/J^(n+1) is J^(n+1)/J^(n+2). Multiplication
by J annihilates this kernel. Noetherianity makes it finite over A, hence finite and
finitely presented over A/J. Associativity of K-flat scalar extension and tensor
identifies the displayed layer with the residue reduction tensor over A/J with
this constant finite module, followed by restriction to A/J^(n+2). On each affine
open refine the finitely many residue cohomology stratifications to one finite
stratification, retaining the actual projection maps. Exact stratum restriction
commutes with cohomology and derived tensor. The residue complex is bounded above
on each stratum, and its cohomology is locally constant finite type there; the
constant graded module is concentrated in degree zero. Apply Tag 094H to obtain
locally constant finite type tensor cohomology in every degree. Restriction of
scalars along A/J^(n+2) -> A/J retains those constant models. Their generators remain
finite and finite modules over the Noetherian larger quotient are finitely presented.
This gives the required affine-local strata and trivializations. There is no lower
cohomology bound: the graded module need not be flat. For J=0 or J=top the layer is
zero; the same construction covers the zero ring and the empty scheme. -/
theorem adicFiniteGradedLayer_constructible (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (N : adicFiniteAmbient.{u, v} X A)
    (hres : ProEtale.coefficientBoundedConstructibleProEtale.{u, v} X
      (adicFiniteCoeff J 0) (adicFiniteReduction.{u, v} X J N 0))
    (n : ℕ) (q : ℤ) :
    IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf.{u, v} X
      (adicFiniteCoeff J (n + 1))
      ((coefficientModelCohomology _ q).obj (adicFiniteGradedLayer.{u, v} X J N n)) := by
  let M := adicFiniteResidueGradedModule J n
  have hM : Module.Finite (adicFiniteCoeff J 0) M :=
    adicFiniteResidueGradedModule_finite J n
  have htensor := coefficientConstructible_constantTensor X (adicFiniteCoeff J 0)
    (adicFiniteReduction.{u, v} X J N 0) hres M hM q
  have hrestrict := coefficientSurjectiveRestriction_constructible X
    (adicFiniteCoeff J (n + 1)) (adicFiniteCoeff J 0)
    (adicFiniteFactor J (Nat.zero_le (n + 1)))
    (Ideal.Quotient.factor_surjective
      (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.zero_le (n + 1)) 1)))
    (coefficientConstantTensor.{u, v} X (adicFiniteCoeff J 0)
      (adicFiniteReduction.{u, v} X J N 0) M) q htensor
  obtain ⟨e⟩ := adicFiniteGradedLayer_residueTensor X J N n
  exact ProEtale.coefficientProEtale_constructible_of_iso X
    (adicFiniteCoeff J (n + 1)) ((coefficientModelCohomology _ q).mapIso e).symm hrestrict

end AlgebraicGeometry.Scheme
