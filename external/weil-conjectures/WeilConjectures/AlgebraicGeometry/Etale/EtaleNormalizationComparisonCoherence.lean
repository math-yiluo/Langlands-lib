/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.QuasiFinite.QuasiFiniteCompactSupportExact
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeModules

public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Support.EtaleSupportMapCompatibility
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.LowerShriek.BaseChange

import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange

set_option linter.privateModule false

/-! # Refinement and open coherence of normalized etale tensor families

Source: blueprint sec-six-functors-basics/sk-prop-cohsm,
lem-pur-co-smooth-etale-locality.proof.md, Step 1; Stacks Tags 03S6 and 0GKF
(blueprint: lem-pur-etale-normalization-comparison-coherence).

All arrows below are built from the specified graph comparison, proper/open compositor,
exact inverse-image compositor, and adjunction conjugacy. Right adjoints are arbitrary
chosen right adjoints equipped with their adjunctions.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- Transporting the right adjoint and then using uniqueness gives the inverse mate.
Expand the inverse-mate component formula and the transported adjunction's unit. -/
private theorem uniq_eq_conjugate
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (i : R₁ ≅ R₂) :
    ((a.ofNatIsoRight i).leftAdjointUniq b).inv =
      (conjugateEquiv a b).symm i.hom := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateIsoEquiv, conjugateEquiv_symm_apply_app]

end AlgebraicGeometry.Etale
