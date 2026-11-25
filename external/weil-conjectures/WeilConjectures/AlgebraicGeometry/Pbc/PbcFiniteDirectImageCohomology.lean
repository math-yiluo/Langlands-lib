/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedTowerDirectImageSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
import all WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import all WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import all Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.Topology.KrullDimension
import all Mathlib.GroupTheory.Torsion
import all Mathlib.RingTheory.Ideal.Quotient.Operations
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.RestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Perfect
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Proper finite-coefficient direct image on intrinsic cohomology

## References

* Stacks Tags 095U, 0GL0 and 09AL
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

open ProEtale

private def reductionEncoding (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) :=
  pbcRestrict (pbcLevelConstantComparison T d n).hom ⋙
    CoefficientSerre.proEtaleModuleRestriction T (A ⧸ d.ideal ^ (n + 1))

private instance encoding_additive (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (n : ℕ) : (reductionEncoding T d n).Additive := by
  dsimp [reductionEncoding]
  infer_instance

end AlgebraicGeometry.Scheme
