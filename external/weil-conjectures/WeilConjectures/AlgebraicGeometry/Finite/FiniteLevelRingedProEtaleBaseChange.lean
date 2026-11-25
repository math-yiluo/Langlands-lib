/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumCompletedSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.WeilSheaf.ProfiniteCoefficientInverseImageSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived

/-!
# Finite proper base change with canonical ring-sheaf coefficients

Source: blueprint theorem 1325; Stacks Project, Pro-etale Cohomology, Section 09C8,
and the finite etale-origin step of Theorem 09C9
(blueprint: proposition-proper-direct-image-constructible-complexes--5).
This is the recorded finite theorem in the normalized ring-sheaf presentation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (Λ : Type (t + 1)) [CommRing Λ] [Finite Λ]
  [TopologicalSpace Λ] [DiscreteTopology Λ]

variable {X' X Y' Y : Scheme.{t}}
  {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

end AlgebraicGeometry.Scheme
