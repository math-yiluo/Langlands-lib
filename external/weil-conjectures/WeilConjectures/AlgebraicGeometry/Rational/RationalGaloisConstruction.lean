/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralGaloisConstruction
import all WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Rational reconstruction from integral Galois modules

## References

* Weil II (1.1.1), (1.1.6)
* Stanford Weil II seminar L19, Proposition 1.1.9
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

variable {Y : Scheme.{u}} [ConnectedSpace Y]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
  [IsFundamentalGroup (FiniteEtale.fiber y) G]
  (c : GaloisLisseFiniteCorrespondence y G)
  (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P)
  (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
  (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

end AlgebraicGeometry.Scheme
