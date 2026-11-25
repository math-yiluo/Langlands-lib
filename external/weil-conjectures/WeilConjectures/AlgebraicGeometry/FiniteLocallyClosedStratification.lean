/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!
# Finite locally closed stratifications

Source: Stacks Project, Tag 09XZ, with finiteness added
(blueprint: definition-constructible-sheaves--2).

The upstream `Topology.Stratification` now requires constructible strata. These interfaces
state the recorded DAG notion without that additional condition.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Topology

/-- A finite partition into locally closed subsets; constructibility is not required.
Source: Stacks Project, Tag 09XZ, with finiteness added
(blueprint: definition-constructible-sheaves--2). -/
structure FiniteLocallyClosedStratification (X : Type u) [TopologicalSpace X] where
  /-- Number of strata. -/
  n : ℕ
  /-- The subsets in the partition. -/
  stratum : Fin n → Set X
  /-- Every stratum is locally closed. -/
  isLocallyClosed_stratum : ∀ i, IsLocallyClosed (stratum i)
  /-- The strata cover the space. -/
  iUnion_stratum_eq_univ : ⋃ i, stratum i = Set.univ
  /-- Distinct strata are disjoint. -/
  pairwise_disjoint_stratum : Pairwise (Function.onFun Disjoint stratum)

end Topology

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A finite locally closed partition with scheme immersions realizing its strata.
Source: Stacks Project, Tag 09XZ, with finiteness and scheme realizations added
(blueprint: definition-constructible-sheaves--2). -/
structure FiniteLocallyClosedStratification (X : Scheme.{u}) extends
    Topology.FiniteLocallyClosedStratification X where
  /-- A scheme realizing each stratum. -/
  domain : Fin n → Scheme.{u}
  /-- Its map to the original scheme. -/
  immersion : ∀ i : Fin n, domain i ⟶ X
  /-- Each map is an immersion. -/
  isImmersion : ∀ i : Fin n, IsImmersion (immersion i)
  /-- The image is the designated stratum. -/
  range_immersion : ∀ i, Set.range (immersion i) = stratum i

end AlgebraicGeometry.Scheme
