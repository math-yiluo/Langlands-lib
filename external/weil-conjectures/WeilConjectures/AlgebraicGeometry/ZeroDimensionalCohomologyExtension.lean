/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ZeroDimensionalCohomology


public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.Topology.KrullDimension
import Mathlib.AlgebraicGeometry.Artinian
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyRest

/-! # Étale cohomology in dimension zero

Source: literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-arbitrary-curve-cd/
lem-weil-pbc-zero-dimensional-cohomology.md
(blueprint: lemma-sheaves-finite-support-finite-morphisms--1).
-/

@[expose] public section


universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- The underlying point type of a separated finite-type zero-dimensional scheme
over an algebraically closed field is finite.

Source: literature/blueprint/master/blueprint/sec-curve-estimates/lem-sc-arbitrary-curve-cd/
lem-weil-pbc-zero-dimensional-cohomology.md, finiteness clause;
Stacks Project, Tag 00KH (blueprint: zero-dimensional-etale-finite).

Proof: By LocallyOfFiniteType.isLocallyNoetherian f, C is locally Noetherian. By
QuasiCompact.compactSpace_of_compactSpace f, C is compact.
IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim makes C locally Artinian and hence discrete.
Therefore finite_of_compact_of_discrete proves Finite C (node lem-weil-pbc-finite-type-dim-zero-
artinian).
-/
theorem zero_dimensional_etale_finite
    (k : Type u) [Field k] [IsAlgClosed k] (C : Scheme.{u})
    (f : C ⟶ Spec (.of k)) [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (hdim : topologicalKrullDim C ≤ 0) : Finite C := by
  have : IsLocallyNoetherian C := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : IsLocallyArtinian C := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  exact finite_of_compact_of_discrete



end AlgebraicGeometry
