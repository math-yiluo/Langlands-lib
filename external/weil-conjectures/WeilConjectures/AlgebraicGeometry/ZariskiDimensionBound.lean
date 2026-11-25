/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Algebra.Category.Grp.AB

import WeilConjectures.Topology.NoetherianTopologicalCohomologyVanishing

/-!
# The Zariski dimension bound

Source: the Weil conjectures blueprint, `chap-Smooth-purity`, unit `sk-prop-sf-cbc`,
lemma `lemma-uniform-bounds-pro-etale-affines` (blueprint: lemma-uniform-bounds-pro-etale-affines);
Stacks Project, Cohomology, Proposition 02UZ.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- The Zariski cohomology of every abelian sheaf on a Noetherian scheme vanishes above
any nonnegative upper bound for its topological Krull dimension.
Source: Stacks Project, Cohomology, Proposition 02UZ and the blueprint lemma of the same name
(blueprint: lemma-uniform-bounds-pro-etale-affines).

Proof: forget the scheme structure. The underlying space is Noetherian by
`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`, and its dimension is at most `d`
by hypothesis (`def-kun-topological-krull-dimension`). The small Zariski site is the site
of open subsets with jointly surjective open coverings (`lemma-uniform-bounds-pro-etale-affines`).
Thus `F` is an abelian sheaf on that space, and its topological cohomology
(`def-sc-topological-abelian-cohomology`) is precisely its Zariski cohomology
(`lemma-uniform-bounds-pro-etale-affines`). Apply
`lem-sc-noetherian-topological-cohomology-vanishing` to obtain vanishing for every `q > d`.
-/
theorem isZero_zariskiCohomology_of_dimension_bound
    (X : Scheme.{u}) [CompactSpace X] [IsLocallyNoetherian X]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (q : ℕ) (hq : d < q) : IsZero (Sheaf.H' F q (⊤ : X.Opens)) := by
  let : IsNoetherian X := IsNoetherian.mk
  exact TopCat.isZero_noetherian_topological_cohomology_of_dimension_bound
    X d hdim F q hq

end AlgebraicGeometry
