/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.KrullDimension
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimension

/-!
# Affine torsion cohomological dimension bound

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
`lemma-uniform-bounds-pro-etale-affines`, affine part of the proof of
`lemma-uniform-bounds-pro-etale-affines` (blueprint: lemma-uniform-bounds-pro-etale-affines).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The affine finite-type step in the torsion cohomological-dimension bound.

Source: the affine bound `lemma-uniform-bounds-pro-etale-affines` in the blueprint subsection
`sec-smooth-purity/sk-prop-sf-cbc`, with its proof by induction on dimension; also
Stacks Project, Tag 0F0V (https://stacks.math.columbia.edu/tag/0F0V).

Proof: the cited affine theorem gives torsion cohomological dimension at most
`dim X + c` for a nonempty affine finite-type scheme. Its finite-type hypothesis
is exactly local finite type together with quasi-compactness of the structure
morphism. Noether normalization makes the Krull dimension finite. The bound
`hX` makes that dimension at most `d`, so `q > d + c` implies `q > dim X + c`
and the cited theorem gives the required vanishing. If X is empty, every object
of its small etale site is empty, the empty covering forces every abelian sheaf
to have zero sections, and hence its section functor and all its derived
functors vanish. Thus this case also satisfies the displayed bound. Torsion here
means locally torsion sections, as in the cited theorem, without a uniform
annihilator. The upstream source declaration
`hasTorsionCohomologicalDimensionLE_of_isAffine` already provides this affine bound,
and the present theorem exposes the same result in the `Sheaf.H` formulation used by
the surrounding modules.
(blueprint: new-thm-sc-affine-torsion-cd-bound)
-/
theorem subsingleton_H_of_two_mul_add_lt_of_isAffine {K : Type u} [Field K] (c d : ℕ)
    (hK : ∀ F : Sheaf (Spec (.of K)).smallEtaleTopology AddCommGrpCat.{u + 1}, F.IsTorsion →
      ∀ q : ℕ, c < q → Subsingleton (Sheaf.H F q))
    {X : Scheme.{u}} (a : X ⟶ Spec (.of K)) [LocallyOfFiniteType a] [QuasiCompact a]
    [IsAffine X] (hX : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion) (q : ℕ)
    (hq : d + c < q) : Subsingleton (Sheaf.H F q) := by
  exact hasTorsionCohomologicalDimensionLE_of_isAffine hK a hX F hF q hq

end AlgebraicGeometry.Scheme
