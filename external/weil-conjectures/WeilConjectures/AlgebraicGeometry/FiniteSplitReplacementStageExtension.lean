/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementStage
public import WeilConjectures.AlgebraicGeometry.EtaleHypercover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementGeometry
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementRelativeCover
import WeilConjectures.AlgebraicGeometry.FiniteSplitReplacementBoundaryAttachment

/-! The finite successor step in the split replacement construction. -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.FiniteSplitEtaleHypercover

/-- Source: Stacks Project, Hypercoverings, 0DAV and 01GJ, with finite choices as in 094K.

Form the matching scheme of the finite split skeleton `A`. Its terms are finite sums
of qcqs étale schemes, so finite limits are qcqs. The map of truncated simplicial
objects induces a map to the matching scheme of `K`. Pull back the covering matching
map of `K` along this map. Finitely many affine opens in this relative cover cover
the matching scheme: étale images are open and its underlying space is compact.
Each chosen affine scheme is qcqs, and its étale structure map to the qcqs base is
quasi-compact, quasi-separated and locally of finite presentation. Take their finite
disjoint union as the new nondegenerate summand. Adjoin the copies of old summands
indexed by proper surjections, and use the epi--mono factorization to define the
operators. Face compatibility is precisely the relative matching equation. Uniqueness
of image factorization proves all composition laws. The new summand covers the whole
matching scheme, proving the covering condition. The old data, including the map to K,
are retained literally, giving the displayed equality after restriction.
This statement is finite: it attaches only degree n+1 to a given finite skeleton.
(auxiliary; not a blueprint node) -/
theorem exists_replacement_stage_extension
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (K : SimplicialObject X.Etale) (hK : IsEtaleHypercover K)
    (n : ℕ) (A : FiniteSplitReplacementStage K n) :
    ∃ B : FiniteSplitReplacementStage K (n + 1), B.restrict n (Nat.le_succ n) = A := by
  obtain ⟨Q⟩ := exists_replacement_boundary A.U
  obtain ⟨N, b, g, hc, hf, hcomp⟩ := exists_finite_relative_boundary_cover K hK A Q
  exact exists_replacement_stage_of_boundary_cover K A Q N b g hc hf hcomp

end AlgebraicGeometry.FiniteSplitEtaleHypercover
