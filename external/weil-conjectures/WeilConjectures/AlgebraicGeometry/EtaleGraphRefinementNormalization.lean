/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphSideTransport

/-! # Normalization of a graph map along one Cartesian proper refinement

Source: Stacks Project, Tags 0F7C--0F7E and the unit--open-base-change formula in
`LowerShriekIndependenceUnbounded.lean`.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The graph map from a compactification to its Cartesian proper refinement is the
specified refinement map, followed by restoration of the initial identity direct image.
Source: Stacks Tags 0F7C--0F7E; `LowerShriekIndependenceUnbounded.lean`, refinement map
(auxiliary; not a blueprint node).

Proof:
1. Construct z=(1,rs.hom):r.Z -> r.Z ×_Y s.Z. Its two supporting-open
   neighborhoods pull back to r.i, giving the specified transports tau₁ and tau₂.
2. Vertical exchange pasting on their intersection gives middle; tau₂ = tau₁.
   This is `etaleRefinementGraphMiddleTransport`.
3. Horizontal exchange pasting with the two product projections, and associativity
   of the normalized proper compositor, give side₁; tau₁ = rho(rs) and
   side₂; tau₂ = openNormalization(r). The second identity is the identity-refinement
   case of the same calculation. The existing unbounded comparison theorem identifies
   the first exchange with the specified unit--inverse-base-change refinement map.
   These are `etaleRefinementGraphSideTransport`.
4. Expand the graph comparison as side₁; middle; side₂ inverse, substitute the middle
   identity, and cancel tau₂ against its inverse. Substituting the two boundary
   identities gives exactly the equation below, with no quasi-compactness assumption. -/
theorem etaleGraphFromOpen_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (s r : Compactification f)
    (rs : r.Refinement s) (hs : IsPullback r.i (𝟙 X) rs.hom s.i) :
    etaleGraphComparisonFromOpen A s (EtaleGraphPresentation.ofCompactification r) =
      asIso (rightDerivedLowerShriekOfCompactificationComparison
        (ModuleCat.{u + 1} A) rs hs) ≪≫ (etaleGraphOpenNormalization A r).symm := by
  obtain ⟨h₁, h₂⟩ := etaleRefinementGraphSideTransport A s r rs hs
  have hm := etaleRefinementGraphMiddleTransport A s r rs hs
  let b₁ := locallyClosedGraphSide₁ (𝟙 X) r.i r.g s.i s.g
    (EtaleRefinementGraph.equation s r) A
  let b₂ := locallyClosedGraphSide₂ (𝟙 X) r.i r.g s.i s.g
    (EtaleRefinementGraph.equation s r) A
  calc
    _ = b₁ ≪≫ EtaleRefinementGraph.middle s r A ≪≫ b₂.symm := by
      change locallyClosedGraphIso (𝟙 X) r.i r.g s.i s.g
        (EtaleRefinementGraph.equation s r) A = _
      simp only [locallyClosedGraphIso, EtaleRefinementGraph.middle,
        b₁, b₂, EtaleRefinementGraph.s₁, EtaleRefinementGraph.s₂,
        EtaleRefinementGraph.b₁, EtaleRefinementGraph.b₂, EtaleRefinementGraph.p,
        Iso.trans_assoc]
    _ = (b₁ ≪≫ EtaleRefinementGraph.transport₁ s r rs A hs) ≪≫
        (b₂ ≪≫ EtaleRefinementGraph.transport₂ s r rs A).symm := by
      rw [← hm]
      simp only [Iso.trans_symm, Iso.trans_assoc, Iso.self_symm_id_assoc]
    _ = _ := by rw [h₁, h₂]

end AlgebraicGeometry.Etale
