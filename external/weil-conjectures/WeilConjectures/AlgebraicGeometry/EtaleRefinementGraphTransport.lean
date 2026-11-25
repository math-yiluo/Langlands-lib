/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation

/-! # The proper graph and its two neighborhood transports

Source: Stacks Project, Tags 0F7C--0F7E, the two projection grids in
`lem-pur-etale-graph-refinement-normalization`, steps 2--3.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.EtaleRefinementGraph

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (s r : Compactification f)
  (rs : r.Refinement s)

/-- The equality used by the fixed product graph.
Source: the supplied compactification equations
(auxiliary; not a blueprint node). -/
theorem equation : ((𝟙 X) ≫ r.i) ≫ r.g = s.i ≫ s.g := by
  simp only [Category.id_comp, ← r.comm, ← s.comm]

/-- The proper graph `(1,rs.hom)` in the product of the two ambient schemes.
Source: Stacks Tags 0F7C--0F7E, refinement projection grids
(auxiliary; not a blueprint node). -/
def z : r.Z ⟶ pullback r.g s.g :=
  pullback.lift (𝟙 r.Z) rs.hom (by simpa using rs.hom_g.symm)

/-- The proper ambient structural map of the fixed graph.
Source: the product graph formula, Stacks Tag 0F7B
(auxiliary; not a blueprint node). -/
abbrev p : pullback r.g s.g ⟶ Y := pullback.fst r.g s.g ≫ r.g

/-- The first supporting open, pulled back from `s`.
Source: the product graph formula, Stacks Tag 0F7B
(auxiliary; not a blueprint node). -/
abbrev b₁ := pullback.fst (pullback.snd r.g s.g) s.i

/-- The second supporting open, pulled back from `r`.
Source: the product graph formula, Stacks Tag 0F7B
(auxiliary; not a blueprint node). -/
abbrev b₂ := pullback.fst (pullback.fst r.g s.g) r.i

/-- The first graph lift.
Source: the explicit graph formula, Stacks Tag 0F7B
(auxiliary; not a blueprint node). -/
abbrev s₁ := locallyClosedGraphS₁ (𝟙 X) r.i r.g s.i s.g (equation s r)

/-- The second graph lift.
Source: the explicit graph formula, Stacks Tag 0F7B
(auxiliary; not a blueprint node). -/
abbrev s₂ := locallyClosedGraphS₂ (𝟙 X) r.i r.g s.i s.g (equation s r)

/-- Properness follows by composing with the separated first projection to obtain `1`.
Source: Stacks Tag 01W6 (auxiliary; not a blueprint node). -/
instance z_proper : IsProper (z s r rs) := by
  have : IsProper (z s r rs ≫ pullback.fst r.g s.g) := by
    simpa only [z, pullback.lift_fst] using (inferInstance : IsProper (𝟙 r.Z))
  exact IsProper.of_comp _ (pullback.fst r.g s.g)

/-- Properness of the first neighborhood graph.
Source: Stacks Tag 01W6 (auxiliary; not a blueprint node). -/
instance s₁_proper : IsProper (s₁ s r) := by
  have : IsProper (s₁ s r ≫ pullback.snd (pullback.snd r.g s.g) s.i) := by
    simpa only [s₁, locallyClosedGraphS₁, pullback.lift_snd] using
      (inferInstance : IsProper (𝟙 X))
  exact IsProper.of_comp _ (pullback.snd (pullback.snd r.g s.g) s.i)

/-- Properness of the second neighborhood graph.
Source: Stacks Tag 01W6 (auxiliary; not a blueprint node). -/
instance s₂_proper : IsProper (s₂ s r) := by
  have : IsProper (s₂ s r ≫ pullback.snd (pullback.fst r.g s.g) r.i) := by
    simpa only [s₂, locallyClosedGraphS₂, pullback.lift_snd] using
      (inferInstance : IsProper (𝟙 X))
  exact IsProper.of_comp _ (pullback.snd (pullback.fst r.g s.g) r.i)

/-- Both neighborhood graphs lie over the same map `r.i;z`.
Source: the two pullback projection equations
(auxiliary; not a blueprint node). -/
theorem graph_fac :
    locallyClosedGraphV (𝟙 X) r.i r.g s.i s.g (equation s r) = r.i ≫ z s r rs := by
  apply pullback.hom_ext
  · simp [locallyClosedGraphV, z]
  · simp [locallyClosedGraphV, z, rs.i_hom]

/-- The first neighborhood pulls back along `z` to the supplied open `r.i`.
Source: pullback cancellation and the supplied Cartesian refinement square
(auxiliary; not a blueprint node). -/
theorem square₁ (hs : IsPullback r.i (𝟙 X) rs.hom s.i) :
    IsPullback (s₁ s r) r.i (b₁ s r) (z s r rs) := by
  have outer : IsPullback r.i
      (s₁ s r ≫ pullback.snd (pullback.snd r.g s.g) s.i)
      (z s r rs ≫ pullback.snd r.g s.g) s.i := by
    simpa only [s₁, locallyClosedGraphS₁, z, pullback.lift_snd] using hs
  exact (outer.of_bot (by
    simp only [s₁, locallyClosedGraphS₁, pullback.lift_fst]
    exact (graph_fac s r rs).symm)
    (IsPullback.of_hasPullback (pullback.snd r.g s.g) s.i)).flip

/-- The second neighborhood pulls back along `z` to `r.i`, since `pr₁ z = 1`.
Source: pullback cancellation and the identity square
(auxiliary; not a blueprint node). -/
theorem square₂ : IsPullback (s₂ s r) r.i (b₂ s r) (z s r rs) := by
  have outer : IsPullback r.i
      (s₂ s r ≫ pullback.snd (pullback.fst r.g s.g) r.i)
      (z s r rs ≫ pullback.fst r.g s.g) r.i := by
    simpa only [s₂, locallyClosedGraphS₂, z, pullback.lift_snd, pullback.lift_fst] using
      IsPullback.id_vert r.i
  exact (outer.of_bot (by
    simp only [s₂, locallyClosedGraphS₂, pullback.lift_fst]
    exact (graph_fac s r rs).symm)
    (IsPullback.of_hasPullback (pullback.fst r.g s.g) r.i)).flip

/-- The graph followed by the structural map is the refined proper factor.
Source: the first product projection identity
(auxiliary; not a blueprint node). -/
theorem z_p : z s r rs ≫ p s r = r.g := by
  dsimp only [z, p]
  rw [← Category.assoc, pullback.lift_fst]
  exact Category.id_comp r.g

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The middle word of the fixed graph, including its exterior proper direct image.
Source: the explicit intersection formula in `EtaleLocallyClosedGraphModel`
(auxiliary; not a blueprint node). -/
def middle :
    R((s₁ s r)_*[ModuleCat.{u + 1} A]) ⋙
        D((b₁ s r)_!open[ModuleCat.{u + 1} A]) ⋙ R((p s r)_*[ModuleCat.{u + 1} A]) ≅
      R((s₂ s r)_*[ModuleCat.{u + 1} A]) ⋙
        D((b₂ s r)_!open[ModuleCat.{u + 1} A]) ⋙ R((p s r)_*[ModuleCat.{u + 1} A]) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (locallyClosedGraphMiddle (𝟙 X) r.i r.g s.i s.g (equation s r) A) _ ≪≫
    Functor.associator _ _ _

/-- Transport the first graph neighborhood along the proper graph, including exterior image.
Source: Cartesian proper/open interchange, Stacks Tags 0F7B--0F7C
(auxiliary; not a blueprint node). -/
def transport₁ (hs : IsPullback r.i (𝟙 X) rs.hom s.i) :
    R((s₁ s r)_*[ModuleCat.{u + 1} A]) ⋙
        D((b₁ s r)_!open[ModuleCat.{u + 1} A]) ⋙ R((p s r)_*[ModuleCat.{u + 1} A]) ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) r :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
      (square₁ s r rs hs)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
      (z s r rs) (p s r) r.g (z_p s r rs))

/-- Transport the second graph neighborhood along the same proper graph.
Source: Cartesian proper/open interchange, Stacks Tags 0F7B--0F7C
(auxiliary; not a blueprint node). -/
def transport₂ :
    R((s₂ s r)_*[ModuleCat.{u + 1} A]) ⋙
        D((b₂ s r)_!open[ModuleCat.{u + 1} A]) ⋙ R((p s r)_*[ModuleCat.{u + 1} A]) ≅
      rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) r :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openImmersionLowerShriekLowerStarExchangeIso A
      (square₂ s r rs)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (rightDerivedLowerStarCompOfEq (ModuleCat.{u + 1} A)
      (z s r rs) (p s r) r.g (z_p s r rs))

end AlgebraicGeometry.Etale.EtaleRefinementGraph
