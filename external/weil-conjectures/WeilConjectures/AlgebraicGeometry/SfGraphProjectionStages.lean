/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfGraphProjectionData

/-! # The constituent words of the graph projection square

Source: `LowerShriekComposition.lean`, eA/eC/eB, and the explicit constructions in
`EtaleLocallyClosedGraphModel.lean` (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (t : EtaleGraphPresentation f)

/-- The first graph is proper because its composite with a separated projection is
identity. Source: `LowerShriekComposition.lean`, graph Gamma1
(auxiliary; not a blueprint node). -/
theorem sfGraphFirst_proper :
    IsProper (locallyClosedGraphS₁ t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm))) := by
  let s := locallyClosedGraphS₁ t.a t.e t.p c.i c.g
    ((Category.assoc _ _ _).trans (t.fac.trans c.comm))
  have hs : s ≫ pullback.snd (pullback.snd t.p c.g) c.i = 𝟙 X := by
    dsimp only [s, locallyClosedGraphS₁]
    exact pullback.lift_snd _ _ _
  have : IsProper (s ≫ pullback.snd (pullback.snd t.p c.g) c.i) := by
    rw [hs]
    infer_instance
  exact IsProper.of_comp s (pullback.snd (pullback.snd t.p c.g) c.i)

/-- The second graph is proper because its composite with a separated projection is a.
Source: `LowerShriekComposition.lean`, graph h2
(auxiliary; not a blueprint node). -/
theorem sfGraphSecond_proper :
    IsProper (locallyClosedGraphS₂ t.a t.e t.p c.i c.g
      ((Category.assoc _ _ _).trans (t.fac.trans c.comm))) := by
  let s := locallyClosedGraphS₂ t.a t.e t.p c.i c.g
    ((Category.assoc _ _ _).trans (t.fac.trans c.comm))
  have hs : s ≫ pullback.snd (pullback.fst t.p c.g) t.e = t.a := by
    dsimp only [s, locallyClosedGraphS₂]
    exact pullback.lift_snd _ _ _
  have : IsProper (s ≫ pullback.snd (pullback.fst t.p c.g) t.e) := by
    rw [hs]
    infer_instance
  exact IsProper.of_comp s (pullback.snd (pullback.fst t.p c.g) t.e)

/-- The proper/open/proper presentation through the first graph neighborhood.
Source: `LowerShriekComposition.lean`, target of eA
(auxiliary; not a blueprint node). -/
def sfGraphFirstPresentation : EtaleGraphPresentation f where
  U := pullback (pullback.snd t.p c.g) c.i
  P := pullback t.p c.g
  a := locallyClosedGraphS₁ t.a t.e t.p c.i c.g
    ((Category.assoc _ _ _).trans (t.fac.trans c.comm))
  e := pullback.fst (pullback.snd t.p c.g) c.i
  p := pullback.fst t.p c.g ≫ t.p
  properA := sfGraphFirst_proper c t
  fac := by
    simp only [locallyClosedGraphS₁, locallyClosedGraphV,
      pullback.lift_fst_assoc, Category.assoc]
    exact t.fac

/-- The proper/open/proper presentation through the second graph neighborhood.
Source: `LowerShriekComposition.lean`, target of eB
(auxiliary; not a blueprint node). -/
def sfGraphSecondPresentation : EtaleGraphPresentation f where
  U := pullback (pullback.fst t.p c.g) t.e
  P := pullback t.p c.g
  a := locallyClosedGraphS₂ t.a t.e t.p c.i c.g
    ((Category.assoc _ _ _).trans (t.fac.trans c.comm))
  e := pullback.fst (pullback.fst t.p c.g) t.e
  p := pullback.fst t.p c.g ≫ t.p
  properA := sfGraphSecond_proper c t
  fac := by
    simp only [locallyClosedGraphS₂, locallyClosedGraphV,
      pullback.lift_fst_assoc, Category.assoc]
    exact t.fac

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- B1, with precisely the endpoints used by the word projection.
Source: `LowerShriekComposition.lean`, eA (auxiliary; not a blueprint node). -/
def sfGraphFirstSideIso :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      (sfGraphFirstPresentation c t).functor A :=
  locallyClosedGraphSide₁ t.a t.e t.p c.i c.g
    ((Category.assoc _ _ _).trans (t.fac.trans c.comm)) A

/-- B2, with precisely the endpoints used by the word projection.
Source: `LowerShriekComposition.lean`, eB (auxiliary; not a blueprint node). -/
def sfGraphSecondSideIso :
    t.functor A ≅ (sfGraphSecondPresentation c t).functor A :=
  locallyClosedGraphSide₂ t.a t.e t.p c.i c.g
    ((Category.assoc _ _ _).trans (t.fac.trans c.comm)) A

/-- R(p1 p)(B12), including the two functor associators.
Source: `LowerShriekComposition.lean`, eC (auxiliary; not a blueprint node). -/
def sfGraphMiddleIso :
    (sfGraphFirstPresentation c t).functor A ≅
      (sfGraphSecondPresentation c t).functor A :=
  letI := sfGraphFirst_proper c t
  letI := sfGraphSecond_proper c t
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (locallyClosedGraphMiddle t.a t.e t.p c.i c.g
        ((Category.assoc _ _ _).trans (t.fac.trans c.comm)) A) _ ≪≫
    Functor.associator _ _ _

/-- The specified comparison is the composite of its three graph constituents.
Source: the defining graph formula (auxiliary; not a blueprint node). -/
theorem sfGraphPresentationComparison_stages :
    sfGraphPresentationComparison A c t =
      sfGraphFirstSideIso c t A ≪≫ sfGraphMiddleIso c t A ≪≫
        (sfGraphSecondSideIso c t A).symm := by
  apply Iso.ext
  ext M
  simp only [sfGraphPresentationComparison, sfGraphCompactificationComparison,
    sfGraphFirstSideIso, sfGraphMiddleIso, sfGraphSecondSideIso,
    locallyClosedGraphSide₁, locallyClosedGraphSide₂, locallyClosedGraphMiddle,
    Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rfl

end AlgebraicGeometry.Etale
