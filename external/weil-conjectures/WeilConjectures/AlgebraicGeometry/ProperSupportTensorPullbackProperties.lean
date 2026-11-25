/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.FiniteTypeModuleSupportPullback
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.RelativelyFlatModulePullback
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Base change of finitely presented relatively flat modules with proper support

Source: Stacks Project, Tag 0A1H, affine reduction; Tags 01AT and 0CYM.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Ordinary tensor pullback preserves the three termwise hypotheses of Tag 0A1H.
Source: Stacks Project, Tag 0A1H, affine reduction; Tags 01AT and 0CYM.
Proof: pull back each local finite presentation to obtain a finite presentation of
its tensor pullback. At a point of the cartesian square, the stalk of this pullback
is tensor extension of the original module stalk. Relative flatness is preserved
by base change of modules and subsequent localization, giving flatness over the
new base stalk. Since the original stalk module is finite, Nakayama's lemma shows
that it is nonzero exactly when its tensor extension along the local ring map is
nonzero. Consequently the support is the inverse image of the original closed
support. Its reduced induced scheme is the reduction of the scheme-theoretic base
change of the original reduced support. Reduction is a closed immersion; compose
it with the proper base change of the original support morphism. This proves
properness for precisely the closed support required by HasSupportProperOver.
Empty supports and zero modules are included, and the base change need not be flat.
(blueprint: lem-pc-proper-support-tensor-pullback-properties). -/
theorem properSupport_tensorPullback_properties
    {X S T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (p : T ⟶ S)
    (F : X.Modules) [F.IsFinitePresentation]
    (hflat : F.IsFlatOver f) (hproper : Scheme.Modules.HasSupportProperOver f F) :
    (Scheme.Modules.tensorPullbackObj (pullback.fst f p) F).IsFinitePresentation ∧
      (Scheme.Modules.tensorPullbackObj (pullback.fst f p) F).IsFlatOver
        (pullback.snd f p) ∧
      Scheme.Modules.HasSupportProperOver (pullback.snd f p)
        (Scheme.Modules.tensorPullbackObj (pullback.fst f p) F)  := by
  classical
  let q := pullback.fst f p
  let f' := pullback.snd f p
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction q
  let e := adj.leftAdjointUniq (Scheme.Modules.pullbackPushforwardAdjunction q)
  have hfp : (Scheme.Modules.tensorPullbackObj q F).IsFinitePresentation :=
    Scheme.Modules.isFinitePresentation_of_iso ((e.app F).symm)
  refine ⟨hfp, relativelyFlat_module_pullback f p F hflat, ?_⟩
  obtain ⟨Z, hZ, hp⟩ := hproper
  let i := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  have hi : Set.range i = (Z : Set X) := by simp [i]
  have : IsProper (i ≫ f) := hp
  let C : TopologicalSpace.Closeds (pullback f p : Scheme.{u}) :=
    ⟨q ⁻¹' (Z : Set X), Z.isClosed.preimage q.continuous⟩
  have hsupp := (Scheme.Modules.finiteType_module_support_pullback F).2.2
    (pullback f p) q
  refine ⟨C, ?_, ?_⟩
  · change q ⁻¹' (Z : Set X) = _
    exact (congrArg (fun D : Set X ↦ q ⁻¹' D) hZ).trans hsupp.2.symm
  · apply (Scheme.closed_subset_proper_over_base_properties f' C).1.mpr
    have hsq := (IsPullback.of_hasPullback i q).paste_vert
      (IsPullback.of_hasPullback f p)
    have hproper' : IsProper (pullback.snd i q ≫ f') :=
      MorphismProperty.of_isPullback hsq inferInstance
    refine ⟨pullback i q, pullback.snd i q, inferInstance, ?_, hproper'⟩
    change Set.range (pullback.snd i q) = q ⁻¹' (Z : Set X)
    rw [Scheme.Pullback.range_snd, hi]

end AlgebraicGeometry
