/-
Ported from `P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the `p2m_open` commands are
replaced by `open`; the `p2m_export` commands are replaced by `export`. The paired Markdown
file lists the changes.
-/
import Mathlib
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
namespace P2MW.S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective

set_option autoImplicit false

universe u

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MorphismProperty _root_.AlgebraicGeometry

namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Surjective Spec Scheme GeometricallyConnected geometrically)
namespace GeometricallyConnectedDescentAux
open _root_.AlgebraicGeometry

theorem geometricallyConnected_of_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S) [Surjective σ]
    [hgc : GeometricallyConnected (pullback.snd f σ)] : GeometricallyConnected f := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩

  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) := ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' := ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by simp only [kL, l', Category.assoc, pullback.condition]
  haveI : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩

  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l') (by simpa only [Category.assoc] using s.w)
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd _ _ _
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by rw [hm₁]; exact s
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have hc : ConnectedSpace ↥(pullback b kL) := hgc.geometrically_connectedSpace l' m (pullback.snd b kL) sq

  exact (pullback.fst b kL).surjective.connectedSpace (pullback.fst b kL).continuous

end AlgebraicGeometry.GeometricallyConnectedDescentAux

theorem solution :
    DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective := by
  refine DescendsAlong.mk' fun {X Y Z} {f} {g} _ hf hfst => ?_
  haveI : Surjective f := hf
  haveI : GeometricallyConnected (pullback.fst f g) := hfst
  haveI : GeometricallyConnected (pullback.snd g f) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyConnected _ _).mpr hfst
  exact AlgebraicGeometry.GeometricallyConnectedDescentAux.geometricallyConnected_of_pullback_snd g f
