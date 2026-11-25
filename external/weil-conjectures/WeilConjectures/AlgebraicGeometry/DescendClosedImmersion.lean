/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LimitAffineTransition
public import Mathlib.CategoryTheory.Comma.Over.Pullback
import WeilConjectures.AlgebraicGeometry.DescendFinite
import WeilConjectures.AlgebraicGeometry.DescendMonomorphism

/-!
# Descent of closed immersions to a stage of an inverse limit

Source: Stacks Project, Limits, Tag 01ZP, in Situation 081D
(blueprint: lem-weil-pbc-descend-closed-immersion).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem property_overPullback_comp
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {S T U : Scheme.{u}} (a : U ⟶ T) (b : T ⟶ S)
    {X Y : Over S} (f : X ⟶ Y)
    (h : P ((Over.pullback b).map f).left) :
    P ((Over.pullback (a ≫ b)).map f).left := by
  have h' := P.overPullbackMap a ((Over.pullback b).map f) h
  let e := Over.pullbackComp a b
  let eX := (Over.forget U).mapIso (e.app X)
  let eY := (Over.forget U).mapIso (e.app Y)
  apply (P.arrow_mk_iso_iff (Arrow.isoMk eX eY ?_)).mpr h'
  exact (congrArg Over.Hom.left (e.hom.naturality f)).symm

/-- A locally finite type morphism between quasi-compact quasi-separated schemes over a
quasi-compact quasi-separated stage becomes a closed immersion at some later stage if its
base change to the limit is a closed immersion.

Source: Stacks Project, Limits, Tag 01ZP, in Situation 081D
(blueprint: lem-weil-pbc-descend-closed-immersion).

Proof:
A closed immersion is finite and monic. Descend these two properties separately
(Stacks Limits, Tags 01ZO and 07RQ). Directedness gives a common upper stage.
Pullback composition identifies its morphism with a base change of either descended
morphism, so it is finite and monic there. The finite-monomorphism criterion gives a
closed immersion. -/
theorem exists_isClosedImmersion_stage_of_locallyOfFiniteType
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Iᵒᵖ ⥤ Scheme.{u})
    [∀ {i j : Iᵒᵖ} (t : i ⟶ j), IsAffineHom (D.map t)]
    (c : Cone D) (hc : IsLimit c) (i₀ : I)
    [CompactSpace (D.obj (op i₀))] [QuasiSeparatedSpace (D.obj (op i₀))]
    (X₀ Y₀ : Over (D.obj (op i₀)))
    [CompactSpace X₀.left] [QuasiSeparatedSpace X₀.left]
    [CompactSpace Y₀.left] [QuasiSeparatedSpace Y₀.left]
    (f₀ : X₀ ⟶ Y₀) [LocallyOfFiniteType f₀.left]
    (hf : IsClosedImmersion ((Over.pullback (c.π.app (op i₀))).map f₀).left) :
    ∃ (i : I) (h : i₀ ≤ i),
      IsClosedImmersion
        ((Over.pullback (D.map (homOfLE h).op)).map f₀).left := by
  have : IsClosedImmersion ((Over.pullback (c.π.app (op i₀))).map f₀).left := hf
  obtain ⟨i, hi, hfinite⟩ := exists_isFinite_baseChange_stage D c hc i₀ X₀ Y₀ f₀
    (inferInstance : IsFinite ((Over.pullback (c.π.app (op i₀))).map f₀).left)
  obtain ⟨j, hj, hmono⟩ := exists_mono_baseChange_stage D c hc i₀ X₀ Y₀ f₀
    (inferInstance : Mono ((Over.pullback (c.π.app (op i₀))).map f₀).left)
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, hi.trans hik, ?_⟩
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  constructor
  · have H := property_overPullback_comp (@IsFinite)
      (D.map (homOfLE hik).op) (D.map (homOfLE hi).op) f₀ hfinite
    have he : D.map (homOfLE hik).op ≫ D.map (homOfLE hi).op =
        D.map (homOfLE (hi.trans hik)).op := by
      rw [← Functor.map_comp]
      rfl
    rwa [he] at H
  · have H := property_overPullback_comp (MorphismProperty.monomorphisms Scheme.{u})
      (D.map (homOfLE hjk).op) (D.map (homOfLE hj).op) f₀ hmono
    have he : D.map (homOfLE hjk).op ≫ D.map (homOfLE hj).op =
        D.map (homOfLE (hi.trans hik)).op := by
      rw [← Functor.map_comp]
      rfl
    rw [he] at H
    exact H

end AlgebraicGeometry
