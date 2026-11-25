/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Lifting closed-point classes across a curve compactification

Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine,
first paragraph, restriction and boundary divisors
(blueprint: lem-sc-pic-restriction-point-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

/-- Closed points lift to the compactification and their point-ideal classes pull back correctly.
Source: blueprint, sec-curve-estimates/lem-sc-arbitrary-curve-cd/lem-sc-pic-affine, first paragraph;
restriction and boundary divisors, steps 1 and 4 of lem-sc-pic-restriction-exact
(blueprint: lem-sc-pic-restriction-point-lift).

Proof: Send Q to c.i(Q). A closed point of a finite-type curve over the algebraically closed
field is a rational point, so its image in the separated finite-type curve c.Z is closed.
The open immersion identifies the stalks at Q and its image. Pullback of the vanishing ideal
of the image is the vanishing ideal of Q: on this open subscheme both are the ideal defining
that reduced point. Pullback commutes with the dual of an invertible module. Therefore the
classes of the dual point ideals satisfy the displayed equality. This is the single-point
case of restricting O(D); arbitrary divisors follow by the group law. No boundary point is
chosen, and the assertion remains valid when the boundary is empty. -/
theorem Scheme.Hom.pic_restriction_point_lift
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g] [hC : SmoothOfRelativeDimension 1 f]
    (Q : closedPoints C) :
    ∃ P : closedPoints c.Z, P.val = c.i.base Q.val ∧
      Scheme.Pic.mapHom c.i (@Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P) =
        @Scheme.Pic.ofClosedPoint k _ C ⟨f⟩ hC Q  := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  let : c.Z.Over (Spec (.of k)) := ⟨c.g⟩
  let : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) := by
    change SmoothOfRelativeDimension 1 f
    exact hC
  let : SmoothOfRelativeDimension 1 (c.Z ↘ Spec (.of k)) := by
    change SmoothOfRelativeDimension 1 c.g
    exact hsm
  let x := pointOfClosedPoint f Q.val Q.property
  have hx : x ≫ f = 𝟙 _ := pointOfClosedPoint_comp f Q.val Q.property
  have hcomp : (x ≫ c.i) ≫ c.g = 𝟙 _ := by rw [Category.assoc, ← c.comm, hx]
  have : IsClosedImmersion (x ≫ c.i) := isClosedImmersion_of_comp_eq_id c.g _ hcomp
  have hclosed : IsClosed ({c.i.base Q.val} : Set c.Z) := by
    have hr : Set.range (x ≫ c.i).base = {c.i.base Q.val} := by
      apply Set.range_eq_singleton_iff.mpr
      intro a
      change c.i.base (x.base a) = c.i.base Q.val
      rw [pointOfClosedPoint_apply]
    rw [← hr]
    exact (x ≫ c.i).isClosedEmbedding.isClosed_range
  let P : closedPoints c.Z := ⟨c.i.base Q.val, hclosed⟩
  refine ⟨P, rfl, ?_⟩
  let I : C.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{Q.val}, Q.property⟩
  let J : c.Z.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨{P.val}, P.property⟩
  have hmap : I.map c.i = J := by
    dsimp only [I]
    rw [Scheme.IdealSheafData.map_vanishingIdeal]
    apply congrArg Scheme.IdealSheafData.vanishingIdeal
    apply SetLike.coe_injective
    change closure (c.i.base '' {Q.val}) = {c.i.base Q.val}
    rw [Set.image_singleton, hclosed.closure_eq]
  have : QuasiCompact c.i := by
    have : IsNoetherian C := isNoetherian_of_locallyOfFiniteType f
    infer_instance
  have hcomap : J.comap c.i = I := by
    rw [← hmap, Scheme.IdealSheafData.comap_map]
  have hI : I.IsInvertible := isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one
    f Q.property
  have hJ : J.IsInvertible := isInvertible_vanishingIdeal_of_smoothOfRelativeDimension_one
    c.g P.property
  have hJ' : (J.comap c.i).IsInvertible := by rw [hcomap]; exact hI
  have := hI.isInvertible_dual_toModules
  have := hJ.isInvertible_dual_toModules
  obtain ⟨e⟩ := hJ.nonempty_pullback_dual_toModules_iso c.i hJ'
  have e' : (J.comap c.i).toModulesᵛ ≅ I.toModulesᵛ :=
    eqToIso (congrArg (fun K ↦ K.toModulesᵛ) hcomap)
  change Scheme.Pic.mapHom c.i (Scheme.Pic.ofIsInvertible J.toModulesᵛ) =
    Scheme.Pic.ofIsInvertible I.toModulesᵛ
  apply Scheme.Pic.eq_iff_nonempty_iso.2
  exact ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Scheme.Modules.pullback c.i).mapIso (Scheme.Pic.ofIsInvertibleIso _) ≪≫ e ≪≫ e' ≪≫
    (Scheme.Pic.ofIsInvertibleIso _).symm⟩

end AlgebraicGeometry
