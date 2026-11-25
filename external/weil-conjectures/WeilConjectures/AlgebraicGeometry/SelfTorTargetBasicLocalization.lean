/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.RingTheory.SelfTorConormalComparison
public import Mathlib.AlgebraicGeometry.Modules.Tilde

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection

import WeilConjectures.AlgebraicGeometry.SelfTorTargetRestrictionCoordinates
import WeilConjectures.RingTheory.SelfTorRestrictionConormalWedge

/-! # Target self-Tor coordinates and principal localization of algebraic wedge images

Source: Stacks Project, Tags 09PQ and 06YH.
(blueprint: new-t2-self-tor-target-basic-localization). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace AlgebraicGeometry

/-- Choose only the Tor-to-derived-homology coordinates, and compare their values on
explicit associated algebraic Tor elements under a principal localization. No exterior
sheaf source coordinate or pullback-unit wedge equation is assumed or asserted.
Source: Stacks Project, Tag 09PQ (normalized Tor products), Tag 06YH (K-flat tensor).
(blueprint: new-t2-self-tor-target-basic-localization).

Proof: On each U choose a projective quotient resolution with its augmentation.
Sheafify it using exists_affine_quotient_sheafified_resolution. Its bounded-above
flat cochain complex is K-flat, so the augmentation comparison with the fixed derived
tensor identifies quotient-tensored homology with the restriction of its homology.
The ideal acts by zero on Tor; its tensor pullback is thus the associated Tor module
on the closed chart. This gives t on each chart, determined by the augmented
resolution comparison. For V=D(f) and b defined on U, include b into I_U. Lift the
Koszul quotient augmentation for that tuple to the projective resolution on U.
After quotient tensoring its top wedge is a cycle. By selfTorConormalComparison_spec,
its homology image is c_U(selfTorIdealWedge b). Localization is flat, preserves the
augmentation and the projective resolution, and takes this cycle to the cycle of
the restricted tuple on V. Compare this localized resolution with the one chosen
on V over the quotient augmentation. The two Koszul lifts are chain homotopic,
so they have equal homology images. Normalization on V identifies that image with
c_V of the restricted ideal wedge. The K-flat augmentation comparison identifies
these classes in the fixed derived tensor and commutes with restriction. The
explicit selfTorAffineSection sends each algebraic class to exactly its associated
sheaf section and then its tensor-pullback-unit image, so the equality is precisely
the displayed equation. In degree zero the cycle is the quotient unit; for f=0
both sides are sections on the empty chart, and for f=1 the localization is the
identity. Zero quotients give zero modules. No regularity, finite generation of I,
or acyclicity of the Koszul complex is used. -/
theorem exists_selfTor_target_basic_localization
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    let c := fun U : Y.affineOpens ↦
      selfTorConormalComparison (Γ(Y, U.1) : Type u) (i.ker.ideal U) n
    ∃ t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1)
        (b : Fin n → i.ker.toModules.val.obj (op U.1)),
        (t U).hom.val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
            (((T U).obj _).val.map (homOfLE (i.preimage_mono h)).op
              (selfTorAffineSection i U _ ((c U) (selfTorIdealWedge i U n b)))) =
          (t V).hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
            (selfTorAffineSection i V _ ((c V) (selfTorIdealWedge i V n
              (fun j ↦ i.ker.toModules.val.map (homOfLE h).op (b j))))) := by
  classical
  dsimp only
  obtain ⟨t, ht⟩ := exists_selfTor_target_restriction_coordinates.{u, w} i n
  refine ⟨t, ?_⟩
  intro V U h hbasic b
  obtain ⟨q, hq, hx⟩ := ht V U h hbasic
  have hg (j : Fin n) :
      (Y.presheaf.map (homOfLE h).op).hom (selfTorIdealSection i U (b j)) =
        selfTorIdealSection i V (i.ker.toModules.val.map (homOfLE h).op (b j)) := by
    exact (PresheafOfModules.naturality_apply i.ker.toModulesι.val
      (homOfLE h).op (b j)).symm
  have hw := selfTor_restriction_conormal_wedge
    (Γ(Y, U.1) : Type u) (Γ(Y, V.1) : Type u) (i.ker.ideal U) (i.ker.ideal V)
    (Y.presheaf.map (homOfLE h).op).hom n q hq
    (fun j ↦ selfTorIdealSection i U (b j))
    (fun j ↦ selfTorIdealSection i V (i.ker.toModules.val.map (homOfLE h).op (b j))) hg
  change q (selfTorConormalComparison _ _ n (selfTorIdealWedge i U n b)) =
    selfTorConormalComparison _ _ n (selfTorIdealWedge i V n
      (fun j ↦ i.ker.toModules.val.map (homOfLE h).op (b j))) at hw
  exact (hx (selfTorConormalComparison _ _ n (selfTorIdealWedge i U n b))).trans
    (congrArg (fun x ↦ (t V).hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
      (selfTorAffineSection i V _ x)) hw)

end AlgebraicGeometry
