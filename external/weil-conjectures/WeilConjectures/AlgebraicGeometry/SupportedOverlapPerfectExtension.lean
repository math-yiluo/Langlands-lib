/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.AffineScheme

import WeilConjectures.AlgebraicGeometry.AffinePerfectSupportExtension
import WeilConjectures.AlgebraicGeometry.SupportedOverlapRestrictionData

/-! # Supported perfect extension across an affine overlap

Source: Stacks Project, Tags 08EK and 09IM.
(blueprint: lem-sc-supported-overlap-perfect-extension).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

-- The chosen overlap localization and its open-site family are dependent data.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
/-- Extend the stabilization of a supported perfect object from the overlap to V.
Source: Stacks Project, Tag 09IM, affine extension step using Tag 08EK.
(blueprint: lem-sc-supported-overlap-perfect-extension).

Proof: Regard W intersect V as the inverse-image open U in V. Its inclusion into the
ambient overlap is a scheme isomorphism. Quasi-separatedness makes the intersection of
the compact opens W and V compact; the homeomorphism makes U compact. The inverse image
of T in V is closed. Its complement is compact because it identifies with the intersection
of V and the compact open complement of T. Restrict F from W to the overlap. Restriction
of strictly perfect local models proves perfectness there, and exactness and the stalk
comparison prove support on the pullback of T. Transport this object to U and apply
exists_perfect_supported_extension on the affine scheme V.toScheme. Transport the resulting
restriction isomorphism back through the scheme isomorphism. Exact restriction preserves
biproducts and commutes with shifts, identifying its stabilized target with the displayed
restriction of F plus F[1]. The same comparisons give the stated support on V. Empty
opens and T are covered by the extension theorem and the zero restriction categories. -/
theorem exists_supported_overlap_perfect_extension
    (X : Scheme.{u}) [QuasiSeparatedSpace X]
    (W V : X.Opens) (hW : IsCompact (W : Set X)) (hV : IsAffineOpen V)
    (T : Set X) (hT : IsClosed T) (hTc : IsCompact Tᶜ)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace))]
    [∀ O : W.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings W.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [∀ O : V.toScheme.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings V.toScheme.toRingedSpace).over O))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (W ⊓ V).toScheme.toRingedSpace))]
    (F : schemeDerivedCategory W.toScheme) (hF : IsPerfect W.toScheme F)
    (hFT : (∀ (i : ℤ) (x : W.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace)) i).obj F).val.presheaf x)))) :
    let SW := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_left : W ⊓ V ⟶ W)).mapDerivedCategory
    let SV := (schemeOpenOverlapRestriction X
      (homOfLE inf_le_right : W ⊓ V ⟶ V)).mapDerivedCategory
    ∃ Q : schemeDerivedCategory V.toScheme, IsPerfect V.toScheme Q ∧
      (∀ (i : ℤ) (x : V.toScheme), x.val ∉ T →
      Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) i).obj Q).val.presheaf x))) ∧
      Nonempty (SV.obj Q ≅ SW.obj (F ⊞ F⟦(1 : ℤ)⟧)) := by
  classical
  obtain ⟨U, hU, hTV, hTVc, hD, hO, G, hG, hGT, e, ⟨d⟩, ⟨g⟩⟩ :=
    exists_supported_overlap_restriction_data X W V hW hV T hT hTc F hF hFT
  let := hD
  let := hO
  let : IsAffine V.toScheme := hV
  obtain ⟨Q, hQ, hQT, ⟨q⟩⟩ := exists_perfect_supported_extension V.toScheme
    (Subtype.val ⁻¹' T) hTV hTVc U hU G hG hGT
  exact ⟨Q, hQ, hQT, ⟨(d.app Q).symm ≪≫ e.functor.mapIso q ≪≫ g⟩⟩

end AlgebraicGeometry.Scheme
