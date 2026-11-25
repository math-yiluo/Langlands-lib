/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.FlatBaseChangeOpenChoices
public import Mathlib.Algebra.Module.LocalizedModule.Away
import WeilConjectures.AlgebraicGeometry.SectionCohomologyPrincipalLocalization

/-! # Principal localization of the higher-image cohomology presheaf

Source: Stacks Project, Tag 09MR, tensor-unit specialization, and Tag 01E4.
(blueprint: lem-pc-higher-image-cohomology-presheaf-localization).
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The restriction on resolution cohomology over inverse images of affine opens is
module localization at the defining function. This concerns presheaf cohomology,
not sections of the higher direct image sheaf.
Source: Stacks Project, Tags 09MR and 01E4.
(blueprint: lem-pc-higher-image-cohomology-presheaf-localization).

Proof: Let Y = f⁻¹W and b = f^♯a. The qcqs hypotheses and affineness of W imply
that Y is qcqs. Restriction of F to Y remains quasi-coherent. Apply 09MR on Y
with L = O_Y and s = b. Identify every tensor power of O_Y with O_Y by the
unitors; the transition morphisms are multiplication by b. The fraction
presentation is therefore ordinary localization at b. Its comparison sends
x/b^n to b^(-n) res(x), which is linear over Γ(T,W), acting through f^♯.
The equality f⁻¹D(a) = D(b) identifies its target with cohomology over
f⁻¹D(a). Compute both cohomology groups from I: restriction of an injective
resolution to an open is injective, and exact evaluation identifies the
presheaf homology with these section-complex homology groups. The restriction
identification in 01E4 identifies the map with P.map, not an arbitrary
localization map. Transport the localization property through these linear
identifications. This includes q = 0 and a = 0; localization at zero is zero,
as is cohomology on the empty open. -/
theorem higherImageCohomologyPresheaf_isLocalized
    {X T : Scheme.{u}} (f : X ⟶ T) [QuasiCompact f] [QuasiSeparated f]
    (F : X.Modules) [F.IsQuasicoherent] (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (hW : IsAffineOpen W) (a : Γ(T, W)) :
    let P := sectionCohomologyPresheaf
      (((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) q
    IsLocalizedModule.Away a (P.map (homOfLE (T.basicOpen_le a)).op).hom := by
  exact sectionCohomologyPresheaf_isLocalized_away f F I q W hW a

end AlgebraicGeometry.Scheme.Modules
