/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroRelativeSectionKernel
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroUnitsAdditiveKernelOfSections

/-! # A square-zero closed immersion identifies its unit and additive kernels.

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-square-zero-relative-units-additive-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- A square-zero closed immersion identifies its unit and additive kernels.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-square-zero-relative-units-additive-kernel)

Proof: The kernel ideal of the closed immersion Z_I to Z_J is I/J and its
square is zero since I squared is contained in J. On an affine etale object
of Z_J, let C be its structure ring and K the extended ideal of this immersion.
It too has square zero, by base change. Sections of the unit kernel are units
u with u-1 in K; sections of the additive kernel are elements a of K. Send u
to u-1 and a to 1+a. The latter is a unit with inverse 1-a because a squared
is zero. The formulas are inverse. For a,b in K their product is zero, so
(1+a)(1+b)=1+a+b, proving additivity after writing units additively. These
formulas commute with structure ring maps and the coefficient universe lift.
They therefore define mutually inverse morphisms on the affine etale basis
and extend uniquely to the two kernel sheaves on Z_J. This argument needs
no nilpotence of I on X: only I/J has to be square zero. For I=J or I=0 both
kernels are zero. Over the empty scheme all section groups are trivial. -/
theorem nonempty_squareZeroRelativeUnitsAdditiveKernelIso (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hII : I * I ≤ J) :
    Nonempty (kernel (gmSheafToLowerStarGmSheaf (IdealSheafData.inclusion hJI)) ≅
      kernel (etaleAdditiveSheafToLowerStar (IdealSheafData.inclusion hJI))) := by
  apply nonempty_unitsAdditiveKernelIso_of_sections (IdealSheafData.inclusion hJI)
  intro V a b ha hb
  exact squareZeroRelativeSectionKernel X I J hJI hII V a b ha hb

end AlgebraicGeometry.Scheme
