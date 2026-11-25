/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.AlgebraicGeometry.Curve.NilIdealUnitImageRelativeKernel
import WeilConjectures.AlgebraicGeometry.Curve.IdealAdditiveImageRelativeKernel
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroRelativeUnitsAdditiveKernel

/-! # Linearizing the unit image into the additive image

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim,
as expanded in `lem-sc-nil-ideal-units-image-linearization`, Steps 2 and 3.
(blueprint: lem-sc-nil-ideal-units-additive-image-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- For a nil ideal I with I squared contained in J contained in I, subtracting one
identifies the multiplicative image of the congruence subgroup with the additive
image of the ideal. This assertion involves only structure rings and their units,
not the module cokernel or tensor sections.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim;
`lem-sc-nil-ideal-units-image-linearization`, Steps 2 and 3.
(blueprint: lem-sc-nil-ideal-units-additive-image-comparison)

Proof: On an affine etale V over affine U, put B=Gamma(V,O). The pullbacks of I,J
have ideals I_B,J_B. Sections of the two kernels are respectively units congruent
to one modulo I_B and the additive ideal I_B. Every a in I_B is nilpotent: it is
a finite sum of multiples of images of nilpotent elements of I(U), and nilpotent
elements of a commutative ring form an ideal. Thus 1+a is a unit by the finite
geometric-series inverse. The sectionwise unit image consists of the images of
1+a in (B/J_B)^units. Subtracting one sends such an image to the image of a in
B/J_B. This is well defined and injective since equality on both sides is
exactly a-b in J_B. It is surjective since every additive image comes from an
a in I_B. It preserves the group operations: ab lies in J_B, so
(1+a)(1+b)=1+a+b modulo J_B. Its inverse sends a mod J_B to 1+a mod J_B.
Both formulas commute with ring maps and therefore with restrictions to affine
etale refinements. Categorical sheaf images are sheafifications of these
presheaf images; sheafifying the mutually inverse natural homomorphisms gives
the desired isomorphism, including the coefficient universe lift. When I=J,
I=0 or the scheme is empty both images vanish and the formulas still apply.
No quasi-coherence assertion about the module cokernel is used.

Formal reduction: First identify each image with the pushforward from Z_J of
the corresponding kernel for Z_I to Z_J. The unit identification uses nilpotence
to lift units; the additive identification is quotient exactness without any
nil hypothesis. On Z_J the relative ideal I/J has square zero, so subtracting
one identifies these two kernel sheaves. Push forward that isomorphism and
compose with the two image identifications. -/
theorem nonempty_nilIdealUnitsAdditiveImageIso (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) (hII : I * I ≤ J)
    (hIN : I ≤ X.nilradical) :
    Nonempty (image (kernel.ι (gmSheafToLowerStarGmSheaf I.subschemeι) ≫
        gmSheafToLowerStarGmSheaf J.subschemeι) ≅
      image (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
        etaleAdditiveSheafToLowerStar J.subschemeι)) := by
  obtain ⟨eUnits⟩ := nonempty_nilIdealUnitImageRelativeKernelIso X I J hJI hIN
  obtain ⟨eAdditive⟩ := nonempty_idealAdditiveImageRelativeKernelIso X I J hJI
  obtain ⟨eRelative⟩ := nonempty_squareZeroRelativeUnitsAdditiveKernelIso X I J hJI hII
  exact ⟨eUnits ≪≫
    (Etale.lowerStar AddCommGrpCat.{u + 1} J.subschemeι).mapIso eRelative ≪≫
      eAdditive.symm⟩

end AlgebraicGeometry.Scheme
