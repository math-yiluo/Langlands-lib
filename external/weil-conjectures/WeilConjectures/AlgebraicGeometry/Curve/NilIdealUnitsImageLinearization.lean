/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.Curve.NilIdealUnitsAdditiveImageComparison
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveIdealImageTensorComparison
import WeilConjectures.CategoryTheory.Sites.Torsor

/-! # Linearization of the image of nilpotent units modulo an ideal

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-nil-ideal-units-image-linearization)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- For nil ideals `J ≤ I` with `I * I ≤ J`, the image of the units congruent to one
modulo `I` in the units on the subscheme defined by `J` is the additive sheaf of `I/J`.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-nil-ideal-units-image-linearization)

Proof: Work over an affine etale object V over an affine open U of X. Write A for
Gamma(U,O), B for Gamma(V,O), and I_B,J_B for the extended ideals. Flatness identifies
sections of the pullback of the module cokernel with I_B/J_B. The image sheaf in the
statement is locally the image of 1+I_B in (B/J_B)^units. Indeed kernels of sheaves are
computed on sections, and categorical images are sheafifications of presheaf images.
Every element a of I_B is nilpotent: the generators coming from I are nilpotent, and
finite sums of multiples of nilpotents in a commutative ring are nilpotent. Hence 1+a
is a unit, by the finite geometric-series inverse. Map its image in B/J_B to a mod J_B.
Two representatives give the same unit exactly when their differences lie in J_B, so
this map is well defined and injective. Every class of I_B/J_B is obtained this way.
It is additive because (1+a)(1+b)=1+a+b+ab and I_B squared is contained in J_B.
Pullback of functions respects both formulas, so the local identifications and their
inverses commute with restriction and glue on affine etale refinements. They give an
isomorphism of sheaves. The module cokernel and tensor sections use these same affine
quotient modules, not independently chosen objects. Applying the coefficient universe
lift gives exactly the groups used for Gm. For I=J the image and quotient vanish;
for I=0 or empty X the same construction is the unique map between zero sheaves.
No finite generation, Noetherian, or uniform nilpotence assumption is used. -/
theorem nonempty_nilIdealUnitsImageIso (X : Scheme.{u}) (I J : X.IdealSheafData)
    (hJI : J ≤ I) (hII : I * I ≤ J) (hIN : I ≤ X.nilradical)
    [(cokernel (IdealSheafData.toModulesOfLE hJI)).IsQuasicoherent] :
    Nonempty (image (kernel.ι (gmSheafToLowerStarGmSheaf I.subschemeι) ≫
        gmSheafToLowerStarGmSheaf J.subschemeι) ≅
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf
          (cokernel (IdealSheafData.toModulesOfLE hJI))))) := by
  obtain ⟨unitsToAdditive⟩ :=
    nonempty_nilIdealUnitsAdditiveImageIso X I J hJI hII hIN
  obtain ⟨additiveToTensor⟩ := nonempty_additiveIdealImageTensorIso X I J hJI
  exact ⟨unitsToAdditive.trans additiveToTensor⟩

end AlgebraicGeometry.Scheme
