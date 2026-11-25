/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
import WeilConjectures.AlgebraicGeometry.Curve.EtaleIdealKernelIso
import WeilConjectures.AlgebraicGeometry.Curve.EtaleNestedIdealKernel
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact

/-! # Tensor presentation of the kernel of ideal restriction

Source: blueprint `lem-sc-additive-ideal-image-tensor-comparison`, Proof, Steps 1 and 3.
(blueprint: lem-sc-etale-ideal-kernel-presentation)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Tensor sections of an ideal identify with its additive vanishing functions.
For nested ideals, the tensor of their inclusion is a kernel of restriction.
There is no cokernel or quasi-coherence-of-the-quotient assumption in this assertion.
Source: blueprint `lem-sc-additive-ideal-image-tensor-comparison`, Steps 1 and 3,
from `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim.
(blueprint: lem-sc-etale-ideal-kernel-presentation)

Proof: Cover an etale object by affine etale objects V over affine opens
U=Spec A of X. Write B=Gamma(V,O). Etaleness makes B flat over A. Pullback of
0 to I(U) to A identifies B tensor I(U) with the extended ideal I_B in B.
The specified module I.toModules is the kernel of restriction to Z_I;
its inclusion in the structure module is the specified ideal inclusion.
Restriction to V times_X Z_I is the quotient B to B/I_B. Thus the canonical
map from tensor sections of I to additive functions is an isomorphism onto
its kernel. The same applies to J. The map on tensor sections induced by
J.toModules to I.toModules is the ordinary inclusion J_B to I_B. Restriction
of I_B to B/J_B has kernel J_B. It follows that this map, followed by the
kernel identification for I, is a kernel of restriction to Z_J. All maps
used are the inclusion of an ideal, restriction of functions, or tensor base
change. They commute with ring maps, so the affine identifications glue
uniquely on overlaps and give the claimed kernel fork on the whole etale
site. Sheafification and additive universe lift preserve kernels. When I=J
the kernel fork is an identity fork, when J=0 it has zero kernel, and for
empty objects all the groups are zero. -/
theorem exists_etaleIdealKernelPresentation (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) :
    ∃ e : (Modules.etaleTensorSectionsFunctor X).obj I.toModules ≅
        kernel (etaleAdditiveSheafToLowerStar I.subschemeι),
      ∃ hzero : ((Modules.etaleTensorSectionsFunctor X).map
          (IdealSheafData.toModulesOfLE hJI) ≫ e.hom) ≫
          (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
            etaleAdditiveSheafToLowerStar J.subschemeι) = 0,
        Nonempty (IsLimit (KernelFork.ofι
          ((Modules.etaleTensorSectionsFunctor X).map
            (IdealSheafData.toModulesOfLE hJI) ≫ e.hom) hzero)) := by
  obtain ⟨eI, eJ, he⟩ := exists_etaleIdealKernelIsoPair X I J hJI
  obtain ⟨k, hk, hz, ⟨hlim⟩⟩ := exists_etaleNestedIdealKernel X I J hJI
  have hmap : eJ.hom ≫ k =
      (Modules.etaleTensorSectionsFunctor X).map
        (IdealSheafData.toModulesOfLE hJI) ≫ eI.hom := by
    apply (cancel_mono (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι))).mp
    simpa only [Category.assoc, hk] using he.symm
  have hzero : ((Modules.etaleTensorSectionsFunctor X).map
      (IdealSheafData.toModulesOfLE hJI) ≫ eI.hom) ≫
      (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
        etaleAdditiveSheafToLowerStar J.subschemeι) = 0 := by
    rw [← hmap, Category.assoc, hz, comp_zero]
  exact ⟨eI, hzero, ⟨IsKernel.isoKernel _ _ hlim eJ hmap⟩⟩

end AlgebraicGeometry.Scheme
