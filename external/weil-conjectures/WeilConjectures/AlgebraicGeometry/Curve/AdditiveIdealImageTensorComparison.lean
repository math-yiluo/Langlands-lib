/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.Curve.EtaleIdealKernelPresentation
import Mathlib.CategoryTheory.Abelian.Exact

/-! # The additive ideal image and tensor sections

Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim,
as expanded in `lem-sc-nil-ideal-units-image-linearization`, Step 1.
(blueprint: lem-sc-additive-ideal-image-tensor-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- For J contained in I, the additive image of the ideal of I on the subscheme of J
is the etale sheaf associated with the specified module cokernel J to I.
There is no nilpotence or square-zero hypothesis in this additive assertion.
Source: blueprint `lemma-cohomology-multiplicative-group--6`, Proof, Step 1 and its Claim;
`lem-sc-nil-ideal-units-image-linearization`, Step 1.
(blueprint: lem-sc-additive-ideal-image-tensor-comparison)

Proof: Refine any etale object by affine etale V over affine open U=Spec A of X.
Write B=Gamma(V,O), and I_B,J_B for the extended ideals. The kernel of restriction
of functions to V times_X Z_I has sections I_B; restriction to V times_X Z_J
sends this ideal to its image in B/J_B. Its kernel is J_B, since J is contained
in I. Thus the sectionwise additive image is I_B/J_B. Flatness of B over A
identifies this quotient with B tensor_A coker(J(U) to I(U)). The specified
ideal modules are kernels of the same structure-module restrictions, so their
affine sections are precisely I(U) and J(U), and the specified inclusion is the
ordinary inclusion. The affine tensor description identifies the latter tensor
product with sections of the pullback of the specified module cokernel.
These linear identifications commute with restriction because quotient maps,
ideal inclusions and tensor base change commute with ring maps. Sheafifying
the presheaf image and gluing the comparisons on affine etale refinements gives
the stated sheaf isomorphism. Finally lift additive groups to the Gm universe;
the lift is an equivalence onto its image and preserves the identifications.
For I=J both sides vanish; the zero ring and empty objects give zero groups. -/
theorem nonempty_additiveIdealImageTensorIso (X : Scheme.{u}) (I J : X.IdealSheafData)
    (hJI : J ≤ I) [(cokernel (IdealSheafData.toModulesOfLE hJI)).IsQuasicoherent] :
    Nonempty (image (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
        etaleAdditiveSheafToLowerStar J.subschemeι) ≅
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf
          (cokernel (IdealSheafData.toModulesOfLE hJI))))) := by
  let T := Modules.etaleTensorSectionsFunctor X
  let a := IdealSheafData.toModulesOfLE hJI
  let f := kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
    etaleAdditiveSheafToLowerStar J.subschemeι
  obtain ⟨e, hz, ⟨hk⟩⟩ := exists_etaleIdealKernelPresentation X I J hJI
  let S := ShortComplex.mk (T.map a ≫ e.hom) f hz
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hk
  let e₁ : cokernel (T.map a ≫ e.hom) ≅ image f :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hS.isColimitImage
  let e₂ : cokernel (T.map a) ≅ cokernel (T.map a ≫ e.hom) :=
    cokernel.mapIso _ _ (Iso.refl _) e (by simp)
  have : PreservesColimitsOfShape WalkingParallelPair T :=
    Modules.preservesCokernels_etaleTensorSectionsFunctor X
  exact ⟨e₁.symm ≪≫ e₂.symm ≪≫ (PreservesCokernel.iso T a).symm ≪≫
    Modules.etaleTensorSectionsFunctorObjIso (cokernel a)⟩

end AlgebraicGeometry.Scheme
