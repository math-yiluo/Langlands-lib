/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import WeilConjectures.AlgebraicGeometry.QuasiCoherentTensorProductAffineSections
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false in
private theorem product_quasicoherent {X : Scheme.{u}} {K : X.Modules}
    (i : K ⟶ SheafOfModules.unit X.ringCatSheaf) (F : X.Modules)
    [K.IsQuasicoherent] [F.IsQuasicoherent] :
    (Scheme.idealModuleProduct i F).IsQuasicoherent := by
  let : MonoidalCategory X.Modules := SheafOfModules.monoidalCategory X.sheaf
  have := (Scheme.Modules.quasiCoherent_tensor_product_affine_sections K F).1
  let a := (MonoidalCategoryStruct.whiskerRight i F) ≫
    (MonoidalCategoryStruct.leftUnitor F).hom
  have := Scheme.Modules.isQuasicoherent_cokernel a
  have := Scheme.Modules.isQuasicoherent_kernel (cokernel.π a)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage a) inferInstance

/-- The affine formal quotient projection is surjective.
Source: Stacks Project, Tags 01I8, 01IC and 087W, affine module correspondence.
(blueprint: lem-weil-pbc-formal-module-quotient-affine-projection-surj).

Proof: The associated sheaf of M is quasi-coherent, as is the positive ideal power
by the ideal-times affine-sections theorem. Its product with the associated sheaf
is the image of the multiplication from their tensor product. Tensor products,
cokernels and kernels preserve quasi-coherence, so this image is quasi-coherent.
Apply the affine cokernel-image theorem to the product inclusion on the whole
spectrum. Its cokernel projection is surjective on sections. The functor
moduleSpecΓFunctor only restricts scalars on those sections; therefore its map is
surjective as well. Compose with the bijective tilde unit to obtain p. -/
theorem formalModuleQuotient_affine_projection_surjective
    (A : Type u) [CommRing A] (I : Ideal A)
    (J : (Spec (CommRingCat.of A)).IdealSheafData)
    (hJ : J = Scheme.IdealSheafData.ofIdealTop
      (I.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom))
    (M : ModuleCat.{u} A) (m : ℕ) (hm : 0 < m) :
    let p := (tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app M ≫
      (moduleSpecΓFunctor (R := CommRingCat.of A)).map
        (formalModuleQuotientπ J m ((tilde.functor (CommRingCat.of A)).obj M))
    Function.Surjective p := by
  have _hJ := hJ
  let F := (tilde.functor (CommRingCat.of A)).obj M
  have : F.IsQuasicoherent := by
    change (tilde.{u} (R := CommRingCat.of A) M).IsQuasicoherent
    infer_instance
  have := (Scheme.Modules.ideal_times_quasiCoherent_affine_sections J F).2.2.1 m hm
  have := product_quasicoherent (Scheme.idealSheafPower J.toModulesι m).2 F
  have hs := (Scheme.Modules.quasiCoherent_cokernel_image
    (Scheme.idealModuleProductι (Scheme.idealSheafPower J.toModulesι m).2 F)).2.2.2.2.2.2.2.2
      ⟨⊤, isAffineOpen_top (Spec (CommRingCat.of A))⟩
  have hq : Function.Surjective
      ((moduleSpecΓFunctor (R := CommRingCat.of A)).map (formalModuleQuotientπ J m F)) :=
    hs.2.1
  exact hq.comp (ConcreteCategory.bijective_of_isIso
    ((tilde.toTildeΓNatIso (R := CommRingCat.of A)).hom.app M)).2

end AlgebraicGeometry
