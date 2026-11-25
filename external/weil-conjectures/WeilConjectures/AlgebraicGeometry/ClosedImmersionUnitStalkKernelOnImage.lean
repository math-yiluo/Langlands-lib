/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.ClosedPushforwardStalks
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! # Kernel of the pullback unit at a point on the closed image

Source: Stacks Project, Modules, Lemma 08KS, using Sheaves, Lemmas 0098 and 00AE.
(blueprint: lem-weil-pbc-closed-immersion-unit-stalk-kernel-on-image).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings
open AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem ker_tensor_unit {R S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{w} R) :
    let :=  f.toAlgebra
    LinearMap.ker (TensorProduct.mk R S M 1) =
      RingHom.ker f • (⊤ : Submodule R M) := by
  let :=  f.toAlgebra
  let g : R →ₗ[R] S := Algebra.linearMap R S
  have hg : Function.Surjective g := hf
  have hk := (rTensor_exact M g.exact_subtype_ker_map hg).linearMap_ker_eq
  apply Submodule.comap_injective_of_surjective (TensorProduct.lid R M).surjective
  rw [← LinearMap.ker_comp]
  have heq : (TensorProduct.mk R S M 1).comp (TensorProduct.lid R M).toLinearMap =
      LinearMap.rTensor M g := by
    ext r
    simp [g]
  rw [heq, hk]
  rw [Submodule.comap_equiv_eq_map_symm]
  symm
  rw [Submodule.map_symm_eq_iff, Submodule.map_range_rTensor_subtype_lid]
  rfl

/-- At a point on the closed image, the kernel of the pullback unit is the local
ring kernel times the module stalk. This involves no ideal sheaf or multiplication map.
Source: Stacks Project, Modules, Lemma 08KS; Sheaves, Lemmas 0098 and 00AE.
(blueprint: lem-weil-pbc-closed-immersion-unit-stalk-kernel-on-image).

Proof: For the canonical tensor adjunction, compose the pushforward stalk comparison
at i(z) with the tensor pullback stalk comparison. The germ formulas identify the
unit with m mapping to 1 tensor m in O_Z,z tensor over O_Y,i(z) F_i(z).
The local ring map is surjective because i is a closed immersion. Writing its
kernel as K, tensor the exact pair K -> O_Y,i(z) -> O_Z,z with F_i(z).
Right exactness identifies the tensor map kernel with the image of K tensor F_i(z).
The left unitor O_Y,i(z) tensor F_i(z) -> F_i(z) sends that image to K F_i(z)
and sends the tensor map to m mapping to 1 tensor m. Its kernel is K F_i(z).
For any other adjunction on the same two functors, uniqueness of left adjoints
relates its unit to the canonical unit by postcomposition with the pushforward
of an isomorphism. Its stalk is invertible, so the kernel does not change.
For the identity immersion K is zero; for F zero both submodules are zero.
The empty immersion has no z and hence introduces no excluded case. -/
theorem closedImmersion_unit_stalk_kernel_on_image {Y Z : Scheme.{w}} (i : Z ⟶ Y)
    [IsClosedImmersion i] (F : Y.Modules) (z : Z) :
    let adj := Classical.choice (nonempty_tensorPullbackAdjunction i)
    let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace (i.base z)
    LinearMap.ker (S.map (adj.unit.app F)).hom =
      RingHom.ker (i.stalkMap z).hom •
        (⊤ : Submodule (Y.presheaf.stalk (i.base z)) (S.obj F)) := by
  classical
  dsimp only
  let S := RingedSpace.moduleStalkFunctor Y.toRingedSpace (i.base z)
  let G := (tensorPullback i).obj F
  let adj₀ := Classical.choose (exists_tensorPullbackAdjunction i)
  let adj₁ := Classical.choice (nonempty_tensorPullbackAdjunction i)
  obtain ⟨δ, hδ⟩ := exists_tensorPullback_stalk_iso i z
  let c := TopCat.Presheaf.stalkPushforward Ab i.base G.presheaf z
  have hc : IsIso c := (closedImmersion_pushforward_stalks i i.isClosedEmbedding G).2.1 z |>.2.1
  let ε : S.obj ((pushforward i).obj G) ≃+
      (ModuleCat.extendScalars (i.stalkMap z).hom).obj (S.obj F) :=
    (asIso c).addCommGroupIsoToAddEquiv.trans (δ.app F).toLinearEquiv.toAddEquiv
  have hunit (m : S.obj F) :
      ε (S.map (adj₀.unit.app F) m) =
        (1 : Z.presheaf.stalk z) ⊗ₜ[Y.presheaf.stalk (i.base z), (i.stalkMap z).hom] m := by
    obtain ⟨U, hx, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf m
    have hg : S.map (adj₀.unit.app F)
        (TopCat.Presheaf.germ F.val.presheaf U (i.base z) hx m) =
      TopCat.Presheaf.germ ((pushforward i).obj G).val.presheaf U (i.base z) hx
        ((adj₀.unit.app F).val.app (op U) m) := by
      change RingedSpace.stalkAddMap Y.toRingedSpace (i.base z) _ _ = _
      dsimp only [RingedSpace.stalkAddMap]
      erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
      rfl
    rw [hg]
    change (δ.hom.app F) (c
      (TopCat.Presheaf.germ ((pushforward i).obj G).val.presheaf U (i.base z) hx
        ((adj₀.unit.app F).val.app (op U) m))) = _
    erw [TopCat.Presheaf.stalkPushforward_germ_apply]
    exact hδ F U hx m
  let f := (i.stalkMap z).hom
  let :=  f.toAlgebra
  have hk₀ : LinearMap.ker (S.map (adj₀.unit.app F)).hom =
      RingHom.ker f • (⊤ : Submodule (Y.presheaf.stalk (i.base z)) (S.obj F)) := by
    rw [← ker_tensor_unit f (i.stalkMap_surjective z) (S.obj F)]
    ext m
    change S.map (adj₀.unit.app F) m = 0 ↔ _
    rw [← ε.map_eq_zero_iff, hunit]
    rfl
  have ht := adj₀.unit_leftAdjointUniq_hom_app adj₁ F
  let β := (pushforward i).map ((adj₀.leftAdjointUniq adj₁).hom.app F)
  have hβ : Function.Injective (S.map β) := ConcreteCategory.bijective_of_isIso _ |>.1
  have hker : LinearMap.ker (S.map (adj₁.unit.app F)).hom =
      LinearMap.ker (S.map (adj₀.unit.app F)).hom := by
    rw [← ht, S.map_comp]
    ext m
    change S.map β (S.map (adj₀.unit.app F) m) = 0 ↔ S.map (adj₀.unit.app F) m = 0
    exact map_eq_zero_iff _ hβ
  exact hker.trans hk₀

end
end AlgebraicGeometry.Scheme.Modules
