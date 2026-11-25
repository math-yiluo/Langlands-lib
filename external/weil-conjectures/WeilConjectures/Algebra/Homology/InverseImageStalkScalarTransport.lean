/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.Topology.Sheaves.Sheafify
import WeilConjectures.Algebra.Homology.InverseImageStalkScalarTransportBeta
import WeilConjectures.Algebra.Homology.InverseImageStalkScalarTransportNaturality

/-!
# Scalar transport for inverse-image stalks on ringed spaces

Source: Stacks Project, Sheaves, Tags 008H and 0098.
(blueprint: lem-pc-ringed-inverse-image-stalk-scalar-transport).
-/

@[expose] public section

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry
open scoped ChangeOfRings

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Transport tensor scalars through the inverse-image ring and module stalk comparisons.
Source: Stacks Project, Sheaves, Tag 0098, proof using Tag 008H.
(blueprint: lem-pc-ringed-inverse-image-stalk-scalar-transport).

Proof: the canonical ring comparison is the presheaf inverse-image stalk map followed
by the stalk of sheafification. Both factors are isomorphisms. The analogous abelian
comparison c is an isomorphism, natural in the module. Represent a scalar and vector
on a common neighborhood. The germ formulas and semilinearity of the inverse-image
unit show c(r m) = k(r)c(m). Write psi for the stalk of alpha, so rho = psi k.
The forward balanced tensor map sends b tensor m to b tensor c(m); balancing follows
from psi(k(r)) = rho(r). The inverse sends b tensor n to b tensor c inverse(n).
Its balancing follows from c inverse(s n) = k inverse(s)c inverse(n) and
rho(k inverse(s)) = psi(s). Both maps are linear over the target stalk ring and
are inverse on pure tensors, hence everywhere. Naturality of c proves the displayed
square on pure tensors; additive generation gives equality of linear maps.
There is no flatness assumption. Zero rings and zero modules satisfy the same
identities; for an empty source space there is no point x. -/
theorem exists_ringed_inverseImage_stalk_scalar_transport
    (X Y : RingedSpace.{u}) (f : X.carrier ⟶ Y.carrier)
    (α : TopCat.Sheaf.inverseImageRing f Y.sheaf ⟶ X.sheaf) (x : X) :
    let k := TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))
    let ψ : TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.carrier)
        (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x →+* X.presheaf.stalk x :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α.hom).hom
    let ρ := ψ.comp k.hom
    ∃ (c : ∀ M : RingedSpace.Modules Y,
        (RingedSpace.moduleStalkFunctor Y (f x)).obj M ≃+
          TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
            (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf x)
      (β : ∀ M : RingedSpace.Modules Y,
        (ModuleCat.extendScalars ρ).obj
            ((RingedSpace.moduleStalkFunctor Y (f x)).obj M) ≅
          (ModuleCat.extendScalars ψ).obj
            (ModuleCat.of (TopCat.Presheaf.stalk (C := CommRingCat.{u})
              (X := X.carrier) (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x)
              (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
                (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf x))),
      (∀ (M : RingedSpace.Modules Y) (b : X.presheaf.stalk x)
        (m : (RingedSpace.moduleStalkFunctor Y (f x)).obj M),
        (β M).hom (b ⊗ₜ[_, ρ] m) = b ⊗ₜ[_, ψ] (c M m)) ∧
      (∀ (M N : RingedSpace.Modules Y) (a : M ⟶ N)
        (m : (RingedSpace.moduleStalkFunctor Y (f x)).obj M),
        c N ((RingedSpace.moduleStalkFunctor Y (f x)).map a m) =
          PresheafOfModules.stalkAddMap
            (TopCat.Sheaf.inverseImageModuleMap f Y.sheaf M a).val (c M m)) := by
  dsimp
  obtain ⟨c, hs, hn⟩ := exists_inverseImage_stalk_comparison_natural X Y f x
  have : IsIso (TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x) :=
    (TopCat.Presheaf.stalkPullbackIso CommRingCat.{u} f Y.presheaf x).isIso_hom
  have := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x CommRingCat.{u}
    ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf)
  let k : Y.presheaf.stalk (f x) ⟶
      TopCat.Presheaf.stalk (C := CommRingCat.{u}) (X := X.carrier)
        (TopCat.Sheaf.inverseImageRing f Y.sheaf).obj x :=
    TopCat.Presheaf.stalkPullbackHom CommRingCat.{u} f Y.presheaf x ≫
      (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map
        (toSheafify (Opens.grothendieckTopology X)
          ((TopCat.Presheaf.pullback CommRingCat.{u} f).obj Y.presheaf))
  have hk := ConcreteCategory.bijective_of_isIso k
  let ψ := ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map α.hom).hom
  have hβ := fun M ↦ exists_inverseImage_stalk_scalar_transport_beta k.hom hk ψ
    ((RingedSpace.moduleStalkFunctor Y (f x)).obj M)
    (ModuleCat.of _ (TopCat.Presheaf.stalk (C := Ab.{u}) (X := X.carrier)
      (TopCat.Sheaf.inverseImageModule f Y.sheaf M).val.presheaf x)) (c M) (hs M)
  choose β hβ using hβ
  exact ⟨c, β, hβ, hn⟩

end
