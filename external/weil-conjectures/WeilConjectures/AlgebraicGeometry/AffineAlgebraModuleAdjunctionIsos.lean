/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionFiniteLimits
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionUnitIso
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionCounitIso

/-! # The underived affine algebra adjunction

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- Tensor pullback for the direct-image algebra is exact, and its adjunction
maps are isomorphisms on quasi-coherent modules.
Source: Stacks Project, Tag 0AVW, proof, and Tag 01SB,
morphisms-lemma-affine-equivalence-modules.
(blueprint: lem-sc-affine-algebra-module-adjunction-isos).

Proof: Cover Y by affine opens Spec B with inverse images Spec A. At a point p
above q the ring map for g is A localized at q to A localized at p. It is a
localization and hence flat. Tensor pullback is therefore exact, as can be checked
on stalks; it preserves finite limits and, being a left adjoint, finite colimits.
The underived tensor pullback agrees with the two tensor operations of
Scheme.Modules.affine_module_correspondence, by associativity of tensor products.
Its counit is that theorem's alpha: the map from the tensor pullback of the
pushforward to the original sheaf. Its unit is that theorem's beta: the map
adjoint to the tensor unit. Their components on quasi-coherent modules are
isomorphisms by the correspondence. For an arbitrary P and adjunction a to the
fixed moduleDirectImage g, uniqueness of left adjoints supplies the natural
isomorphism from P to tensor pullback that is compatible with both adjunctions.
It transports finite-limit preservation and the unit and counit isomorphisms.
No surjectivity of f, finiteness of its algebra, or nonzero ring is needed.
For empty schemes or zero modules the comparisons are between zero objects;
for the identity morphism they are the identity comparisons. -/
theorem affine_algebra_module_adjunction_isos
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)) :
    Limits.PreservesFiniteLimits P ∧
    (∀ M : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)),
      M.IsQuasicoherent → IsIso (a.unit.app M)) ∧
    (∀ K : SheafOfModules.{v} (moduleRings X.toRingedSpace),
      K.IsQuasicoherent → IsIso (a.counit.app K)) := by
  let G := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  let : G.IsRightAdjoint := a.isRightAdjoint
  let b := Adjunction.ofIsRightAdjoint G
  let : Limits.PreservesFiniteLimits G.leftAdjoint :=
    affine_algebra_module_adjunction_preserves_finite_limits f
  refine ⟨Limits.preservesFiniteLimits_of_natIso (b.leftAdjointUniq a), ?_, ?_⟩
  · intro M hM
    have hunit : IsIso (b.unit.app M) := affine_algebra_module_adjunction_unit_iso f M hM
    let := hunit
    rw [← b.unit_leftAdjointUniq_hom_app a M]
    infer_instance
  · intro K hK
    have hcounit : IsIso (b.counit.app K) := affine_algebra_module_adjunction_counit_iso f K hK
    let := hcounit
    rw [← a.leftAdjointUniq_hom_app_counit b K]
    infer_instance

end AlgebraicGeometry
