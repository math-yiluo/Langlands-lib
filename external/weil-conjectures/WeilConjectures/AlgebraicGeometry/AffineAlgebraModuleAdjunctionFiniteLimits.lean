/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import WeilConjectures.AlgebraicGeometry.RingedSpaceTensorPullbackUnderived
import WeilConjectures.AlgebraicGeometry.AffineAlgebraTensorPullbackExact
/-! # Canonical affine algebra module adjunction component

Source: Stacks Project, Tags 0AVW and 01SB. -/

@[expose] public section

noncomputable section
universe v
open CategoryTheory
namespace AlgebraicGeometry
/-- The canonical affine algebra adjunction component.
Source: Stacks Project, Tags 0AVW and 01SB.
(blueprint: new-affine-algebra-module-finite-limits).

Proof: Identify the canonical left adjoint with tensor pullback using the tensor Hom adjunction.
On an
affine open Spec B with inverse image Spec A, the stalk map at p over q is the localization A
localized away from q to A_p, hence flat. Tensor pullback preserves kernels by the exact,
jointly conservative stalk functors. It preserves finite products because tensor preserves
finite direct sums. Kernels and finite products imply preservation of finite limits in an
abelian category. Transport along the unique isomorphism of left adjoints. Empty schemes and
zero modules cause no exceptions.
-/
theorem affine_algebra_module_adjunction_preserves_finite_limits
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [(RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).IsRightAdjoint] :
    Limits.PreservesFiniteLimits
      (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)).leftAdjoint := by
  obtain ⟨P, h, hm, _, ⟨adj⟩⟩ :=
    RingedSpace.exists_tensorModulePullback (toDirectImageAlgebraSpace f)
  have : Limits.PreservesFiniteLimits P :=
    (affine_algebra_tensorModulePullback_exact f P h hm).1
  exact Limits.preservesFiniteLimits_of_natIso
    (adj.leftAdjointUniq (Adjunction.ofIsRightAdjoint
      (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))))
end AlgebraicGeometry
