/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.QuasiCoherentSymmetricAlgebra
import WeilConjectures.AlgebraicGeometry.Curve.CommAlgebraSheafTensorPowerMaps
import WeilConjectures.AlgebraicGeometry.Curve.InvertibleSymmetricAlgebraCoproduct

/-! # The algebra coproduct of tensor powers of a line bundle

Source: Stacks Project, Tag 09MS, the direct sum in coherent-equation-ses.
(blueprint: lem-sc-tensor-power-algebra-coproduct).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
noncomputable section

/-- Tensor powers of a line bundle have a commutative algebra coproduct, with the
usual multiplication of homogeneous sections.

Source: Stacks Project, Tag 09MS, the direct sum in coherent-equation-ses.
(blueprint: lem-sc-tensor-power-algebra-coproduct).
Proof: Choose local frames for L. On a frame open use the polynomial algebra over
its structure sheaf, with degree-d inclusion sending a coefficient to its monomial
of degree d. If frames differ by a unit v, send the polynomial variable to v times
the variable. These maps are invertible, preserve the structure map, and satisfy
cocycle identities. Glue the algebra sheaves and their homogeneous inclusions.
On each frame the underlying module sheaf is the sheafification of the presheaf
of finite sums of homogeneous terms. Its maps into any module sheaf correspond
uniquely to families of maps from the powers of L. This is the coproduct universal
property; the local universal maps agree on overlaps and hence glue. Multiplication
of monomials gives the displayed identity on frames. The transitions respect it,
and sheaf separation proves it on every open, also for degree zero and the empty
open. This assertion constructs only the algebra on X, with no quotient data. -/
theorem exists_tensorPowerAlgebraCoproduct {X : Scheme.{u}}
    (L : X.Modules) [L.IsInvertible] :
    ∃ (B : X.CommAlgebraSheaf)
      (b : ∀ d : ℕ, L.tensorPow d ⟶ commAlgebraSheafModule X.sheaf B),
      Nonempty (IsColimit (Cofan.mk (commAlgebraSheafModule X.sheaf B) b)) ∧
      ∀ (U : X.Opens) (a d : ℕ) (s : Γ(L.tensorPow a, U))
        (t : Γ(L.tensorPow d, U)),
        (show B.right.obj.obj (op U) from (b a).app U s) *
          (show B.right.obj.obj (op U) from (b d).app U t) =
          (show B.right.obj.obj (op U) from
            (b (a + d)).app U ((L.tensorPowAddIso a d).inv.app U (tmulSection s t))) := by
  obtain ⟨B, j, _, _, hAffine⟩ := exists_quasiCoherentSymmetricAlgebra X L
  obtain ⟨b, hZero, hOne, hMul⟩ := exists_commAlgebraSheaf_tensorPower_maps L B j
  exact ⟨B, b, isColimit_invertible_symmetricAlgebra_cofan
    L B j b hAffine hZero hOne hMul, hMul⟩

end
end AlgebraicGeometry.Scheme.Modules
