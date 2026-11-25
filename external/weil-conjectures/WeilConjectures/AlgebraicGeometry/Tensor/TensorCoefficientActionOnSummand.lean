/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
import WeilConjectures.AlgebraicGeometry.Tensor.TensorIdealSectionCoefficientComparison

/-! # Action on one ideal summand equals tensor multiplication

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, the quotient action on a square-zero ideal.
(blueprint: lem-sc-tensor-coefficient-action-on-summand).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
attribute [local irreducible] RingedSpace.moduleCohomology
  boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
noncomputable section

/-- On one source summand the homogeneous action is the canonical tensor multiplication.
Source: Stacks Project, Tag 09MS, graded ideal sequence; Tag 0B8S, quotient action.
(blueprint: lem-sc-tensor-coefficient-action-on-summand).
Proof: On an open trivializing L, locally lift the restricted section f through the
closed-immersion unit in degree n. By b_quotient its image in C is the restriction
of tensorGradedSection. Apply hlocal to this lift and the image under k of an ideal
tensor section. Use k_inclusion and b_multiply to compute their product in degree
n+n(e+1). Under boundaryIdealKernelIso its inclusion is multiplication of the ideal
factor and the tensor-power factor. The inverse unit on the annihilated ideal and
boundaryCoefficientDegreeIso identify this operation with pushforward of
mulTensorPowSection f F e 1. These comparisons are canonical: uniqueness of the
adjunction comparison respects the monoidal tensor product, and the ideal-kernel
comparison is fixed by its inclusion equation. Cancel the monic i to obtain the
identity in I. Changing the lift adds a kernel element, whose product with the
ideal section is zero by squareZero. Restriction compatibility hrestrict and
hglobal identify these local calculations with the specified global action.
Sheaf separation gives the asserted morphism equality. This also covers n=0:
the monoidal unit comparisons give the same product in degree zero. -/
theorem tensorGradedCoefficient_action_on_summand {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hrestrict : ∀ (U V : X.Opens) (a : V ⟶ U)
      (g : T.C.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      T.I.val.map a.op (σ U g y) = σ V (T.C.right.obj.map a.op g) (T.I.val.map a.op y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).asHom.val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y) :
    letI := square_zero_ideal_tensor_unit_isIso j L hI (n * (e + 1))
    letI := square_zero_ideal_tensor_unit_isIso j L hI (n * ((e + 1) + 1))
    T.k (n * (e + 1)) ≫ (μ (tensorGradedSection T D 0 (tensorPowSection f 1))).asHom =
      ((pushforward j).mapIso (boundaryCoefficientDegreeIso j L n e).symm ≪≫
      (asIso ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (j.ker.toModules ⊗ L.tensorPow (n * (e + 1))))).symm ≪≫
      boundaryIdealKernelIso j (L.tensorPow (n * (e + 1)))).inv ≫
        (pushforward j).map
          (mulTensorPowSection f ((tensorPullback j).obj
            (j.ker.toModules ⊗ L.tensorPow n)) e 1) ≫
      ((pushforward j).mapIso (boundaryCoefficientDegreeIso j L n (e + 1)).symm ≪≫
      (asIso ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (j.ker.toModules ⊗ L.tensorPow (n * ((e + 1) + 1))))).symm ≪≫
      boundaryIdealKernelIso j (L.tensorPow (n * ((e + 1) + 1)))).hom ≫
        T.k (n * ((e + 1) + 1)) := by
  have := square_zero_ideal_tensor_unit_isIso j L hI (n * (e + 1))
  have := square_zero_ideal_tensor_unit_isIso j L hI (n * ((e + 1) + 1))
  have _ := hrestrict
  have hdeg : n * (e + 1) + n * (0 + 1) = n * ((e + 1) + 1) := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.zero_add]
  have hm := tensorHomogeneousKernel_action j L hI T
    (n * (0 + 1)) (n * (e + 1)) (n * ((e + 1) + 1)) hdeg
    (tensorPowSection f 1 ≫ (D.a 0).inv) σ μ hlocal hglobal
  have hc := tensorIdealSectionMultiply_coefficient_comparison j L hI n D hD e f hdeg
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [tensorGradedSection, tensorHomogeneousKernelMap, hc, Functor.map_comp,
        Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom, Functor.mapIso_inv,
        Functor.mapIso_hom, asIso_inv, asIso_hom, Category.assoc] using hm

end
end AlgebraicGeometry.Scheme.Modules
