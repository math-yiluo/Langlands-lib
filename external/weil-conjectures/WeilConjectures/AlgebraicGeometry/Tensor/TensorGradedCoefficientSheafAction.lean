/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
import WeilConjectures.AlgebraicGeometry.Tensor.TensorCoefficientActionOnSummand
import WeilConjectures.AlgebraicGeometry.Tensor.TensorCoefficientActionSupport

/-! # The homogeneous coefficient action before cohomology

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, the quotient action on a square-zero ideal.
(blueprint: lem-sc-square-zero-tensor-graded-coefficient-sheaf-action).
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

/-- Identify the pushed-forward coefficient module with the degreewise kernel.
The map uses only the explicit tensor-degree comparison, the inverse annihilated-module
unit, and the ideal-kernel comparison determined by its inclusion equation.
Source: Stacks Project, Tags 09MS and 08KS.
(blueprint: lem-sc-square-zero-tensor-graded-coefficient-sheaf-action). -/
def tensorCoefficientSheafIso {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n e : ℕ) :
    (pushforward j).obj ((tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
      (((tensorPullback j).obj L).tensorPow n).tensorPow e) ≅
      kernel (tensorGradedUnit j (L.tensorPow (n * (e + 1)))) := by
  have := square_zero_ideal_tensor_unit_isIso j L hI (n * (e + 1))
  exact (pushforward j).mapIso (boundaryCoefficientDegreeIso j L n e).symm ≪≫
    (asIso ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
      (j.ker.toModules ⊗ L.tensorPow (n * (e + 1))))).symm ≪≫
    boundaryIdealKernelIso j (L.tensorPow (n * (e + 1)))

/-- Transport an explicit coefficient morphism to the degreewise kernels.
Source: Stacks Project, Tag 09MS, the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-coefficient-sheaf-action). -/
def tensorCoefficientKernelMap {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n a b : ℕ)
    (v : (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow a ⟶
      (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
        (((tensorPullback j).obj L).tensorPow n).tensorPow b) :
    kernel (tensorGradedUnit j (L.tensorPow (n * (a + 1)))) ⟶
      kernel (tensorGradedUnit j (L.tensorPow (n * (b + 1)))) :=
  (tensorCoefficientSheafIso j L hI n a).inv ≫ (pushforward j).map v ≫
    (tensorCoefficientSheafIso j L hI n b).hom

attribute [irreducible] tensorCoefficientSheafIso tensorCoefficientKernelMap

/-- The first homogeneous action square, as an equality of sheaf morphisms.
There is no cohomology or cohomology action in this statement.

Source: Stacks Project, Tag 09MS, coherent-equation-ses and the graded direct sum;
Tag 0B8S, cohomology-lemma-boundary-derivation-over-cup-product, first proof paragraph.
(blueprint: lem-sc-square-zero-tensor-graded-coefficient-sheaf-action).
Proof: Cancel the monomorphism i to compute the quotient action using hlocal.
Locally lift the restriction of the homogeneous section through the tensor-pullback
unit in degree n; the unit is epi by the closed-immersion unit quotient theorem.
Use b_quotient to identify its image under p. Precompose the proposed square with
k d for every d. By k_inclusion and b_multiply, multiplication by the chosen lift
has degree n+d. If d differs from n(e+1), k_orthogonal kills its projection to
n(e+2); otherwise k_projection leaves exactly the product on that coefficient.
The ideal-kernel inclusion equation identifies this product with tensoring by the
lift. The inverse annihilated-module unit and tensor-degree comparisons identify
it with pushforward of mulTensorPowSection f F e 1. A different local lift changes
the product by the product of two kernel sections, zero by squareZero. Naturality
of these comparisons and hrestrict glue the local equalities; hglobal identifies
the global endomorphism. Finally k_colimit.hom_ext proves the square from its
restrictions to all k d. When n=0, n+d=d and the same projection calculation uses
only the diagonal identity for d=0 and orthogonality for d≠0. No positive-degree,
affineness, or nonzero-section assumption is needed. -/
theorem tensorGradedCoefficient_sheaf_action {X Z : Scheme.{u}} (j : Z ⟶ X)
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
    (μ (tensorGradedSection T D 0 (tensorPowSection f 1))).asHom ≫
        (T.degree (n * ((e + 1) + 1))).τ₁ =
      (T.degree (n * (e + 1))).τ₁ ≫
        tensorCoefficientKernelMap j L hI n e (e + 1)
          (mulTensorPowSection f ((tensorPullback j).obj
            (j.ker.toModules ⊗ L.tensorPow n)) e 1) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  apply Cofan.IsColimit.hom_ext T.k_colimit
  intro d
  change T.k d ≫ _ = T.k d ≫ _
  by_cases hd : d = n * (e + 1)
  · subst d
    have h := tensorGradedCoefficient_action_on_summand j L hI n T D hD e f
      σ μ hlocal hrestrict hglobal
    simp only [← Category.assoc] at h
    have hdiag : T.k (n * (e + 1)) ≫
        (μ (tensorGradedSection T D 0 (tensorPowSection f 1))).asHom =
      tensorCoefficientKernelMap j L hI n e (e + 1)
        (mulTensorPowSection f ((tensorPullback j).obj
          (j.ker.toModules ⊗ L.tensorPow n)) e 1) ≫
        T.k (n * ((e + 1) + 1)) := by
      simpa only [tensorCoefficientKernelMap, tensorCoefficientSheafIso,
        Category.assoc] using h
    rw [← Category.assoc, hdiag, Category.assoc, T.k_projection]
    rw [← Category.assoc, T.k_projection]
    simp
  · obtain ⟨v, hv⟩ := tensorGradedCoefficient_action_support j L hI n T D hD d f
      σ μ hlocal hrestrict hglobal
    have hdegree : n + d ≠ n * ((e + 1) + 1) := by
      rw [Nat.mul_add]
      omega
    rw [← Category.assoc, hv, Category.assoc, T.k_orthogonal _ _ hdegree]
    rw [← Category.assoc, T.k_orthogonal _ _ hd]
    simp

end
end AlgebraicGeometry.Scheme.Modules
