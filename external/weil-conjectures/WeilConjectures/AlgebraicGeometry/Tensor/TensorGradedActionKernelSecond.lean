/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorBoundaryKernelMapNaturality
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedQuotientActionHomogeneous
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedActionKernelSecondDiagonal

/-! # Homogeneous quotient multiplication on degree kernels

Source: Stacks Project, Tags 09MS and 0B8S.
(blueprint: lem-sc-tensor-graded-action-kernel-second).
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

/-- Multiplication by x followed by the output projection factors through the input
projection and the explicit transported tensor-by-x map, already on sheaves.
Source: Stacks Project, Tag 09MS, coherent-equation-ses and the graded direct sum;
Tag 0B8S, quotient multiplication on the square-zero ideal.
(blueprint: lem-sc-tensor-graded-action-kernel-second).
Proof: First substitute hD, so the section comparison is boundarySectionDegreeIso.
Since the inclusion of the ideal is mono, the local lift formula fixes the
quotient action. Check the asserted morphism identity after each coproduct injection
T.k d, which jointly determine a morphism by T.k_colimit. Locally trivialize L and
lift the quotient section x through the degreewise quotient unit in degree n(e+1).
The relation b_quotient identifies its image with tensorGradedSection. The relations
k_inclusion and b_multiply compute multiplication on the degree-d ideal summand
as ideal tensor multiplication in degree d+n(e+1). Project to n(e+2). If d is not n,
the output is zero by k_orthogonal; the input projection is also zero. If d=n,
k_projection identifies both sides with multiplication by x on the ideal coefficient.
In a trivialization with generator ell, write the kernel inclusion of y as
r times ell^d with r in J, and a lift of x as a times ell^(n(e+1)). The product
is ar times ell^(d+n(e+1)). The inclusion equation of boundaryIdealKernelIso
identifies y with r; the annihilated-module unit reduces the coefficient to Z.
The recursive tensor-power and pullback comparisons send each tensor of ell
to the same tensor of its pullback, with the unitors in exponent zero. Thus
boundaryCoefficientDegreeIso identifies the diagonal product with F tensor x,
and conjugating by the kernel-to-pushforward isomorphisms gives the stated map.
Changing a lift by a kernel section contributes zero,
by squareZero. These calculations hold on an open cover and glue by sheaf separation;
hglobal identifies the sectionwise action with the given module endomorphism.
For n=0 the output degree is d, so exactly d=0 survives; no distinct-degree assumption
is made. The zero section and zero ideal give zero maps on both sides. -/
theorem tensorGradedAction_kernel_second {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).asHom.val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    (μ (tensorGradedSection T D e x)).asHom ≫ (T.degree (n * ((e + 1) + 1))).τ₁ =
      (T.degree (n * (0 + 1))).τ₁ ≫
        tensorBoundaryKernelMap j L hI n 0 (e + 1) (F ◁ x) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      dsimp only
      apply Cofan.IsColimit.hom_ext T.k_colimit
      intro d
      change T.k d ≫ ((μ (tensorGradedSection T D e x)).asHom ≫ _) = T.k d ≫ (_ ≫ _)
      by_cases hd : d = n * (0 + 1)
      · subst d
        rw [← Category.assoc,
          tensorGradedAction_kernel_second_diagonal j L hI n T D hD e x σ μ hlocal hglobal,
          Category.assoc, T.k_projection, Category.comp_id,
          ← Category.assoc, T.k_projection, Category.id_comp]
      · obtain ⟨v, hv⟩ := tensorGradedQuotientAction_homogeneous j L T
          (n * (e + 1)) d ((x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)))
          σ μ hlocal hglobal
        have hdeg : d + n * (e + 1) ≠ n * ((e + 1) + 1) := by
          simp only [Nat.mul_add, Nat.mul_one] at *
          omega
        change T.k d ≫ (μ (tensorGradedSection T D e x)).asHom = _ at hv
        rw [← Category.assoc, hv, Category.assoc, T.k_orthogonal _ _ hdeg,
          comp_zero, ← Category.assoc, T.k_orthogonal _ _ hd, zero_comp]

end
end AlgebraicGeometry.Scheme.Modules
