/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedPresentation
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedQuotientMultiply
import WeilConjectures.AlgebraicGeometry.SquareZeroTensorSectionProductComparison

/-! # Homogeneous sections and their product in a graded presentation

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-product-projection).
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

/-- Include the transported section in its homogeneous degree.
Source: Stacks Project, Tag 09MS, the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-product-projection). -/
def tensorGradedSection {X Z : Scheme.{u}} {j : Z ⟶ X} [IsClosedImmersion j]
    {L : X.Modules} {n : ℕ} (T : TensorGradedPresentation j L)
    (D : TensorBoundaryComparisonData j L n) (e : ℕ)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1)) :
    T.C.right.obj.obj (op ⊤) :=
  (T.c (n * (e + 1))).app ⊤ ((x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)))

/-- Take cohomology of a degree projection and then the inverse coefficient comparison.
This is an explicit composite, with no object selected from an unproved theorem.
Source: Stacks Project, Tag 09MS, the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-product-projection). -/
def tensorGradedCoefficientProjection {X Z : Scheme.{u}} {j : Z ⟶ X}
    [IsClosedImmersion j] {L : X.Modules} {n : ℕ}
    (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n) (e : ℕ) :
    ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I) →+
      (RingedSpace.moduleCohomology Z.toRingedSpace 1).obj
        (show Z.Modules from (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n) ⊗
          (((tensorPullback j).obj L).tensorPow n).tensorPow e) :=
  (Iso.addCommGroupIsoToAddEquiv (D.k e)).symm.toAddMonoidHom.comp
    (((RingedSpace.moduleCohomology X.toRingedSpace 1).map
      (T.degree (n * (e + 1))).τ₁).hom.toAddMonoidHom)

/-- Evaluation of the explicit additive coefficient projection.
Source: Stacks Project, Tag 09MS, the graded ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-product-projection). -/
theorem tensorGradedCoefficientProjection_apply {X Z : Scheme.{u}} {j : Z ⟶ X}
    [IsClosedImmersion j] {L : X.Modules} {n : ℕ}
    (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n) (e : ℕ)
    (z : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I) :
    tensorGradedCoefficientProjection T D e z =
      (Iso.addCommGroupIsoToAddEquiv (D.k e)).symm
        (((RingedSpace.moduleCohomology X.toRingedSpace 1).map
          (T.degree (n * (e + 1))).τ₁).hom z) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simp only [tensorGradedCoefficientProjection, AddMonoidHom.comp_apply,
        AddEquiv.coe_toAddMonoidHom]
  rfl

attribute [irreducible] tensorGradedCoefficientProjection

/-- The raw homogeneous multiplication identity.
Source: Stacks Project, Tag 09MS, multiplication in the direct-sum algebra.
(blueprint: lem-sc-square-zero-tensor-graded-product-projection-raw).
Proof: Work locally where the invertible module is free of rank one, lift both quotient
sections through the degreewise adjunction unit, apply `b_multiply`, and use `b_quotient`
and `c_projection`. Tensor-power associativity and the unitors identify the resulting
section with the displayed transported tensor product; local equality glues by sheaf
separation. -/
theorem tensorGradedSection_product_raw {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1)) :
    tensorGradedSection T D 0 (tensorPowSection f 1) * tensorGradedSection T D e x =
      (T.c (n * ((e + 1) + 1))).app ⊤
        ((((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x)) ≫ (D.a (e + 1)).inv).app ⊤
          (1 : Γ(Z, ⊤))) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      unfold tensorGradedSection
  have hm := tensorGradedQuotient_multiply j L T (n * (0 + 1)) (n * (e + 1))
    ((tensorPowSection f 1 ≫ (D.a 0).inv).app ⊤ (1 : Γ(Z, ⊤)))
    ((x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)))
  simp only [tensorGradedAlgebraSection] at hm
  rw [hm]
  have hdeg : n * (0 + 1) + n * (e + 1) = n * ((e + 1) + 1) := by
    simp only [Nat.mul_add, Nat.mul_one, Nat.zero_add]
    omega
  have hc := tensorSectionProduct_comparison j L hI n D hD e f x hdeg
  generalize hs : (((tensorPullback j).map
    (L.tensorPowAddIso (n * (0 + 1)) (n * (e + 1))).inv).app ⊤
    ((boundaryPullbackTensorIso j (L.tensorPow (n * (0 + 1)))
      (L.tensorPow (n * (e + 1)))).inv.app ⊤
      (tmulSection
        ((tensorPowSection f 1 ≫ (D.a 0).inv).app ⊤ (1 : Γ(Z, ⊤)))
        ((x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)))))) = s at hc ⊢
  rw [← hc]
  clear hc hs hm
  generalize n * (0 + 1) + n * (e + 1) = a at *
  generalize n * ((e + 1) + 1) = b at *
  subst b
  simp
  rfl

/-- Applying the degree quotient projection to the raw homogeneous product identity.
Source: Stacks Project, Tag 09MS, the projection relation for the graded quotient.
(blueprint: lem-sc-square-zero-tensor-graded-product-projection-projection). -/
theorem tensorGradedSection_projection_of_raw {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (hraw : tensorGradedSection T D 0 (tensorPowSection f 1) *
      tensorGradedSection T D e x =
      (T.c (n * ((e + 1) + 1))).app ⊤
        ((((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x)) ≫ (D.a (e + 1)).inv).app ⊤
          (1 : Γ(Z, ⊤)))) :
    Hom.app (T.q (n * ((e + 1) + 1))) ⊤
      (tensorGradedSection T D 0 (tensorPowSection f 1) * tensorGradedSection T D e x) =
      ((((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x)) ≫ (D.a (e + 1)).inv).app ⊤
        (1 : Γ(Z, ⊤))) := by
  have _ := hD
  rw [hraw]
  exact congrArg (fun φ ↦ φ.app ⊤
    (((((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x)) ≫ (D.a (e + 1)).inv).app ⊤)
      (1 : Γ(Z, ⊤)))) (T.c_projection (n * ((e + 1) + 1)))

/-- Projecting a product of the two homogeneous sections gives the transported tensor
product section. No cohomology boundary, action, or derivation identity occurs here.

Source: Stacks Project, Tag 09MS, multiplication in the direct-sum algebra.
(blueprint: lem-sc-square-zero-tensor-graded-product-projection).
Proof: Work locally where L is free of rank one and lift each quotient section through
the degreewise adjunction unit, which is an epimorphism. The compatibility b_quotient
identifies its homogeneous image with the image of its homogeneous lift under p.
Apply the algebra map p to b_multiply. The c_projection identity extracts degree
n+n(e+1)=n(e+2). The canonical monoidal pullback comparison and tensor-power multiplication
identify this product with lambda inverse followed by f tensor x. For s, tensorPowSection
f 1 includes exactly the degree-one right unitor needed by a_0. Changing a lift changes
it by a kernel section and hence does not change the quotient product. These identities
hold locally and glue by sheaf separation. The same argument for n=0 uses the unit
summand twice; it does not require the two summands to have different degrees. -/
theorem tensorGradedSection_product {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1)) :
    Hom.app (T.q (n * ((e + 1) + 1))) ⊤
      (tensorGradedSection T D 0 (tensorPowSection f 1) * tensorGradedSection T D e x) =
      ((((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x)) ≫ (D.a (e + 1)).inv).app ⊤
        (1 : Γ(Z, ⊤))) := by
  apply tensorGradedSection_projection_of_raw j L hI n T D hD e f x
  exact tensorGradedSection_product_raw j L hI n T D hD e f x

end
end AlgebraicGeometry.Scheme.Modules
