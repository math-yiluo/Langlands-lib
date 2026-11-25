/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
import WeilConjectures.AlgebraicGeometry.Curve.tensorGradedAction_projection_first
import WeilConjectures.AlgebraicGeometry.Curve.tensorGradedAction_projection_second

/-! # Projection of homogeneous quotient actions

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, the quotient action on a square-zero ideal.
(blueprint: lem-sc-square-zero-tensor-graded-action-projection).
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

set_option linter.unusedVariables false in
/-- The homogeneous quotient actions commute with the coefficient projections.
This statement concerns only actions: it has no connecting map or resolution presentation.

Source: Stacks Project, Tag 09MS, the graded ideal sequence; Tag 0B8S, first paragraph
of the proof (the quotient action); Tag 01XC, functoriality of the affine cohomology edge.
(blueprint: lem-sc-square-zero-tensor-graded-action-projection).
Proof: The local lift formula uniquely determines an action on I, since its inclusion
in B is mono. Cover an open by opens on which the section in question lifts through
the degreewise adjunction unit. Express local sections of I, after another refinement,
as finite sums of homogeneous sections using the colimit cofan k. The relation
k_inclusion and homogeneous multiplication b_multiply compute the action of each lift
on each summand. The k_projection and k_orthogonal relations extract only the summand
whose degree plus the section degree is n(e+2). Thus s extracts degree n(e+1) and t
extracts degree n. For n=0 both degrees can coincide; the same diagonal projection,
not the off-diagonal relation, applies. The computations commute with restriction and
glue. Apply H^1 to these module morphism identities and use haction. The canonical
coefficient comparisons consist of the ideal-kernel inclusion comparison, the inverse
annihilated-module unit, the inverse affine cohomology edge, and the tensor-degree
comparison. Naturality of each transports the first square to mulTensorPowSection
f F e 1 and the second to rho_F inverse followed by F whiskered with x, preceded by
rho_F on the degree-zero coefficient. The equality hD fixes exactly these comparisons.
Evaluation gives the two equations for every cohomology class, including zero classes
and zero sections, with no use of a product rule for boundaries. -/
theorem tensorGradedAction_projection {X Z : Scheme.{u}} (j : Z ⟶ X)
    [IsClosedImmersion j] (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥)
    (n : ℕ) (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D)
    (e : ℕ) (f : 𝟙_ Z.Modules ⟶ ((tensorPullback j).obj L).tensorPow n)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1))
    (σ : ∀ U : X.Opens, T.C.right.obj.obj (op U) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (T.I.val.obj (op U)))
    (μ : T.C.right.obj.obj (op ⊤) →+* End T.I)
    (ρ : T.C.right.obj.obj (op ⊤) →+*
      Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I))
    (hlocal : ∀ (U : X.Opens) (b : T.B.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      @id (T.B.right.obj.obj (op U))
        (T.i.val.app (op U) (σ U (T.p.right.hom.app (op U) b) y)) =
        b * @id (T.B.right.obj.obj (op U)) (T.i.val.app (op U) y))
    (hrestrict : ∀ (U V : X.Opens) (a : V ⟶ U)
      (g : T.C.right.obj.obj (op U)) (y : T.I.val.obj (op U)),
      T.I.val.map a.op (σ U g y) = σ V (T.C.right.obj.map a.op g) (T.I.val.map a.op y))
    (hglobal : ∀ (g : T.C.right.obj.obj (op ⊤)) (U : X.Opens)
      (y : T.I.val.obj (op U)),
      (μ g).asHom.val.app (op U) y = σ U (T.C.right.obj.map (homOfLE le_top).op g) y)
    (haction : ∀ g : T.C.right.obj.obj (op ⊤), ρ g =
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ g).asHom).hom) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    let N : Z.Modules := ((tensorPullback j).obj L).tensorPow n
    let H := RingedSpace.moduleCohomology Z.toRingedSpace 1
    (∀ z : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I,
      tensorGradedCoefficientProjection T D (e + 1)
        (ρ (tensorGradedSection T D 0 (tensorPowSection f 1)) z) =
      H.map (mulTensorPowSection f F e 1) (tensorGradedCoefficientProjection T D e z)) ∧
    (∀ z : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I,
      tensorGradedCoefficientProjection T D (e + 1) (ρ (tensorGradedSection T D e x) z) =
      H.map ((ρ_ F).inv ≫ F ◁ x)
        (H.map (ρ_ F).hom (tensorGradedCoefficientProjection T D 0 z))) := by
  constructor
  · exact tensorGradedAction_projection_first j L hI n T D hD e f x σ μ ρ
      hlocal hrestrict hglobal haction
  · exact tensorGradedAction_projection_second j L hI n T D hD e f x σ μ ρ
      hlocal hrestrict hglobal haction

end
end AlgebraicGeometry.Scheme.Modules
