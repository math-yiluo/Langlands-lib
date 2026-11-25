/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
import WeilConjectures.AlgebraicGeometry.Tensor.TensorGradedActionKernelSecond

/-! # Projection of homogeneous quotient actions

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, the quotient action on a square-zero ideal.
(blueprint: lem-sc-square-zero-tensor-graded-action-projection-second).
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
/-- Compatibility of the degree-n(e+1) section x on the degree-n coefficient.

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence;
Tag 0B8S, quotient multiplication on the square-zero ideal;
Tag 01XC, naturality of the affine cohomology comparison.
(blueprint: lem-sc-square-zero-tensor-graded-action-projection-second).
Proof: The inclusion i is mono by short exactness, so hlocal uniquely determines the
quotient action. Lift the homogeneous quotient section locally through the degreewise
unit. On each kernel summand k_d, use k_inclusion and b_multiply to compute multiplication
by this lift. Project to degree n(e+2); k_projection gives the diagonal term and
k_orthogonal kills every other input degree. The surviving input degree is
n. If n=0 this is a diagonal calculation in degree zero; no distinct-degree
assumption is needed. The colimit cofan k determines the map from these summands.
Changing a lift by a kernel section changes no product, since the ideal is square zero.
Restriction compatibility glues these local identities, and hglobal identifies the
resulting global action with mu. Apply H^1 and use haction. Transport the resulting
square through the canonical ideal-kernel, annihilated-module unit, affine cohomology,
and tensor-degree comparisons fixed by hD. Naturality identifies the transported map
with the right-unitor inverse followed by tensoring with x;
the degree-zero comparison contributes the right unitor on the input.
The identity holds for every class, including the zero class and zero section. -/
theorem tensorGradedAction_projection_second {X Z : Scheme.{u}} (j : Z ⟶ X)
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
      tensorGradedCoefficientProjection T D (e + 1) (ρ (tensorGradedSection T D e x) z) =
      H.map ((ρ_ F).inv ≫ F ◁ x)
        (H.map (ρ_ F).hom (tensorGradedCoefficientProjection T D 0 z))) := by
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      subst D
      dsimp only
      intro z
      let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
      let HX := RingedSpace.moduleCohomology X.toRingedSpace 1
      let HZ := RingedSpace.moduleCohomology Z.toRingedSpace 1
      have hk := tensorGradedAction_kernel_second j L hI n T
        (canonicalTensorBoundaryComparisons j L hI n) rfl e x σ μ hlocal hglobal
      let w := (HX.map (T.degree (n * (0 + 1))).τ₁).hom z
      let v := F ◁ x
      let m := tensorBoundaryKernelMap j L hI n 0 (e + 1) v
      let D0 := canonicalTensorBoundaryComparisons j L hI n
      have hp (r : ℕ) (y : HX.obj T.I) :
          tensorGradedCoefficientProjection T D0 r y =
            (boundaryCoefficientCohomologyIso j L hI n r).inv
              ((HX.map (T.degree (n * (r + 1))).τ₁).hom y) := by
        have h := tensorGradedCoefficientProjection_apply T D0 r y
        have hk : D0.k r = boundaryCoefficientCohomologyIso j L hI n r := by
          unfold D0 canonicalTensorBoundaryComparisons
          rfl
        calc
          _ = (D0.k r).addCommGroupIsoToAddEquiv.symm
              ((HX.map (T.degree (n * (r + 1))).τ₁).hom y) := h
          _ = _ := congrArg (fun t ↦ t.addCommGroupIsoToAddEquiv.symm
              ((HX.map (T.degree (n * (r + 1))).τ₁).hom y)) hk
      have hh : (HX.map (T.degree (n * ((e + 1) + 1))).τ₁).hom
          ((HX.map (μ (tensorGradedSection T D0 e x)).asHom).hom z) =
          (HX.map m).hom w := by
        let t := tensorGradedSection T D0 e x
        let p0 := (T.degree (n * (0 + 1))).τ₁
        let p1 := (T.degree (n * ((e + 1) + 1))).τ₁
        have hk' : (μ t).asHom ≫ p1 = p0 ≫ m := hk
        calc
          (HX.map p1).hom ((HX.map (μ t).asHom).hom z) =
              (HX.map ((μ t).asHom ≫ p1)).hom z :=
            congrArg (fun g ↦ g.hom z) (HX.map_comp (μ t).asHom p1).symm
          _ = (HX.map (p0 ≫ m)).hom z :=
            congrArg (fun g ↦ (HX.map g).hom z) hk'
          _ = (HX.map m).hom ((HX.map p0).hom z) :=
            congrArg (fun g ↦ g.hom z) (HX.map_comp p0 m)
      have hn : (boundaryCoefficientCohomologyIso j L hI n (e + 1)).inv
          ((HX.map m).hom w) =
          HZ.map v ((boundaryCoefficientCohomologyIso j L hI n 0).inv w) := by
        have h := tensorBoundaryKernelMap_naturality j L hI n 0 (e + 1) v
        exact congrArg (fun g ↦ g w) h
      have hr (y : HZ.obj (show Z.Modules from F ⊗ 𝟙_ Z.Modules)) :
          HZ.map v y = HZ.map ((ρ_ F).inv ≫ v) (HZ.map (ρ_ F).hom y) := by
        have h : (ρ_ F).hom ≫ ((ρ_ F).inv ≫ v) = v :=
          Iso.hom_inv_id_assoc (ρ_ F) v
        have hc := congrArg (fun g ↦ HZ.map g) h
        have he := congrArg (fun g ↦ g y) hc
        exact (show HZ.map ((ρ_ F).inv ≫ v) (HZ.map (ρ_ F).hom y) =
          HZ.map v y by
            simpa only [Functor.map_comp, ModuleCat.comp_apply] using he).symm
      calc
        tensorGradedCoefficientProjection T D0 (e + 1)
            (ρ (tensorGradedSection T D0 e x) z) =
            tensorGradedCoefficientProjection T D0 (e + 1)
              ((HX.map (μ (tensorGradedSection T D0 e x)).asHom).hom z) :=
          congrArg (fun g ↦ tensorGradedCoefficientProjection T D0 (e + 1) (g z))
            (haction (tensorGradedSection T D0 e x))
        _ = (boundaryCoefficientCohomologyIso j L hI n (e + 1)).inv
              ((HX.map (T.degree (n * ((e + 1) + 1))).τ₁).hom
                ((HX.map (μ (tensorGradedSection T D0 e x)).asHom).hom z)) := hp _ _
        _ = (boundaryCoefficientCohomologyIso j L hI n (e + 1)).inv
              ((HX.map m).hom w) :=
          congrArg (fun y ↦ (boundaryCoefficientCohomologyIso j L hI n (e + 1)).inv y) hh
        _ = HZ.map v ((boundaryCoefficientCohomologyIso j L hI n 0).inv w) := hn
        _ = HZ.map ((ρ_ F).inv ≫ v)
              (HZ.map (ρ_ F).hom ((boundaryCoefficientCohomologyIso j L hI n 0).inv w)) :=
          hr _
        _ = HZ.map ((ρ_ F).inv ≫ v)
              (HZ.map (ρ_ F).hom (tensorGradedCoefficientProjection T D0 0 z)) :=
          congrArg (fun y ↦ HZ.map ((ρ_ F).inv ≫ v) (HZ.map (ρ_ F).hom y))
            (hp 0 z).symm

end
end AlgebraicGeometry.Scheme.Modules
