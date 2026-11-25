/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedProductProjection
import WeilConjectures.CategoryTheory.Abelian.ResolvedBoundaryNaturality
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Naturality of homogeneous boundary projections

Source: Stacks Project, Tag 09MS, the graded direct-sum ideal sequence.
(blueprint: lem-sc-square-zero-tensor-graded-boundary-projection).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD
attribute [local irreducible] boundaryCoefficientCohomologyIso canonicalTensorBoundaryComparisons
attribute [local irreducible] RingedSpace.moduleSectionBoundary Functor.rightDerived tensorPullback
  Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso
  InjectiveResolution.isoRightDerivedObj DerivedCategory.HomologySequence.δ
  ShortComplex.ShortExact.δ tensorGradedAlgebraMap Functor.mapHomologicalComplex
  ShortComplex.ShortExact.singleTrianglePlus
private theorem boundary_enoughInjectives (X : Scheme.{u}) :
    EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
attribute [local instance] boundary_enoughInjectives
noncomputable section

/-- Cohomology of a degree projection carries the canonical section boundary to the
boundary of its quotient projection. This statement concerns one short-complex morphism,
not products, actions, or the realization existential. Compatible resolutions only
present the single boundary whose degree projection is computed.

Source: Stacks Project, Tag 01DZ, naturality of the cohomology boundary;
Tag 09MS, projections of the graded direct-sum short exact sequence.
(blueprint: lem-sc-square-zero-tensor-graded-boundary-projection).
Proof: The snake/triangle comparison for the supplied compatible resolutions identifies
δ-prime with the canonical section boundary. Apply rightDerived_triangle_connecting
to global sections. Its triangle comparison
identifies its delta with moduleCohomologyBoundary after the canonical single-complex
isomorphisms. Delta naturality for T.degree in degrees zero and one, followed by naturality
of toRightDerivedZero, identifies the two section-boundary composites. Evaluate on z and
use degree_quotient to replace the third component by q. Compose with the inverse additive
coefficient comparison D.k; tensorGradedCoefficientProjection_apply identifies the left
side. No multiplication rule is used. The argument includes n=0, e=0 and zero sections. -/
theorem tensorGradedProjection_boundary {X Z : Scheme.{u}} {j : Z ⟶ X}
    [IsClosedImmersion j]
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))]
    {L : X.Modules} {n : ℕ} (T : TensorGradedPresentation j L)
    (D : TensorBoundaryComparisonData j L n)
    (hshort : ∀ d : ℕ, (ShortComplex.kernelSequence
      (tensorGradedUnit j (L.tensorPow d))).ShortExact)
    (IA : InjectiveResolution T.I)
    (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf T.B))
    (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf T.C))
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map T.i ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ _).map
      (tensorGradedAlgebraMap T.p) ≫ IC.ι)
    (hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
    (hΓ : ((ShortComplex.mk α β hαβ).map
      ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
        (ComplexShape.up ℕ))).ShortExact)
    (δ' : T.C.right.obj.obj (op ⊤) →+
      ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj T.I))
    (hboundary : ∀ z : T.C.right.obj.obj (op ⊤), δ' z =
      (((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
          (commAlgebraSheafModule X.sheaf T.C) ≫
        (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
        hΓ.δ 0 1 rfl ≫
        (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv).hom z))
    (e : ℕ) (z : T.C.right.obj.obj (op ⊤)) :
    tensorGradedCoefficientProjection T D e (δ' z) =
      (Iso.addCommGroupIsoToAddEquiv
        (Y := AddCommGrpCat.of ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj
          (kernel (tensorGradedUnit j (L.tensorPow (n * (e + 1))))))) (D.k e)).symm
        (RingedSpace.moduleSectionBoundary X.toRingedSpace
          (ShortComplex.kernelSequence
            (tensorGradedUnit j (L.tensorPow (n * (e + 1))))) (hshort (n * (e + 1)))
          (Hom.app (T.q (n * (e + 1))) ⊤ z)) := by
  -- Keep the derived comparison maps opaque during concrete definition matching.
  set_option maxRecDepth 300 in
    set_option backward.isDefEq.respectTransparency true in
      set_option backward.isDefEq.respectTransparency.types true in
        let v := RingedSpace.globalSectionsFunctor X.toRingedSpace
        let : PreservesFiniteLimits v := inferInstanceAs (PreservesFiniteLimits
          (SheafOfModules.evaluation (moduleRings X.toRingedSpace) (op ⊤)))
        let S : ShortComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
          ShortComplex.kernelSequence (tensorGradedUnit j (L.tensorPow (n * (e + 1))))
        let hS : S.ShortExact := hshort (n * (e + 1))
        unfold tensorGradedCoefficientProjection
        change (Iso.addCommGroupIsoToAddEquiv
          (Y := AddCommGrpCat.of ((v.rightDerived 1).obj S.X₁)) (D.k e)).symm
            (((v.rightDerived 1).map (T.degree (n * (e + 1))).τ₁).hom (δ' z)) = _
        refine congrArg (α := (v.rightDerived 1).obj S.X₁)
          (Iso.addCommGroupIsoToAddEquiv
            (Y := AddCommGrpCat.of ((v.rightDerived 1).obj S.X₁)) (D.k e)).symm ?_
        refine (congrArg
          (((v.rightDerived 1).map (T.degree (n * (e + 1))).τ₁).hom)
          (hboundary z)).trans ?_
        exact resolvedBoundary_naturality.{_, _, _, wC, wD} v
          (ShortComplex.mk T.i (tensorGradedAlgebraMap T.p) T.hw) S
          T.shortExact hS (T.degree (n * (e + 1)))
          (T.q (n * (e + 1))) (T.degree_quotient (n * (e + 1)))
          IA IB IC α β hαβ hιA hιB hH hΓ z (Hom.app (T.q (n * (e + 1))) ⊤ z)
          (by rfl) (RingedSpace.moduleSectionBoundary X.toRingedSpace S hS) (by
            unfold RingedSpace.moduleSectionBoundary RingedSpace.moduleCohomologyBoundary
            rfl)

end
end AlgebraicGeometry.Scheme.Modules
