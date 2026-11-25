/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SquareZeroTensorBoundaryComparisons
public import WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf
public import WeilConjectures.CategoryTheory.CommAlgebraSheafModule
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedActionProjection
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroTensorGradedBoundaryProjection

/-! # Homogeneous realization of tensor boundaries

Source: Stacks Project, Tag 09MS, coherent-equation-ses and its direct sum over degrees;
Tag 0B8S, the quotient action on the square-zero kernel.
(blueprint: lem-sc-square-zero-tensor-boundary-graded-realization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
open Opposite TopologicalSpace
attribute [local irreducible] AlgebraicGeometry.Scheme.Modules.tensorPullback
  Functor.rightDerived Functor.rightDerivedToHomotopyCategory
namespace AlgebraicGeometry.Scheme.Modules
universe u wC wD
attribute [local irreducible] RingedSpace.moduleSectionBoundary boundaryCoefficientCohomologyIso
  canonicalTensorBoundaryComparisons tensorGradedSection
noncomputable section

section GradedProjectionHelpers
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] RingedSpace.moduleCohomology

private theorem graded_section_projection {X Z : Scheme.{u}} {j : Z ⟶ X}
    [IsClosedImmersion j] {L : X.Modules} {n : ℕ}
    (T : TensorGradedPresentation j L) (D : TensorBoundaryComparisonData j L n) (e : ℕ)
    (x : 𝟙_ Z.Modules ⟶ (((tensorPullback j).obj L).tensorPow n).tensorPow (e + 1)) :
    Hom.app (T.q (n * (e + 1))) ⊤ (tensorGradedSection T D e x) =
      (x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)) := by
  unfold tensorGradedSection
  set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      rw [← AddCommGrpCat.comp_apply, ← Hom.comp_app, T.c_projection, Hom.id_app]
  rfl

end GradedProjectionHelpers

/-- Realize the three homogeneous boundary/action terms in a single square-zero algebra
extension. This is a comparison theorem: it asserts no derivation identity, either for
that algebra extension or for tensor boundaries. The comparison holds for every compatible
resolution presentation and every action satisfying the displayed local formulas.

Source: Stacks Project, Tag 09MS, coherent-equation-ses and the graded direct-sum sequence
following it; Tag 0B8S, first paragraph of the proof (quotient action on the kernel).
(blueprint: lem-sc-square-zero-tensor-boundary-graded-realization).
Proof: form the sheaf direct sum B of L tensor powers, with multiplication given by the
inverse tensor-power addition isomorphisms. On a trivializing open for L this is the
polynomial algebra over O_X; the change-of-frame maps preserve multiplication, so these
algebras glue. Form C from the direct sums of j_* j^* L powers and let p be the direct
sum of adjunction units. The unit-quotient theorem and the ideal-kernel comparisons
identify its kernel K with the direct sum of I tensor L powers. Direct sums of these
short exact sequences are exact on stalks. Locally K is I times a polynomial algebra,
so its square is zero when I squared is zero. No finite type hypothesis is needed.
Include (f; a_0 inverse), after the degree-one right-unitor identification, in C in
homogeneous degree n, and (x; a_e inverse) in degree n(e+1); call these sections s and t.
Let P, Px and Pf be H^1 of the degree n(e+2), n(e+1) and n projections of K,
followed by the respective inverse coefficient comparisons.
For any compatible resolutions the snake boundary is the canonical section boundary:
naturality for the degree inclusion and projection, and the resolution/triangle
connecting comparison, identify P of boundary(s*t) with b_(e+1) inverse of the boundary
of lambda inverse followed by f tensor x. This calculation only identifies the product
section and its boundary; it does not expand that boundary as a sum. The local quotient
action formula uniquely fixes multiplication on K because its inclusion is mono. For
s acting on the degree n(e+1) summand, the coefficient comparison gives
mulTensorPowSection f F e 1. For t acting on degree n, the degree-zero right unitor gives
rho_F inverse followed by F whiskered with x, after H^1(rho_F). Naturality of the affine
cohomology edge and of the degree projections gives the two action equalities on every
cohomology class. Boundary naturality separately gives the two input boundary equalities,
separately, without using a product rule. All comparisons are the canonical ones since
hD identifies D with their explicit construction. Degree zero (n=0 or e=0) uses the same
inclusion/projection and unitors, and zero sections are handled by additivity. -/
theorem tensorBoundary_graded_realization
    {X Z : Scheme.{u}} (j : Z ⟶ X) [IsClosedImmersion j]
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD}
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (Opposite.op ⊤)))]
    (L : X.Modules) [L.IsInvertible] (hI : j.ker ^ 2 = ⊥) (n : ℕ)
    (hshort : ∀ d : ℕ, (ShortComplex.kernelSequence
      ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
        (L.tensorPow d))).ShortExact)
    (D : TensorBoundaryComparisonData j L n)
    (hD : canonicalTensorBoundaryComparisons j L hI n = D) :
    let F : Z.Modules := (tensorPullback j).obj (j.ker.toModules ⊗ L.tensorPow n)
    let N : Z.Modules := ((tensorPullback j).obj L).tensorPow n
    let H := RingedSpace.moduleCohomology Z.toRingedSpace 1
    let b : ∀ e : ℕ, H.obj (show Z.Modules from F ⊗ N.tensorPow e) ≃+
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
          (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
            (L.tensorPow (n * (e + 1))))) :=
      fun e ↦ Iso.addCommGroupIsoToAddEquiv (D.k e)
    let δ : ∀ e : ℕ, (𝟙_ Z.Modules ⟶ N.tensorPow (e + 1)) →
        (RingedSpace.moduleCohomology X.toRingedSpace 1).obj
          (kernel ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
            (L.tensorPow (n * (e + 1))))) :=
      fun (e : ℕ) (x : 𝟙_ Z.Modules ⟶ N.tensorPow (e + 1)) ↦
      RingedSpace.moduleSectionBoundary X.toRingedSpace
        (ShortComplex.kernelSequence
          ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
            (L.tensorPow (n * (e + 1))))) (hshort (n * (e + 1)))
        ((x ≫ (D.a e).inv).app ⊤ (1 : Γ(Z, ⊤)))
    ∀ (e : ℕ) (f : 𝟙_ Z.Modules ⟶ N) (x : 𝟙_ Z.Modules ⟶ N.tensorPow (e + 1)),
    ∃ (B C : X.CommAlgebraSheaf) (p : B ⟶ C)
      (I : SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (i : I ⟶ commAlgebraSheafModule X.sheaf B)
      (hw : i ≫ (commAlgebraSheafModuleFunctor X.sheaf).map p = 0)
      (_hS : (ShortComplex.mk i ((commAlgebraSheafModuleFunctor X.sheaf).map p)
        hw).ShortExact)
      (_hsq : ∀ (U : X.Opens) (a b : B.right.obj.obj (op U)),
        p.right.hom.app (op U) a = 0 → p.right.hom.app (op U) b = 0 → a * b = 0),
      ∀ (IA : InjectiveResolution I) (IB : InjectiveResolution (commAlgebraSheafModule X.sheaf B))
      (IC : InjectiveResolution (commAlgebraSheafModule X.sheaf C))
      (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
      (hαβ : α ≫ β = 0)
      (_hιA : IA.ι ≫ α = (CochainComplex.single₀ _).map i ≫ IB.ι)
      (_hιB : IB.ι ≫ β =
        (CochainComplex.single₀ _).map ((commAlgebraSheafModuleFunctor X.sheaf).map p) ≫ IC.ι)
      (_hH : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
        (HomologicalComplex.eval _ (ComplexShape.up ℕ) k)).ShortExact)
      (hΓ : ((ShortComplex.mk α β hαβ).map
        ((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ))).ShortExact)
        (σ : ∀ U : X.Opens, C.right.obj.obj (op U) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op U)) (I.val.obj (op U)))
      (μ : C.right.obj.obj (op ⊤) →+* End I)
      (ρ : C.right.obj.obj (op ⊤) →+*
        Module.End ((moduleRings X.toRingedSpace).obj.obj (op ⊤))
          ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I))
      (δ' : C.right.obj.obj (op ⊤) →+
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I)),
      (∀ (U : X.Opens) (b : B.right.obj.obj (op U)) (x : I.val.obj (op U)),
        @id (B.right.obj.obj (op U)) (i.val.app (op U) (σ U (p.right.hom.app (op U) b) x)) =
          b * @id (B.right.obj.obj (op U)) (i.val.app (op U) x)) →
      (∀ (U V : X.Opens) (j : V ⟶ U) (f : C.right.obj.obj (op U)) (x : I.val.obj (op U)),
        I.val.map j.op (σ U f x) = σ V (C.right.obj.map j.op f) (I.val.map j.op x)) →
      (∀ (f : C.right.obj.obj (op ⊤)) (U : X.Opens) (x : I.val.obj (op U)),
        (μ f).asHom.val.app (op U) x = σ U (C.right.obj.map (homOfLE le_top).op f) x) →
      (∀ f : C.right.obj.obj (op ⊤), ρ f =
        ((RingedSpace.moduleCohomology X.toRingedSpace 1).map (μ f).asHom).hom) →
      (∀ f : C.right.obj.obj (op ⊤), δ' f =
        (((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app
            (commAlgebraSheafModule X.sheaf C) ≫
          (IC.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 0).hom ≫
          hΓ.δ 0 1 rfl ≫
          (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).inv).hom
            f)) →
      ∃ (s t : C.right.obj.obj (op ⊤))
        (P : ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I) →+
          H.obj (show Z.Modules from F ⊗ N.tensorPow (e + 1)))
        (Px : ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I) →+
          H.obj (show Z.Modules from F ⊗ N.tensorPow e))
        (Pf : ((RingedSpace.moduleCohomology X.toRingedSpace 1).obj I) →+
          H.obj (show Z.Modules from F ⊗ N.tensorPow 0)),
        P (δ' (s * t)) = (b (e + 1)).symm
          (δ (e + 1) ((λ_ (𝟙_ Z.Modules)).inv ≫ (f ⊗ₘ x))) ∧
        Px (δ' t) = (b e).symm (δ e x) ∧
        Pf (δ' s) = (b 0).symm (δ 0 (tensorPowSection f 1)) ∧
        (∀ z : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj I,
          P (ρ s z) = H.map (mulTensorPowSection f F e 1) (Px z)) ∧
        (∀ z : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj I,
          P (ρ t z) = H.map ((ρ_ F).inv ≫ F ◁ x)
          (H.map (ρ_ F).hom (Pf z))) := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      intro F N H b δ e f x
      have hT : Nonempty (TensorGradedPresentation j L) :=
        tensorGradedPresentation_exists j L hI
      rcases hT with ⟨T⟩
      refine Exists.intro T.B ?_
      refine Exists.intro T.C ?_
      refine Exists.intro T.p ?_
      refine Exists.intro T.I ?_
      refine Exists.intro T.i ?_
      refine Exists.intro T.hw ?_
      refine Exists.intro T.shortExact ?_
      refine Exists.intro T.squareZero ?_
      intro IA IB IC α β hαβ hιA hιB hH hΓ σ μ ρ δ' hlocal hrestrict hglobal haction hboundary
      let s := tensorGradedSection T D 0 (tensorPowSection f 1)
      let t := tensorGradedSection T D e x
      let P := tensorGradedCoefficientProjection T D (e + 1)
      let Px := tensorGradedCoefficientProjection T D e
      let Pf := tensorGradedCoefficientProjection T D 0
      have hactions := tensorGradedAction_projection j L hI n T D hD e f x σ μ ρ
        hlocal hrestrict hglobal haction
      refine Exists.intro s ?_
      refine Exists.intro t ?_
      refine Exists.intro P ?_
      refine Exists.intro Px ?_
      refine Exists.intro Pf ?_
      let ψ (d : ℕ) (y : Γ((pushforward j).obj
          ((tensorPullback j).obj (L.tensorPow (n * (d + 1)))), ⊤)) :=
        (b d).symm (RingedSpace.moduleSectionBoundary X.toRingedSpace
          (ShortComplex.kernelSequence
            ((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app
              (L.tensorPow (n * (d + 1))))) (hshort (n * (d + 1))) y)
      refine ⟨?_, ?_, ?_, hactions⟩
      · have hb := tensorGradedProjection_boundary T D hshort
          IA IB IC α β hαβ hιA hιB hH hΓ δ' hboundary (e + 1) (s * t)
        have hp := tensorGradedSection_product j L hI n T D hD e f x
        exact hb.trans (congrArg (ψ (e + 1)) hp)
      · have hb := tensorGradedProjection_boundary T D hshort
          IA IB IC α β hαβ hιA hιB hH hΓ δ' hboundary e t
        have hp := graded_section_projection T D e x
        exact hb.trans (congrArg (ψ e) hp)
      · have hb := tensorGradedProjection_boundary T D hshort
          IA IB IC α β hαβ hιA hιB hH hΓ δ' hboundary 0 s
        have hp := graded_section_projection T D 0 (tensorPowSection f 1)
        exact hb.trans (congrArg (ψ 0) hp)
end
end AlgebraicGeometry.Scheme.Modules
