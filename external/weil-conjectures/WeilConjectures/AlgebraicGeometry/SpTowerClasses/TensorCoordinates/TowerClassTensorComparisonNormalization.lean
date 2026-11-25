/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorComparison
import all WeilConjectures.AlgebraicGeometry.SixFunctors.TowerClassTensorComparisonSections
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorComparisonCoordinates
import all WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorAdjointEvaluation
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.TensorCoordinates.TowerClassTensorUnitCoordinates

/-! # Adjunction normalization of the constructed ordinary tensor comparison

Source: Stacks 03EL; Zheng Construction 4.1; blueprint tower-operations proof (2).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local implicit_reducible] SheafOfModules.toSheaf SheafOfModules.forget
attribute [local implicit_reducible] PresheafOfModules.toPresheaf CategoryTheory.sheafCompose
attribute [local implicit_reducible] PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj PresheafOfModules.presheaf ModuleCat.restrictScalars
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe c v r u
open CategoryTheory.MonoidalCategory
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates
attribute [local irreducible] Scheme.proEtaleConstantRingComparison
  Scheme.proEtaleRingDirectImageMap Scheme.proEtaleRingModulePullback
  Scheme.proEtaleRingModuleAdjunction CategoryTheory.constantSheaf
  Padic Padic.coefficientExtensionIntegers SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
attribute [local implicit_reducible] spCoefficientCommRings SemilinearSections.evaluation
  SheafOfModules.pushforward PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj Scheme.proEtaleRingModuleDirectImage

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The constructed comparison has the ordinary finite adjunction's pure-tensor formula.

Source: Stacks 03EL, Zheng Construction 4.1, and blueprint
`sk-lem-sp-tower-bound-operations.proof.md`, clause (2).
(blueprint: lem-sfb-tower-class-tensor-comparison-normalization).

Proof: remove the specified coefficient and functor coordinate equalities. At level n,
use T.evaluation to replace the evaluation of T.system by its finite tensor comparison,
conjugated by the ordinary pull evaluation and the ordinary tensor evaluations. The
siteTensorIso maps the site sheafification-unit pairing to tensorSection. Apply
T.level_pure to the product of the two underlying module sheaves and its two projections;
the third generalized section is their sheafified pure pairing. Evaluate at the image of
(x,y) under the topos unit. Naturality of that unit says that its images under the two
projections are the unit images of x and y, and its image under the pairing is the unit
image of their pure tensor. The level_unit_underlying equation identifies these images
with the module adjunction unit after moduleUnderlying. The identity-on-sections
hypothesis hpush removes levelPushUnderlying. Transposing T.evaluation therefore sends
the source pure tensor to the tensor of the two finite unit sections, transported by
the inverses of ordinaryPullEvaluation. Finally geometry_unit_evaluation identifies
each of these sections with sectionAdjoint of the system identity. Transport through
the inverse target siteTensorIso to recover tensorPure. This proof uses only one
coefficient index, no transition equation or system assembly. It also covers zero
modules and empty charts, since the pairings and units are defined there. -/
theorem comparison_normalization {b : SpTowerShriek.Base l E}
    {X Y : Scheme.{u}} {f : X ⟶ Y} (g : SpTowerShriek.Geometry l E b f)
    (T : SemilinearSections.GeometryOrdinaryTensor
      (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y) (SpTowerShriek.tau l E Y)
      (Scheme.ProEt.topology X)
      (Scheme.proEtaleSheafInverseImage f (Type (u + 1)))
      (Scheme.proEtaleSheafDirectImage f (Type (u + 1)))
      (Scheme.proEtaleSheafAdjunction f (Type (u + 1))) (ordinaryGeometry l E g))
    (hpush : ∀ (n : ℕ)
      (N : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology X)
        (g.generic.coefficients n)) (U : Y.ProEtᵒᵖ)
      (x : ((SemilinearSections.underlying.{u + 1, u, u + 1}
        (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y n)).obj
          ((g.generic.levelPush n).obj N)).obj.obj U),
      HEq (((g.generic.levelPushUnderlying n).hom.app N).hom.app U x) x)
    (M N : Systems Y (Arings l E Y)) (n : ℕ) (U : Y.ProEtᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    HEq
      ((((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
        _ _) ((g.ordinaryPullEvaluation n).inv.app ((tensorRight l E Y N).obj M) ≫
          (SpTowerShriek.ev l E X n).map ((comparison l E g T N).hom.app M))).val.app U
            (tensorPure l E Y M N (op (n, U.unop)) x y))
      (tensorPure l E X (g.pull.obj M) (g.pull.obj N)
        (op (n, (chart f U).unop))
        (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U x)
        (sectionAdjoint l E g (𝟙 (g.pull.obj N)) n U y)) := by
  let O := ordinaryGeometry l E g
  let J := Scheme.ProEt.topology Y
  let J' := Scheme.ProEt.topology X
  let B := SpTowerShriek.B l E Y
  let τ := SpTowerShriek.tau l E Y
  let L := Scheme.proEtaleSheafInverseImage f (Type (u + 1))
  let P := Scheme.proEtaleSheafDirectImage f (Type (u + 1))
  let a := Scheme.proEtaleSheafAdjunction f (Type (u + 1))
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (SemilinearSections.systemRing J B τ)
  let := SheafOfModules.monoidalCategory (SemilinearSections.systemRing J B τ)
  let := SheafOfModules.isMonoidal_W_independentCoefficients
    (SemilinearSections.systemRing J' O.coefficients O.coefficientTransition)
  let := SheafOfModules.monoidalCategory
    (SemilinearSections.systemRing J' O.coefficients O.coefficientTransition)
  let μ (N : SpTowerShriek.S l E Y) :
      CategoryTheory.MonoidalCategory.tensorRight N ⋙ O.pull ≅
        O.pull ⋙ CategoryTheory.MonoidalCategory.tensorRight (O.pull.obj N) :=
    NatIso.ofComponents (fun M ↦ T.system M N) (by
      intro M M' t
      change O.pull.map (t ▷ N) ≫ (T.system M' N).hom =
        (T.system M N).hom ≫ (O.pull.map t ▷ O.pull.obj N)
      have h := T.system_natural t (𝟙 N)
      change O.pull.map (t ⊗ₘ 𝟙 N) ≫ (T.system M' N).hom =
        (T.system M N).hom ≫ (O.pull.map t ⊗ₘ O.pull.map (𝟙 N)) at h
      rw [O.pull.map_id, MonoidalCategory.tensorHom_id,
        MonoidalCategory.tensorHom_id] at h
      exact h)
  let d (M N : Systems Y (Arings l E Y)) :=
    O.pull.map ((siteTensorIso.{u + 1, u, u + 1}
      (coefficientSequenceTopology J) (systemRing l E Y) N).hom.app M) ≫
      (T.system M N).hom ≫
        (siteTensorIso.{u + 1, u, u + 1} (coefficientSequenceTopology J')
          (SemilinearSections.systemRing J' O.coefficients O.coefficientTransition)
          (O.pull.obj N)).inv.app (O.pull.obj M)
  let η (Z : Sheaf J (Type (u + 1))) (z : Z.obj.obj U) := (a.unit.app Z).hom.app U z
  have hη {Z W : Sheaf J (Type (u + 1))} (t : Z ⟶ W) (z : Z.obj.obj U) :
      (L.map t).hom.app (chart f U) (η Z z) = η W (t.hom.app U z) :=
    congrArg (fun k ↦ k.hom.app U z) (a.unit.naturality t).symm
  let s := SemilinearSections.sectionImage.{u + 1, u, u + 1}
    J B τ J' L P a O U (chart f U) η n
  have hs (M : Systems Y (Arings l E Y)) (z : M.val.obj (op (n, U.unop))) :
      HEq (s M z) (sectionAdjoint l E g (𝟙 (g.pull.obj M)) n U z) := by
    unfold s SemilinearSections.sectionImage
    apply (cast_heq _ _).trans
    exact tensorComparison_unit_coordinates l E g O.coefficients O.coefficientTransition
      g.coefficients g.transitions O.pull g.pull_eq n
      ⟨(O.inverseImage n).modules, O.levelPush n, O.levelAdjunction n⟩
      (g.levelAdjunction_eq n) (O.ordinaryPullEvaluation n)
      (g.ordinaryPullEvaluation_eq n) (O.inverseImage n).moduleUnderlying
      (O.levelPushUnderlying n) (O.level_unit_underlying n) (hpush n) M U z
  have hk (M N : Systems Y (Arings l E Y)) :
      HEq ((comparison l E g T N).hom.app M) (d M N) :=
    tensorComparison_coordinates l E g O.coefficients O.coefficientTransition
      g.coefficients g.transitions O.pull g.pull_eq μ M N
  have hp (M N : Systems Y (Arings l E Y))
      (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
      (d M N).val.app (op (n, (chart f U).unop))
        (s _ (tensorPure l E Y M N (op (n, U.unop)) x y)) =
      sitePair.{u + 1, u, u + 1} (coefficientSequenceTopology J')
        (SemilinearSections.systemRing J' O.coefficients O.coefficientTransition)
        (O.pull.obj M) (O.pull.obj N) (op (n, (chart f U).unop)) (s M x) (s N y) :=
    SemilinearSections.site_unit_pure.{u + 1, u, u + 1}
      J B τ J' L P a O T U (chart f U) η hη n M N x y
  apply heq_of_eq
  rw [adjoint_section l E g]
  exact transport_pure l E g O.coefficients O.coefficientTransition
    g.coefficients g.transitions O.pull g.pull_eq
    (fun M N ↦ (comparison l E g T N).hom.app M) d hk n U s hs hp M N x y

end AlgebraicGeometry.ProEtale.SpTowerClasses.TensorCoordinates
