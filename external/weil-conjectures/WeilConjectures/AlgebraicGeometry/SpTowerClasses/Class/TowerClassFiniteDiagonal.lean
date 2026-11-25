/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.SingleBoundaryNormalization

import WeilConjectures.AlgebraicGeometry.SpTowerClasses.ClosedIntegralHomExt
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.ClosedTowerDirectImageExact
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

/-! # Finite supported diagonal normalization

Source: blueprint main-20261015, chap-Smooth-purity,
`sk-prop-sp-tower-geometric-classes` (blueprint: def-sp-tower-class-finite-diagonal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ u₃ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Direct image along the actual diagonal is exact on system sheaves.
Source: classes (3); finite direct image exactness
(blueprint: def-sp-tower-class-finite-diagonal).
Proof: a closed immersion has finite geometric fibres and its small pro-etale
direct image is exact, including the empty closed immersion. The coefficient
system maps are formed with the same identity structural maps at every level;
kernels and sheafified cokernels are levelwise, so the ordinary system direct
image preserves both. Transport through the section-normalized realization
retains those kernels and cokernels. -/
theorem diagonalPush_exact {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) :
    PreservesFiniteLimits g.push ∧ PreservesFiniteColimits g.push := by
  have := SmoothOfRelativeDimension.smooth 1 (ProjectiveLine S ↘ S)
  have : LocallyOfFinitePresentation (ProjectiveLine S ↘ S) := inferInstance
  have : LocallyOfFinitePresentation (diagonalImmersion S) := by
    change LocallyOfFinitePresentation (pullback.diagonal (ProjectiveLine S ↘ S))
    infer_instance
  exact closedTowerPush_exact l E (diagonalImmersion S) g

/-- Exact diagonal direct image preserves finite limits.
Source: classes (3) (blueprint: def-sp-tower-class-finite-diagonal). -/
instance diagonalPushLimits {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) :
    PreservesFiniteLimits g.push := (diagonalPush_exact l E g).1

/-- Exact diagonal direct image preserves finite colimits.
Source: classes (3) (blueprint: def-sp-tower-class-finite-diagonal). -/
instance diagonalPushColimits {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) :
    PreservesFiniteColimits g.push := (diagonalPush_exact l E g).2

private theorem forget_apply {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N : SheafOfModules.{u + 1} R} (a : M ⟶ N) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((SheafOfModules.toSheaf R).map a).hom.app U x = a.val.app U x := by
  rfl

private theorem iso_trans_apply {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} {A B D : Sheaf J AddCommGrpCat.{u + 1}}
    (e : A ≅ B) (f : B ≅ D) (U : Cᵒᵖ) (x : A.obj.obj U) :
    (e ≪≫ f).hom.hom.app U x = f.hom.hom.app U (e.hom.hom.app U x) := by
  rfl

/-- The underlying-sheaf comparison for a direct image over an arbitrary constant ring. -/
@[irreducible] private def directImageUnderlying
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : proEtaleRingModules X (proEtaleConstantRing X A)) :
    (SheafOfModules.toSheaf _).obj ((proEtaleConstantRingPushforward A f).obj N) ≅
      (lowerStar AddCommGrpCat.{u + 1} f).obj ((SheafOfModules.toSheaf _).obj N) :=
  Iso.refl _

private theorem directImageUnderlying_hom
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (N : proEtaleRingModules X (proEtaleConstantRing X A)) (U : Y.ProEtᵒᵖ)
    (x : N.val.obj ((Scheme.proEtaleBaseChange f).op.obj U)) :
    (directImageUnderlying A f N).hom.hom.app U x = x := by
  unfold directImageUnderlying
  rfl

private theorem directImageUnderlyingIso_apply
    (A : Type u) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (N : proEtaleRingModules X (proEtaleConstantRing X A))
    (e : M ≅ (proEtaleConstantRingPushforward A f).obj N)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    HEq (((SheafOfModules.toSheaf _).mapIso e ≪≫
      directImageUnderlying A f N).hom.hom.app U x) (e.hom.val.app U x) := by
  have h₁ := iso_trans_apply ((SheafOfModules.toSheaf _).mapIso e)
    (directImageUnderlying A f N) U x
  have h₂ := directImageUnderlying_hom A f N U
    (((SheafOfModules.toSheaf _).map e.hom).hom.app U x)
  have h₃ := forget_apply e.hom U x
  exact h₁.heq.trans (h₂.heq.trans h₃.heq)

/-- Forgetting a system direct image has the same underlying sheaf as ordinary direct image.
The identity comparison is checked on an arbitrary module, before specializing to coefficients. -/
@[irreducible] private def pushEvaluationUnderlying
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (N : SpTowerShriek.S l E X) (n : ℕ) :
    (finiteForget l E Y n).obj ((SpTowerShriek.ev l E Y n).obj (g.push.obj N)) ≅
      (lowerStar AddCommGrpCat.{u + 1} f).obj
        ((finiteForget l E X n).obj ((SpTowerShriek.ev l E X n).obj N)) :=
  (finiteForget l E Y n).mapIso ((g.ordinaryPushEvaluation n).app N) ≪≫
    directImageUnderlying (SpTowerShriek.R l E n) f ((SpTowerShriek.ev l E X n).obj N)

private theorem pushEvaluationUnderlying_apply
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (N : SpTowerShriek.S l E X) (n : ℕ)
    (U : Y.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E Y n).obj (g.push.obj N)).val.obj U) :
    HEq ((pushEvaluationUnderlying l E g N n).hom.hom.app U x)
      (((g.ordinaryPushEvaluation n).hom.app N).val.app U x) := by
  unfold pushEvaluationUnderlying
  exact directImageUnderlyingIso_apply (SpTowerShriek.R l E n) f
    ((SpTowerShriek.ev l E Y n).obj (g.push.obj N))
    ((SpTowerShriek.ev l E X n).obj N) ((g.ordinaryPushEvaluation n).app N) U x

set_option backward.isDefEq.respectTransparency true in
/-- The supported finite quotient is induced by the same integral quotient on P.
Source: classes (3), supported quotient normalization
(blueprint: def-sp-tower-class-finite-diagonal).
Proof: over a chart U of W its source consists of locally constant integers on
P times_W U. Send each such integer to its residue multiple of one. The ordinary
pushforward evaluation identifies the target with these actual coefficient
sections on P times_W U. Constant generators locally generate the source and
sheaf gluing gives existence and uniqueness. -/
theorem finiteSupportedQuotient_existsUnique {b : SpTowerShriek.Base l E}
    {S : Scheme.{u}} (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) (n : ℕ) :
    ∃! q : diagonalIntegralSource S ⟶
      (finiteForget l E (diagonalSurface S) n).obj
        ((SpTowerShriek.ev l E (diagonalSurface S) n).obj
          (g.push.obj (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S))))),
      ∀ (U : (diagonalSurface S).ProEtᵒᵖ) (k : ULift.{u + 1} ℤ),
        HEq
          (((g.ordinaryPushEvaluation n).hom.app
              (coefficient (ProjectiveLine S) (Arings l E (ProjectiveLine S)))).val.app U
            (q.hom.app U ((toSheafify (Scheme.ProEt.topology (ProjectiveLine S))
              ((Functor.const (ProjectiveLine S).ProEtᵒᵖ).obj
                (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
                  (chart (diagonalImmersion S) U) k)))
          (k.down : (SpTowerShriek.B l E (ProjectiveLine S) n).obj.obj
            (chart (diagonalImmersion S) U)) := by
  let P := ProjectiveLine S
  let W := diagonalSurface S
  let F := lowerStar AddCommGrpCat.{u + 1} (diagonalImmersion S)
  let M := coefficient P (Arings l E P)
  let e := pushEvaluationUnderlying l E g M n
  let q : diagonalIntegralSource S ⟶
      (finiteForget l E W n).obj ((SpTowerShriek.ev l E W n).obj (g.push.obj M)) :=
    F.map (finiteQuotient l E P n) ≫ e.inv
  have he : q ≫ e.hom = F.map (finiteQuotient l E P n) := by
    exact (Category.assoc _ _ _).trans
      ((congrArg (fun t ↦ F.map (finiteQuotient l E P n) ≫ t) e.inv_hom_id).trans
        (Category.comp_id _))
  have hq (U : W.ProEtᵒᵖ) (k : ULift.{u + 1} ℤ) :
      HEq (e.hom.hom.app U (q.hom.app U
        ((toSheafify (Scheme.ProEt.topology P)
          ((Functor.const P.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
            (chart (diagonalImmersion S) U) k)))
        (k.down : (SpTowerShriek.B l E P n).obj.obj (chart (diagonalImmersion S) U)) := by
    have h := congrArg (fun a ↦ a.hom.app U
      ((toSheafify (Scheme.ProEt.topology P)
        ((Functor.const P.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
          (chart (diagonalImmersion S) U) k)) he
    exact h.heq.trans ((finiteQuotient_existsUnique l E P n).exists.choose_spec
      (chart (diagonalImmersion S) U) k)
  refine ⟨q, ?_, ?_⟩
  · intro U k
    exact ((pushEvaluationUnderlying_apply l E g M n U _).symm).trans (hq U k)
  intro q' hq'
  apply closedIntegral_hom_ext (diagonalImmersion S)
  intro U k
  have hi : Function.Injective (e.hom.hom.app U) := by
    apply Function.LeftInverse.injective (g := e.inv.hom.app U)
    intro z
    exact congrArg (fun a ↦ a.hom.app U z) e.hom_inv_id
  apply hi
  exact eq_of_heq ((pushEvaluationUnderlying_apply l E g M n U _).trans
    ((hq' U k).trans (hq U k).symm))

/-- The canonical supported finite coefficient quotient, fixed on integral generators.
Source: classes (3) (blueprint: def-sp-tower-class-finite-diagonal). -/
def finiteSupportedQuotient {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    (g : SpTowerShriek.Geometry l E b (diagonalImmersion S)) (n : ℕ) :=
  (finiteSupportedQuotient_existsUnique l E g n).exists.choose

attribute [local irreducible] finiteSupportedQuotient coefficient

/-- The diagonal class evaluated in its actual finite coefficient module categories.
Source: classes (3) (blueprint: def-sp-tower-class-finite-diagonal). -/
def evaluatedDiagonal {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) (n : ℕ) :=
  mapSingleArrow (SpTowerShriek.ev l E (diagonalSurface S) n) (2 : ℤ)
    ((d.geometry.push.singleFunctorCompRightDerivedFunctorIso).inv.app _ ≫
      diagonalArrow l E c d.sourceIso) ≫
    ((DerivedCategory.singleFunctor _ 0).map (lineEvaluation l E c n).hom)⟦(2 : ℤ)⟧'

/-- Concrete finite diagonal normalization, expressed by the coefficient-linear
realization of the signed Cartier boundary. The supported integer quotient and
the map z -> 1 tensor z fix the source and target, respectively.
Source: classes (3), proof steps 9--13 (blueprint: def-sp-tower-class-finite-diagonal). -/
def FiniteDiagonalNormalization {b : SpTowerShriek.Base l E} {S : Scheme.{u}}
    {c : Chern l E (diagonalSurface S)} (d : Diagonal l E b S c) : Prop :=
  ∀ n : ℕ,
    let quotient := finiteSupportedQuotient l E d.geometry n
    let roots := finiteRootMap l E (diagonalSurface S) n
    let arrow := mapSingleArrow (finiteForget l E (diagonalSurface S) n) (2 : ℤ)
      (evaluatedDiagonal l E d n)
    let boundary := mapSingleArrow (abEvaluation (diagonalSurface S) n) (2 : ℤ)
      (kummerComposite
        (ShortComplex.mk c.kummer.inclusion c.kummer.power c.kummer.zero)
        c.kummer.exact (diagonalBoundary S))
    singleBoundaryEquality quotient roots arrow boundary

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
