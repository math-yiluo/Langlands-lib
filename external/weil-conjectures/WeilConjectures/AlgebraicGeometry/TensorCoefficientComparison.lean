/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # The fixed ordinary-to-tensor coefficient identification -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe v
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- The fixed tensor pullback adjunction, with its large section formula hidden
behind its categorical type. Source: Stacks Project, Tag 0096.
(blueprint: def-sc-tensor-coefficient-comparison) -/
def coefficientTensorAdjunction {A X : Scheme.{v}} (q : A ⟶ X) :
    tensorPullback q ⊣ pushforward q :=
  Classical.choose (exists_tensorPullbackAdjunction q)

/-- The fixed comparison of ordinary and tensor pullback left adjoints.
Source: Stacks Project, Tag 0096.
(blueprint: def-sc-tensor-coefficient-comparison) -/
def coefficientOrdinaryPullbackComparison {A X : Scheme.{v}} (q : A ⟶ X) :
    pullback q ≅ tensorPullback q :=
  ((coefficientTensorAdjunction q).leftAdjointUniq
    (pullbackPushforwardAdjunction q)).symm

/-- The tensor pullback comparison for a commuting triangle, with its fixed
adjunction choices. Source: Stacks Project, Tags 0096 and 0D5S.
(blueprint: def-sc-tensor-coefficient-comparison) -/
def coefficientTensorTriangle {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1) :
    tensorPullback q1 ≅ tensorPullback q ⋙ tensorPullback a :=
  (conjugateIsoEquiv ((coefficientTensorAdjunction q).comp
    (coefficientTensorAdjunction a)) (coefficientTensorAdjunction q1)).symm
    (pushforwardComp a q ≪≫ pushforwardCongr h)

/-- The coefficient identification for a commuting triangle, constructed from
composition of pushforward and the fixed tensor adjunctions.
Source: Stacks Project, Tags 0096 and 0D5S.
(blueprint: def-sc-tensor-coefficient-comparison) -/
@[irreducible]
def tensorCoefficientComparison {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    (pullback a).obj ((tensorPullback q).obj L) ≅ (tensorPullback q1).obj L :=
  (coefficientOrdinaryPullbackComparison a).app ((tensorPullback q).obj L) ≪≫
    ((coefficientTensorTriangle q q1 a h).app L).symm

/-- The defining equation for the coefficient comparison, with the original
selected adjunctions displayed. Source: Stacks Project, Tags 0096 and 0D5S.
(blueprint: def-sc-tensor-coefficient-comparison)
Proof: unfold the typed wrappers; this is the same isomorphism by reflexivity. -/
theorem tensorCoefficientComparison_eq {A B X : Scheme.{v}}
    (q : A ⟶ X) (q1 : B ⟶ X) (a : B ⟶ A) (h : a ≫ q = q1)
    (L : X.Modules) :
    tensorCoefficientComparison q q1 a h L =
      let c := (conjugateIsoEquiv
        ((Classical.choose (exists_tensorPullbackAdjunction q)).comp
          (Classical.choose (exists_tensorPullbackAdjunction a)))
        (Classical.choose (exists_tensorPullbackAdjunction q1))).symm
        (pushforwardComp a q ≪≫ pushforwardCongr h)
      ((Classical.choose (exists_tensorPullbackAdjunction a)).leftAdjointUniq
        (pullbackPushforwardAdjunction a)).symm.app ((tensorPullback q).obj L) ≪≫
          (c.app L).symm := by
  delta tensorCoefficientComparison coefficientOrdinaryPullbackComparison
    coefficientTensorTriangle coefficientTensorAdjunction
  rfl

end
end AlgebraicGeometry.Scheme.Modules
