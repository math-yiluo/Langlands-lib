/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassDiagonal
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionSectionNaturality

/-! # Horizontal transition on the finite tensor generators of the root line -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] SemilinearSections.scalarExtensionSection

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem heq_app {A B A' B' : AddCommGrpCat.{u + 1}}
    (hA : A = A') (hB : B = B') {f : A →+ B} {g : A' →+ B'}
    (hf : HEq f g) {x : A} {y : A'} (hx : HEq x y) :
    HEq (f x) (g y) := by
  cases hA
  cases hB
  exact heq_of_eq (congrArg (fun k : A →+ B ↦ k x) (eq_of_heq hf) |>.trans
    (congrArg g (eq_of_heq hx)))

private theorem cast_heq' {A B : AddCommGrpCat.{u + 1}} (h : A = B) (x : A) :
    HEq ((eqToHom h) x) x := by
  subst B
  rfl

section

attribute [local implicit_reducible] spCoefficientCommRings lineEvaluation
  SemilinearSections.transition

private def lineScalarSection {T : Scheme.{u}} (c : Chern l E T)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : c.rootModule.val.obj (op (n, U.unop))) :
    ((SpTowerShriek.ev l E T n).obj (lineModule l E c)).val.obj U :=
  SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
    (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x

private theorem lineScalarSection_heq {T : Scheme.{u}} (c : Chern l E T)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : c.rootModule.val.obj (op (n, U.unop))) :
    HEq (lineScalarSection l E c n U x)
      (SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
        (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) :=
  HEq.rfl

attribute [local irreducible] lineScalarSection

private theorem lineScalarSection_normalization {T : Scheme.{u}} (c : Chern l E T)
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : c.rootModule.val.obj (op (n, U.unop)))
    (x' : ((c.reduction.forget.F.obj c.rootModule).obj (op n)).obj.obj U)
    (hx : HEq x x') :
    (lineEvaluation l E c n).hom.val.app U (lineScalarSection l E c n U x) =
      Scheme.tateFiniteTensor T l (FiniteRing l E n) n (finiteScalar l E n)
        U.unop 1 ((c.rootForget.hom.app (op n)).hom.app U x') := by
  have hv : HEq (lineScalarSection l E c n U x)
      ((1 : (SpTowerShriek.B l E T n).obj.obj U) •
        SemilinearSections.scalarExtensionSection.{u + 1, u, u + 1}
          (coefficientSystemMap l E T) c.scalar c.rootModule (op (n, U.unop)) x) := by
    simpa only [one_smul] using lineScalarSection_heq l E c n U x
  simpa only [lineEvaluation] using
    (lineEvaluation_existsUnique l E c n).exists.choose_spec
      U 1 x x' (lineScalarSection l E c n U x) hx hv

end

attribute [local irreducible] lineScalarSection

private theorem lineScalarSection_natural {T : Scheme.{u}} (c : Chern l E T)
    {m n : ℕ} (h : n ≤ m) (U : T.ProEtᵒᵖ)
    (x : c.rootModule.val.obj (op (m, U.unop))) :
    HEq
      (((SemilinearSections.transition.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T) h).app (lineModule l E c)).val.app U
          (lineScalarSection l E c m U x))
      (lineScalarSection l E c n U
        (c.rootModule.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)) := by
  exact SemilinearSections.scalarExtensionSection_transition (Scheme.ProEt.topology T)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
    (coefficientSystemMap l E T) c.scalar c.rootModule h U x
    (lineScalarSection l E c m U x)
    (lineScalarSection l E c n U
      (c.rootModule.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x))
    (lineScalarSection_heq l E c m U x)
    (lineScalarSection_heq l E c n U _)

attribute [local irreducible] lineModule

/-- Evaluation carries the actual tower transition on a unit tensor to the unit tensor
of the actual roots transition.

Source: blueprint classes (2), scalar extension of the roots tower.
(blueprint: lem-sfb-tower-line-transition-tensor).

Proof: lift the root through rootForget and the section equality of Forget.
The normalization of lineEvaluation identifies its tensor generator with the
scalar-adjunction unit. Naturality of this unit along the horizontal sequence-site
arrow sends the generator to the generator of the root restriction. The transition
equation of Forget and naturality of rootForget
identify that root restriction with the actual roots-tower transition. Apply the
normalization of lineEvaluation at the target level. The argument uses identities of
sections and applies to empty charts as well as equal indices.
-/
theorem lineEvaluation_transition_tensor {T : Scheme.{u}} (c : Chern l E T)
    {m n : ℕ} (h : n ≤ m) (U : T.ProEtᵒᵖ)
    (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (m + 1))).obj.obj U) :
    HEq
      (((SemilinearSections.transition.{u + 1, u, u + 1}
        (Scheme.ProEt.topology T) (SpTowerShriek.B l E T)
        (SpTowerShriek.tau l E T) h).app (lineModule l E c)).val.app U
          ((lineEvaluation l E c m).inv.val.app U
            (Scheme.tateFiniteTensor T l (FiniteRing l E m) m (finiteScalar l E m)
              U.unop 1 z)))
      ((lineEvaluation l E c n).inv.val.app U
        (Scheme.tateFiniteTensor T l (FiniteRing l E n) n (finiteScalar l E n)
          U.unop 1 (((roots l T).map (homOfLE h).op).hom.app U z))) := by
  let x' := (c.rootForget.inv.app (op m)).hom.app U z
  let x := (eqToHom (c.reduction.forget.sections c.rootModule m U)) x'
  have hx : HEq x x' := cast_heq' _ _
  have hz : (c.rootForget.hom.app (op m)).hom.app U x' = z := by
    exact congrArg (fun f ↦ f.hom.app U z) (c.rootForget.app (op m)).inv_hom_id
  have hnorm := lineScalarSection_normalization l E c m U x x' hx
  rw [hz] at hnorm
  have hi : (lineEvaluation l E c m).inv.val.app U
      (Scheme.tateFiniteTensor T l (FiniteRing l E m) m (finiteScalar l E m)
        U.unop 1 z) =
      lineScalarSection l E c m U x := by
    rw [← hnorm]
    exact congrArg
      (fun f : (SpTowerShriek.ev l E T m).obj (lineModule l E c) ⟶
          (SpTowerShriek.ev l E T m).obj (lineModule l E c) ↦
        f.val.app U (lineScalarSection l E c m U x))
      (lineEvaluation l E c m).hom_inv_id
  rw [hi]
  let p := (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op
  let y := c.rootModule.val.map p x
  let y' := ((c.reduction.forget.F.obj c.rootModule).map (homOfLE h).op).hom.app U x'
  have hy : HEq y y' :=
    heq_app (c.reduction.forget.sections c.rootModule m U).symm
      (c.reduction.forget.sections c.rootModule n U).symm
      (c.reduction.forget.transitions c.rootModule h U).symm hx
  have hyz : (c.rootForget.hom.app (op n)).hom.app U y' =
      ((roots l T).map (homOfLE h).op).hom.app U z := by
    have hn := congrArg (fun f ↦ f.hom.app U x')
      (c.rootForget.hom.naturality (homOfLE h).op)
    change (c.rootForget.hom.app (op n)).hom.app U y' =
      ((roots l T).map (homOfLE h).op).hom.app U
        ((c.rootForget.hom.app (op m)).hom.app U x') at hn
    exact hn.trans (congrArg
      (fun t ↦ ((roots l T).map (homOfLE h).op).hom.app U t) hz)
  have hn := lineScalarSection_normalization l E c n U y y' hy
  rw [hyz] at hn
  have hi_n : (lineEvaluation l E c n).inv.val.app U
      (Scheme.tateFiniteTensor T l (FiniteRing l E n) n (finiteScalar l E n)
        U.unop 1 (((roots l T).map (homOfLE h).op).hom.app U z)) =
      lineScalarSection l E c n U y := by
    rw [← hn]
    exact congrArg
      (fun k : (SpTowerShriek.ev l E T n).obj (lineModule l E c) ⟶
          (SpTowerShriek.ev l E T n).obj (lineModule l E c) ↦
        k.val.app U (lineScalarSection l E c n U y))
      (lineEvaluation l E c n).hom_inv_id
  rw [hi_n]
  exact lineScalarSection_natural l E c h U x

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
