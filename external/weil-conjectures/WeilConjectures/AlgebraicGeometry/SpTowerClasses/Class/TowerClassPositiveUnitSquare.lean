/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Projective.TowerClassProjective
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjointNaturality
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassSectionAdjointFaithful

/-! # The positive pullback square at the coefficient unit

Source: blueprint latest, diagonal-tower trace proof, paragraph (1), and the
section normalizations of the tensor-line projection mate.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] lineModule
  Scheme.proEtaleConstantRingComparison Scheme.proEtaleRingDirectImageMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem unit_one {T : Scheme.{u}} {c : Chern l E T}
    (t : Twisting l E c) (U : (ℕ × T.ProEt)ᵒᵖ)
    (y : (lineModule l E c).val.obj U)
    (z : (t.equivalence.functor.obj (coefficient T (Arings l E T))).val.obj U)
    (hz : HEq z (pure l E c (coefficient T (Arings l E T)) U
      (1 : (systemRing l E T).obj.obj U) y)) :
    t.unitIso.hom.val.app U z = y := by
  simpa only [one_smul] using t.unit_normalization U
    (1 : (systemRing l E T).obj.obj U) y z hz

private theorem unit_pure {T : Scheme.{u}} {c : Chern l E T}
    (t : Twisting l E c) (U : (ℕ × T.ProEt)ᵒᵖ)
    (z : (t.equivalence.functor.obj (coefficient T (Arings l E T))).val.obj U) :
    HEq z (pure l E c (coefficient T (Arings l E T)) U
      (1 : (systemRing l E T).obj.obj U) (t.unitIso.hom.val.app U z)) := by
  let y := t.unitIso.hom.val.app U z
  have hF := congrArg
    (fun F : Systems T (Arings l E T) ⥤ Systems T (Arings l E T) ↦
      ((F.obj (coefficient T (Arings l E T))).val.obj U : Type (u + 1))) t.forward
  let w : (t.equivalence.functor.obj (coefficient T (Arings l E T))).val.obj U :=
    cast hF.symm (pure l E c (coefficient T (Arings l E T)) U
      (1 : (systemRing l E T).obj.obj U) y)
  have hw : HEq w (pure l E c (coefficient T (Arings l E T)) U
      (1 : (systemRing l E T).obj.obj U) y) := cast_heq _ _
  have hu := unit_one l E t U y w hw
  have hi : Function.Injective (t.unitIso.hom.val.app U) := by
    apply Function.LeftInverse.injective (g := t.unitIso.inv.val.app U)
    intro x
    exact congrArg (fun k ↦ k.val.app U x) t.unitIso.hom_inv_id
  have hwz : w = z := hi hu
  simpa only [hwz] using hw

private theorem positive_map_pure {T : Scheme.{u}} (c : Chern l E T)
    (F : Systems T (Arings l E T) ⥤ Systems T (Arings l E T))
    (hF : F = positive l E c) {M N : Systems T (Arings l E T)} (a : M ⟶ N)
    (U : (ℕ × T.ProEt)ᵒᵖ) (x : M.val.obj U)
    (y : (lineModule l E c).val.obj U) (z : (F.obj M).val.obj U)
    (hz : HEq z (pure l E c M U x y)) :
    HEq ((F.map a).val.app U z) (pure l E c N U (a.val.app U x) y) := by
  subst F
  cases eq_of_heq hz
  let := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  let := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (Scheme.ProEt.topology T))
  apply heq_of_eq
  have h := (PresheafOfModules.sheafificationAdjunction
    (R := SemilinearSections.ring (coefficientSequenceTopology (Scheme.ProEt.topology T))
      (systemRing l E T)) (𝟙 _)).unit.naturality
    (SheafOfModules.siteTensorHom a.val (lineModule l E c).val)
  exact (congrArg (fun k ↦ k.app U (x ⊗ₜ[(systemRing l E T).obj.obj U] y)) h).symm

private theorem coefficient_one
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f) (q : CoefficientPullback l E b f g)
    (n : ℕ) (U : Y.ProEtᵒᵖ) :
    sectionAdjoint l E g q.iso.hom n U (1 : (SpTowerShriek.B l E Y n).obj.obj U) =
      (1 : (SpTowerShriek.B l E X n).obj.obj (chart f U)) := by
  have h := (sectionAdjoint_heq l E g q.iso.hom n U
    (1 : (SpTowerShriek.B l E Y n).obj.obj U)).trans (q.normalization n U
      (1 : (SpTowerShriek.B l E Y n).obj.obj U)
      (1 : (SpTowerShriek.B l E Y n).obj.obj U) HEq.rfl)
  have h1 := ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2}
    f CommRingCat.{u + 1}
    (CommRingCat.of.{u + 1} (ULift.{u + 1} (SpTowerShriek.R l E n)))).hom.app U).hom.map_one
  exact (eq_of_heq h).trans h1

attribute [local irreducible] sectionAdjoint pure positive

set_option backward.isDefEq.respectTransparency false in
-- The normalization fields retain their original direct-image section carriers.
private theorem ordinary_unit_square
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {cY : Chern l E Y} {cX : Chern l E X}
    {tY : Twisting l E cY} {tX : Twisting l E cX}
    (q : CoefficientPullback l E b f g) (r : LinePullback l E f g cY cX)
    (v : PositivePullback l E f g tY tX r) :
    g.pull.map tY.unitIso.hom ≫ r.iso.hom =
      v.iso.hom.app (coefficient Y (Arings l E Y)) ≫
        tX.equivalence.functor.map q.iso.hom ≫ tX.unitIso.hom := by
  apply sectionAdjoint_ext l E g
  intro n U z
  let y := tY.unitIso.hom.val.app (op (n, U.unop)) z
  have hz := unit_pure l E tY (op (n, U.unop)) z
  let V := op (n, (chart f U).unop)
  let oneY : (SpTowerShriek.B l E Y n).obj.obj U := 1
  let x' : (g.pull.obj (coefficient Y (Arings l E Y))).val.obj V :=
    sectionAdjoint l E g (𝟙 (g.pull.obj (coefficient Y (Arings l E Y)))) n U oneY
  let y' : (lineModule l E cX).val.obj V :=
    sectionAdjoint l E g r.iso.hom n U y
  let w' : (tX.equivalence.functor.obj
      (g.pull.obj (coefficient Y (Arings l E Y)))).val.obj V :=
    sectionAdjoint l E g (v.iso.hom.app (coefficient Y (Arings l E Y))) n U z
  have hv : HEq w' (pure l E cX (g.pull.obj (coefficient Y (Arings l E Y))) V x' y') :=
    (sectionAdjoint_heq l E g
      (v.iso.hom.app (coefficient Y (Arings l E Y))) n U z).trans
      (v.normalization (coefficient Y (Arings l E Y)) n U oneY y z x' y' hz
        (sectionAdjoint_heq l E g
          (𝟙 (g.pull.obj (coefficient Y (Arings l E Y)))) n U oneY)
        (sectionAdjoint_heq l E g r.iso.hom n U y))
  have hm := positive_map_pure l E cX tX.equivalence.functor tX.forward
    q.iso.hom V x' y' w' hv
  have hq' : sectionAdjoint l E g q.iso.hom n U oneY =
      q.iso.hom.val.app V x' := by
    have hh := sectionAdjoint_postcomp l E g
      (𝟙 (g.pull.obj (coefficient Y (Arings l E Y)))) q.iso.hom n U oneY
    have hid := congrArg (fun h ↦ sectionAdjoint l E g h n U oneY)
      (Category.id_comp q.iso.hom)
    exact hid.symm.trans hh
  have hqone : q.iso.hom.val.app V x' =
      (1 : (SpTowerShriek.B l E X n).obj.obj (chart f U)) := by
    exact hq'.symm.trans (coefficient_one l E g q n U)
  have hp := congrArg (fun a : (SpTowerShriek.B l E X n).obj.obj (chart f U) ↦
    pure l E cX (coefficient X (Arings l E X)) V a y') hqone
  have hm1 := hm.trans (heq_of_eq hp)
  have hX := unit_one l E tX V y' _ hm1
  have hleft := sectionAdjoint_precomp l E g tY.unitIso.hom r.iso.hom n U z
  have hright := sectionAdjoint_postcomp l E g
    (v.iso.hom.app (coefficient Y (Arings l E Y)))
    (tX.equivalence.functor.map q.iso.hom ≫ tX.unitIso.hom) n U z
  exact hleft.trans (hX.symm.trans hright.symm)

/-- The positive pullback comparison respects the coefficient-to-line unit.

Source: `sk-prop-diagonal-tower-trace.proof.md`, paragraph (1), twisting the
unit component; the section normalizations in `TowerClassTwisting.lean`.
(blueprint: lem-sfb-positive-pullback-unit-square).

Proof: the normalized ordinary unit isomorphism identifies every section of
its source with a tensor 1 tensor y. Transpose the two arrows under the ordinary
geometric adjunction and test them on sections using the invertible evaluation
comparison. The positive-pullback normalization, tensor functoriality, and the
coefficient normalization at 1 identify the right path with the adjoint of the
line pullback applied to y, which is the left path. Naturality of the exact
single-functor comparisons and compatibility with derived composition transport
this ordinary equality to the displayed derived square. The argument includes
empty charts and requires no nonvanishing hypothesis. -/
theorem positivePullback_unit_square
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} {f : X ⟶ Y}
    (g : SpTowerShriek.Geometry l E b f)
    {cY : Chern l E Y} {cX : Chern l E X}
    {tY : Twisting l E cY} {tX : Twisting l E cX}
    (q : CoefficientPullback l E b f g) (r : LinePullback l E f g cY cX)
    (v : PositivePullback l E f g tY tX r) :
    (SpTowerShriek.pull l E b g).map (tY.positiveUnit l E).hom ≫
        (r.derivedIso l E).hom =
      (v.derivedIso l E).hom.app (unit Y (Arings l E Y)) ≫
        (tX.T l E).map (q.derivedIso l E).hom ≫ (tX.positiveUnit l E).hom := by
  let := g.pullAdditive
  let := g.pullLimits
  let := g.pullColimits
  let := tY.additive
  let := tY.limits
  let := tY.colimits
  let := tX.additive
  let := tX.limits
  let := tX.colimits
  have h := ordinary_unit_square l E g q r v
  dsimp only [Twisting.positiveUnit, LinePullback.derivedIso,
    PositivePullback.derivedIso, CoefficientPullback.derivedIso]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.mapIso_hom,
    Iso.app_hom, Functor.map_comp, Category.assoc]
  erw [(g.pull.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc
    tY.unitIso.hom]
  erw [(tX.equivalence.functor.mapDerivedCategorySingleFunctor 0).hom.naturality_assoc
    q.iso.hom]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso
    tY.equivalence.functor g.pull).inv.app (unit Y (Arings l E Y)))).mp
  simp only [Iso.inv_hom_id_app_assoc]
  dsimp only [SpTowerShriek.pull, Twisting.T]
  have hcomp₁ := Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor
    tY.equivalence.functor g.pull (coefficient Y (Arings l E Y))
  have hcomb := Functor.mapDerivedCategoryNatIso_comp_hom_app_singleFunctor
    g.pull tX.equivalence.functor (tY.equivalence.functor ⋙ g.pull) v.iso
      (coefficient Y (Arings l E Y))
  erw [reassoc_of% hcomp₁, reassoc_of% hcomb]
  have h' := congrArg (fun a ↦
    ((tY.equivalence.functor ⋙ g.pull).mapDerivedCategorySingleFunctor 0).hom.app
      (coefficient Y (Arings l E Y)) ≫
        (DerivedCategory.singleFunctor (Systems X (Arings l E X)) 0).map a) h
  simp only [Functor.map_comp] at h'
  exact h'

end AlgebraicGeometry.ProEtale.SpTowerClasses
