/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarDirectTransitions
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearEvaluationDirectSections
import WeilConjectures.AlgebraicGeometry.StrictTower.ScalarRestrictionOpenSupport
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations

/-! # Scalar restriction and the geometric adjunctions

Source: Stacks Project, Modules on Sites, Tags 03CZ, 03D7 and 03DI
(blueprint: lem-sf-semilinear-scalar-adjunctions). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor
open WeilConjectures.SemilinearSections

namespace AlgebraicGeometry.ProEtale.VaryingRing

variable (R : ℕ → CommRingCat.{u + 1}) (φ : ∀ n : ℕ, R (n + 1) ⟶ R n)
  (B : Type (u + 1)) [CommRing B] (ψ : ∀ n : ℕ, CommRingCat.of B ⟶ R n)

/-- The inverse/direct-image and open-extension comparisons, with their units.
Source: Stacks 03D7, 03D8 and 03DI
(blueprint: lem-sf-semilinear-scalar-adjunctions). -/
structure OrdinaryScalarAdjunctions (C : OrdinaryScalarRestriction R φ B ψ) where
  /-- The inverse-image coefficient comparison b. -/
  b : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    pull R φ f ⋙ C.rho X ≅ C.rho Y ⋙ StrictTower.towerPullback B f
  /-- The direct-image coefficient comparison d. -/
  d : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    push R φ f ⋙ C.rho Y ≅ C.rho X ⋙ StrictTower.towerDirectImage B f
  /-- Direct image is identity on precisely the prescribed fibre-product sections. -/
  d_sections : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X)
      (n : ℕ) (H : Y.ProEtᵒᵖ),
    ∀ x : (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H,
      HEq ((((d f).hom.app M).app (op n)).val.app H x) x
  /-- The orientation is d = mate of the inverse of b. -/
  mate : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    (mateEquiv (moduleAdj R φ f) (scalarTowerAdj B f) (b f).inv) = (d f).hom
  /-- Ordinary open-extension comparison a. -/
  a : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j],
    extension R φ j ⋙ C.rho X ≅ C.rho U ⋙ StrictTower.towerJ B j
  /-- The prescribed open units normalize a. -/
  open_unit : ∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (M : Modules R φ U),
    (C.rho U).map ((moduleJAdj R φ j).unit.app M) ≫
        (b j).hom.app ((extension R φ j).obj M) ≫
        (StrictTower.towerPullback B j).map ((a j).hom.app M) =
      (scalarTowerOpenAdj B j).unit.app ((C.rho U).obj M)

section MateEquations

variable {A₀ A₁ D₀ D₁ : Type*}
  [Category* A₀] [Category* A₁] [Category* D₀] [Category* D₁]
  {L : A₀ ⥤ A₁} {P : A₁ ⥤ A₀} {L' : D₀ ⥤ D₁} {P' : D₁ ⥤ D₀}
  {H : A₀ ⥤ D₀} {K : A₁ ⥤ D₁}

private theorem scalarMateUnit (adj : L ⊣ P) (adj' : L' ⊣ P')
    (b : L ⋙ K ≅ H ⋙ L') (d : P ⋙ H ≅ K ⋙ P')
    (hm : (mateEquiv adj adj' b.inv) = d.hom) (M : A₀) :
    H.map (adj.unit.app M) ≫ d.hom.app (L.obj M) ≫ P'.map (b.hom.app M) =
      adj'.unit.app (H.obj M) := by
  have hu := unit_mateEquiv adj adj' (TwoSquare.mk _ _ _ _ b.inv) M
  change H.map (adj.unit.app M) ≫
      ((mateEquiv adj adj' b.inv).app (L.obj M)) =
    adj'.unit.app (H.obj M) ≫ P'.map (b.inv.app M) at hu
  rw [hm] at hu
  rw [← Category.assoc, hu, Category.assoc, ← P'.map_comp, Iso.inv_hom_id_app]
  change adj'.unit.app (H.obj M) ≫ P'.map (𝟙 (L'.obj (H.obj M))) = _
  erw [P'.map_id, Category.comp_id]

private theorem scalarMateCounit (adj : L ⊣ P) (adj' : L' ⊣ P')
    (b : L ⋙ K ≅ H ⋙ L') (d : P ⋙ H ≅ K ⋙ P')
    (hm : (mateEquiv adj adj' b.inv) = d.hom) (N : A₁) :
    L'.map (d.hom.app N) ≫ adj'.counit.app (K.obj N) =
      b.inv.app (P.obj N) ≫ K.map (adj.counit.app N) := by
  have hc := mateEquiv_counit adj adj' (TwoSquare.mk _ _ _ _ b.inv) N
  change L'.map ((mateEquiv adj adj' b.inv).app N) ≫
      adj'.counit.app (K.obj N) = _ at hc
  rw [hm] at hc
  exact hc

private theorem scalarInverseMate_app (adj : L ⊣ P) (adj' : L' ⊣ P')
    (d : P ⋙ H ⟶ K ⋙ P') (M : A₀) :
    (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ d)).app M) =
      L'.map (H.map (adj.unit.app M)) ≫ L'.map (d.app (L.obj M)) ≫
        adj'.counit.app (K.obj (L.obj M)) := by
  rw [mateEquiv_symm_apply]
  simp only [TwoSquare.mk, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, Functor.comp_map,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    CategoryTheory.Functor.map_id, Functor.comp_obj,
    Category.id_comp]
  exact congrArg (fun q ↦ L'.map (H.map (adj.unit.app M)) ≫
    L'.map (d.app (L.obj M)) ≫ q)
      (Category.comp_id (adj'.counit.app (K.obj (L.obj M))))

private theorem scalarInverseMate_isIso (adj : L ⊣ P) (adj' : L' ⊣ P')
    (d : P ⋙ H ≅ K ⋙ P') [IsIso adj.unit]
    (hs : ∀ M : A₀, IsIso (adj'.counit.app (K.obj (L.obj M)))) :
    IsIso (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ d.hom))) := by
  have h (M : A₀) : IsIso
      ((((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ d.hom))).app M) := by
    rw [scalarInverseMate_app]
    have := hs M
    infer_instance
  exact NatIso.isIso_of_isIso_app _

end MateEquations

/-- The direct-image mate equation implies preservation of the specified unit.
Source: Stacks 03D7; the ordinary adjunction mate identity
(blueprint: lem-sf-semilinear-scalar-adjunctions).
Proof: use the unit equation for mates and cancel b inverse against b. -/
theorem OrdinaryScalarAdjunctions.unit (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ Y) :
    (C.rho Y).map ((moduleAdj R φ f).unit.app M) ≫
        (G.d f).hom.app ((pull R φ f).obj M) ≫
        (StrictTower.towerDirectImage B f).map ((G.b f).hom.app M) =
      (scalarTowerAdj B f).unit.app ((C.rho Y).obj M) :=
  scalarMateUnit (moduleAdj R φ f) (scalarTowerAdj B f) (G.b f) (G.d f) (G.mate f) M

/-- The direct-image mate equation implies preservation of the specified counit.
Source: Stacks 03D7; the ordinary adjunction mate identity
(blueprint: lem-sf-semilinear-scalar-adjunctions).
Proof: apply the counit equation for mates to b inverse and substitute the mate equation. -/
theorem OrdinaryScalarAdjunctions.counit (C : OrdinaryScalarRestriction R φ B ψ)
    (G : OrdinaryScalarAdjunctions R φ B ψ C)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Modules R φ X) :
    (StrictTower.towerPullback B f).map ((G.d f).hom.app N) ≫
        (scalarTowerAdj B f).counit.app ((C.rho X).obj N) =
      (G.b f).inv.app ((push R φ f).obj N) ≫
        (C.rho X).map ((moduleAdj R φ f).counit.app N) :=
  scalarMateCounit (moduleAdj R φ f) (scalarTowerAdj B f) (G.b f) (G.d f) (G.mate f) N

private theorem scalarCoefficientSquare {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (StrictTower.constantRingIso B f).hom ≫ ordinaryScalarMap R B ψ X n =
      (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).map
          (ordinaryScalarMap R B ψ Y n) ≫ (StrictTower.constantRingIso (R n) f).hom := by
  exact (Scheme.proEtaleConstantInverseImageMap_naturality f (a := ψ n)).symm

private def scalarLevelDirect {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    StrictTower.moduleDirectImage (R n) f ⋙ res (ordinaryScalarMap R B ψ Y n) ≅
      res (ordinaryScalarMap R B ψ X n) ⋙ StrictTower.moduleDirectImage B f :=
  Scheme.proEtaleRingRestrictionDirectImage f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (scalarCoefficientSquare R B ψ f n)

private theorem scalarLevelDirect_heq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : StrictTower.Modules (R n) X) (H : Y.ProEtᵒᵖ)
    (x : ((res (ordinaryScalarMap R B ψ Y n)).obj
      ((StrictTower.moduleDirectImage (R n) f).obj M)).val.obj H) :
    HEq (((scalarLevelDirect R B ψ f n).hom.app M).val.app H x) x := by
  exact heq_of_eq ((Classical.choose_spec
    (Scheme.proEtaleRingRestrictionDirectImage_existsUnique f
      (StrictTower.coefficients B Y) (coefficients R Y n)
      (StrictTower.coefficients B X) (coefficients R X n)
      (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
      (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
      (scalarCoefficientSquare R B ψ f n))).1 M H x)

private theorem scalarRes_heq {X : Scheme.{u}} (n : ℕ)
    {M N : StrictTower.Modules (R n) X} (q : M ⟶ N) (H : X.ProEtᵒᵖ)
    (x : ((res (ordinaryScalarMap R B ψ X n)).obj M).val.obj H)
    (h : ∀ y : M.val.obj H, HEq (q.val.app H y) y) :
    HEq (((res (ordinaryScalarMap R B ψ X n)).map q).val.app H x) x := by
  exact h x

attribute [local irreducible] scalarLevelDirect

private def scalarDirectLevel (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    push R φ f ⋙ C.rho Y ⋙
        (evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n) ≅
      (C.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n)) ⋙
        StrictTower.moduleDirectImage B f := by
  let a : push R φ f ⋙ C.rho Y ⋙
      (evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n) ≅
      push R φ f ⋙ eval R φ Y n ⋙ res (ordinaryScalarMap R B ψ Y n) :=
    isoWhiskerLeft (push R φ f) (C.level Y n)
  let b : push R φ f ⋙ eval R φ Y n ⋙ res (ordinaryScalarMap R B ψ Y n) ≅
      eval R φ X n ⋙ StrictTower.moduleDirectImage (R n) f ⋙
        res (ordinaryScalarMap R B ψ Y n) :=
    (associator (push R φ f) (eval R φ Y n) (res (ordinaryScalarMap R B ψ Y n))).symm ≪≫
      isoWhiskerRight (moduleEvalP R φ f n) (res (ordinaryScalarMap R B ψ Y n)) ≪≫
        associator (eval R φ X n) (StrictTower.moduleDirectImage (R n) f)
          (res (ordinaryScalarMap R B ψ Y n))
  let c : eval R φ X n ⋙ StrictTower.moduleDirectImage (R n) f ⋙
        res (ordinaryScalarMap R B ψ Y n) ≅
      eval R φ X n ⋙ res (ordinaryScalarMap R B ψ X n) ⋙
        StrictTower.moduleDirectImage B f :=
    isoWhiskerLeft (eval R φ X n) (scalarLevelDirect R B ψ f n)
  let d : eval R φ X n ⋙ res (ordinaryScalarMap R B ψ X n) ⋙
        StrictTower.moduleDirectImage B f ≅
      (C.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n)) ⋙
        StrictTower.moduleDirectImage B f :=
    (associator (eval R φ X n) (res (ordinaryScalarMap R B ψ X n))
      (StrictTower.moduleDirectImage B f)).symm ≪≫
      isoWhiskerRight (C.level X n).symm (StrictTower.moduleDirectImage B f)
  exact a ≪≫ b ≪≫ c ≪≫ d

private def scalarDirectComponent (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) (n : ℕ) :
    (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)) ≅
      (StrictTower.moduleDirectImage B f).obj (((C.rho X).obj M).obj (op n)) :=
  (scalarDirectLevel R φ B ψ C f n).app M

attribute [local irreducible] scalarDirectLevel scalarDirectComponent

private theorem scalarDirectComponent_word (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) (n : ℕ) :
    (scalarDirectComponent R φ B ψ C f M n).hom ≫
        (StrictTower.moduleDirectImage B f).map ((C.level X n).hom.app M) =
      (C.level Y n).hom.app ((push R φ f).obj M) ≫
        (res (ordinaryScalarMap R B ψ Y n)).map ((moduleEvalP R φ f n).hom.app M) ≫
        (scalarLevelDirect R B ψ f n).hom.app ((eval R φ X n).obj M) := by
  simp only [scalarDirectComponent, scalarDirectLevel, Iso.trans_hom, Iso.app_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app,
    whiskerRight_app, Iso.symm_hom, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  rw [← (StrictTower.moduleDirectImage B f).map_comp, Iso.inv_hom_id_app,
    (StrictTower.moduleDirectImage B f).map_id]
  simp only [Functor.comp_obj, CategoryTheory.evaluation_obj_obj, Category.comp_id]

private theorem scalarPush_heq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : StrictTower.Modules B X} (q : M ⟶ N) (H : Y.ProEtᵒᵖ)
    (x : ((StrictTower.moduleDirectImage B f).obj M).val.obj H)
    (h : ∀ (V : X.ProEtᵒᵖ) (y : M.val.obj V), HEq (q.val.app V y) y) :
    HEq (((StrictTower.moduleDirectImage B f).map q).val.app H x) x :=
  h ((Scheme.proEtaleBaseChange f).op.obj H) x

private theorem scalarDirectComponent_level (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) (n : ℕ) (H : Y.ProEtᵒᵖ)
    (x : (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H) :
    HEq (((StrictTower.moduleDirectImage B f).map ((C.level X n).hom.app M)).val.app H
      ((scalarDirectComponent R φ B ψ C f M n).hom.val.app H x))
      (((C.level Y n).hom.app ((push R φ f).obj M)).val.app H x) := by
  have h := congrArg (fun q :
      (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)) ⟶
        (StrictTower.moduleDirectImage B f).obj
          ((res (ordinaryScalarMap R B ψ X n)).obj ((eval R φ X n).obj M)) ↦
      q.val.app H x) (scalarDirectComponent_word R φ B ψ C f M n)
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply] at h
  exact (heq_of_eq h).trans ((scalarLevelDirect_heq R B ψ f n
    ((eval R φ X n).obj M) H _).trans
      (scalarRes_heq R B ψ n ((moduleEvalP R φ f n).hom.app M) H _
        (fun y ↦ moduleEvalP_sections_heq R φ f M n H y)))

private theorem scalarDirectComponent_sections (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) (n : ℕ) (H : Y.ProEtᵒᵖ)
    (x : (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H) :
    HEq ((scalarDirectComponent R φ B ψ C f M n).hom.val.app H x) x := by
  have h := scalarPush_heq B f ((C.level X n).hom.app M) H
    ((scalarDirectComponent R φ B ψ C f M n).hom.val.app H x)
    (fun V y ↦ C.level_sections X n M V y)
  exact h.symm.trans ((scalarDirectComponent_level R φ B ψ C f M n H x).trans
    (C.level_sections Y n ((push R φ f).obj M) H x))

private theorem scalarDirectComponent_step (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) (n : ℕ) :
    (((C.rho Y).obj ((push R φ f).obj M)).map (homOfLE (Nat.le_succ n)).op) ≫
        (scalarDirectComponent R φ B ψ C f M n).hom =
      (scalarDirectComponent R φ B ψ C f M (n + 1)).hom ≫
        (StrictTower.moduleDirectImage B f).map
          (((C.rho X).obj M).map (homOfLE (Nat.le_succ n)).op) :=
  ordinaryScalarDirectComponents_step R φ B ψ C f M
    (scalarDirectComponent R φ B ψ C f M)
    (scalarDirectComponent_level R φ B ψ C f M) n

private def scalarDirectApp (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) :
    (C.rho Y).obj ((push R φ f).obj M) ≅
      (StrictTower.towerDirectImage B f).obj ((C.rho X).obj M) := by
  let d : (C.rho Y).obj ((push R φ f).obj M) ⟶
      (StrictTower.towerDirectImage B f).obj ((C.rho X).obj M) := NatTrans.ofOpSequence
    (fun n ↦ (scalarDirectComponent R φ B ψ C f M n).hom)
    (scalarDirectComponent_step R φ B ψ C f M)
  have (n : ℕᵒᵖ) : IsIso (d.app n) := by
    change IsIso (scalarDirectComponent R φ B ψ C f M n.unop).hom
    infer_instance
  have : IsIso d := NatIso.isIso_of_isIso_app d
  exact asIso d

private def scalarDirect (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    push R φ f ⋙ C.rho Y ≅ C.rho X ⋙ StrictTower.towerDirectImage B f :=
  NatIso.ofComponents (scalarDirectApp R φ B ψ C f) (by
    intro M N m
    apply NatTrans.ext
    funext n
    change ((C.rho Y).map ((push R φ f).map m)).app n ≫
        (scalarDirectComponent R φ B ψ C f N n.unop).hom =
      (scalarDirectComponent R φ B ψ C f M n.unop).hom ≫
        (StrictTower.moduleDirectImage B f).map (((C.rho X).map m).app n)
    have h := (scalarDirectLevel R φ B ψ C f n.unop).hom.naturality m
    change ((C.rho Y).map ((push R φ f).map m)).app n ≫
        (scalarDirectLevel R φ B ψ C f n.unop).hom.app N =
      (scalarDirectLevel R φ B ψ C f n.unop).hom.app M ≫
        (StrictTower.moduleDirectImage B f).map (((C.rho X).map m).app n) at h
    simpa only [scalarDirectComponent, Iso.app_hom] using h)

private theorem scalarDirect_component (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) (n : ℕ) :
    (((scalarDirect R φ B ψ C f).hom.app M).app (op n)) =
      (scalarDirectLevel R φ B ψ C f n).hom.app M := by
  change (scalarDirectComponent R φ B ψ C f M n).hom = _
  simp only [scalarDirectComponent, Iso.app_hom]

private theorem scalarDirect_sections (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ X) (n : ℕ) (H : Y.ProEtᵒᵖ)
    (x : (((C.rho Y).obj ((push R φ f).obj M)).obj (op n)).val.obj H) :
    HEq ((((scalarDirect R φ B ψ C f).hom.app M).app (op n)).val.app H x) x := by
  change HEq ((scalarDirectComponent R φ B ψ C f M n).hom.val.app H x) x
  exact scalarDirectComponent_sections R φ B ψ C f M n H x

attribute [local irreducible] scalarDirect

private def scalarLevelPullInv {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    res (ordinaryScalarMap R B ψ Y n) ⋙ StrictTower.modulePullback B f ⟶
      StrictTower.modulePullback (R n) f ⋙ res (ordinaryScalarMap R B ψ X n) :=
  Scheme.proEtaleRingRestrictionPullbackInv f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (scalarCoefficientSquare R B ψ f n)

private theorem scalarLevelPullInv_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    IsIso (scalarLevelPullInv R B ψ f n) :=
  Scheme.proEtaleRingRestrictionPullbackInv_isIso f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (scalarCoefficientSquare R B ψ f n)

attribute [local irreducible] scalarLevelPullInv

private abbrev scalarLevelAdj {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    StrictTower.modulePullback (R n) f ⊣ StrictTower.moduleDirectImage (R n) f :=
  Scheme.proEtaleRingModuleAdjunction f (coefficients R Y n)
    (coefficients R X n) (StrictTower.constantRingIso (R n) f)

private abbrev scalarBAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :
    StrictTower.modulePullback B f ⊣ StrictTower.moduleDirectImage B f :=
  Scheme.proEtaleRingModuleAdjunction f (StrictTower.coefficients B Y)
    (StrictTower.coefficients B X) (StrictTower.constantRingIso B f)

private theorem scalarLevelPullInv_mate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (scalarLevelAdj R f n) (scalarBAdj B f)
      (TwoSquare.mk _ _ _ _ (scalarLevelPullInv R B ψ f n))) =
        (scalarLevelDirect R B ψ f n).hom := by
  unfold scalarLevelPullInv scalarLevelDirect
  have h := Scheme.restrictionPullback_mate f
    (StrictTower.coefficients B Y) (coefficients R Y n)
    (StrictTower.coefficients B X) (coefficients R X n)
    (ordinaryScalarMap R B ψ Y n) (ordinaryScalarMap R B ψ X n)
    (StrictTower.constantRingIso B f) (StrictTower.constantRingIso (R n) f)
    (scalarCoefficientSquare R B ψ f n)
  dsimp only [scalarLevelPullInv, scalarLevelDirect, scalarLevelAdj, scalarBAdj,
    StrictTower.modulePullback, StrictTower.moduleDirectImage, res,
    Scheme.proEtaleRingRestrictScalars, StrictTower.coefficients, coefficients,
    CommRingCat.of_carrier, TwoSquare.mk] at h ⊢
  exact h

private theorem scalarEvalPull_mate {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (moduleAdj R φ f) (scalarLevelAdj R f n)
      (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv)) =
        (moduleEvalP R φ f n).hom := by
  have h := inverseMateEqOfUnit (moduleAdj R φ f) (scalarLevelAdj R f n)
    (eval R φ Y n) (eval R φ X n) (moduleEvalP R φ f n).hom
    (moduleEvalG R φ f n) (moduleEvalG_existsUnique R φ f n).choose_spec.1
  have hs : (mateEquiv (moduleAdj R φ f) (scalarLevelAdj R f n)).symm
      (TwoSquare.mk _ _ _ _ (moduleEvalP R φ f n).hom) =
        TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact congr_app h M
  rw [← hs, Equiv.apply_symm_apply]

private def scalarInverseLevel (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (C.rho Y ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n)) ⋙
        StrictTower.modulePullback B f ≅
      pull R φ f ⋙ C.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) := by
  let a : (C.rho Y ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n)) ⋙
      StrictTower.modulePullback B f ≅
      eval R φ Y n ⋙ res (ordinaryScalarMap R B ψ Y n) ⋙
        StrictTower.modulePullback B f :=
    isoWhiskerRight (C.level Y n) (StrictTower.modulePullback B f) ≪≫
        associator (eval R φ Y n) (res (ordinaryScalarMap R B ψ Y n))
          (StrictTower.modulePullback B f)
  let b : eval R φ Y n ⋙ res (ordinaryScalarMap R B ψ Y n) ⋙
      StrictTower.modulePullback B f ≅
      eval R φ Y n ⋙ StrictTower.modulePullback (R n) f ⋙
        res (ordinaryScalarMap R B ψ X n) :=
    isoWhiskerLeft (eval R φ Y n)
      (@asIso _ _ _ _ (scalarLevelPullInv R B ψ f n)
        (scalarLevelPullInv_isIso R B ψ f n))
  let c : eval R φ Y n ⋙ StrictTower.modulePullback (R n) f ⋙
      res (ordinaryScalarMap R B ψ X n) ≅
      pull R φ f ⋙ eval R φ X n ⋙ res (ordinaryScalarMap R B ψ X n) :=
    (associator (eval R φ Y n) (StrictTower.modulePullback (R n) f)
      (res (ordinaryScalarMap R B ψ X n))).symm ≪≫
      isoWhiskerRight (moduleEvalG R φ f n).symm (res (ordinaryScalarMap R B ψ X n)) ≪≫
        associator (pull R φ f) (eval R φ X n) (res (ordinaryScalarMap R B ψ X n))
  let d : pull R φ f ⋙ eval R φ X n ⋙ res (ordinaryScalarMap R B ψ X n) ≅
      pull R φ f ⋙ C.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n) :=
    isoWhiskerLeft (pull R φ f) (C.level X n).symm
  exact a ≪≫ b ≪≫ c ≪≫ d

attribute [local irreducible] scalarInverseLevel

private theorem scalarInverseLevel_mate (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    (mateEquiv (moduleAdj R φ f) (scalarBAdj B f)
      (TwoSquare.mk
        (C.rho Y ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n))
        (pull R φ f) (StrictTower.modulePullback B f)
        (C.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n))
        (scalarInverseLevel R φ B ψ C f n).hom)) =
        (scalarDirectLevel R φ B ψ C f n).hom := by
  let q : TwoSquare (eval R φ Y n ⋙ res (ordinaryScalarMap R B ψ Y n))
      (pull R φ f) (StrictTower.modulePullback B f)
      (eval R φ X n ⋙ res (ordinaryScalarMap R B ψ X n)) :=
    (TwoSquare.mk (eval R φ Y n) (pull R φ f) (StrictTower.modulePullback (R n) f)
      (eval R φ X n) (moduleEvalG R φ f n).inv).hComp
      (TwoSquare.mk (res (ordinaryScalarMap R B ψ Y n))
        (StrictTower.modulePullback (R n) f) (StrictTower.modulePullback B f)
        (res (ordinaryScalarMap R B ψ X n)) (scalarLevelPullInv R B ψ f n))
  have hq : TwoSquare.mk _ _ _ _ (scalarInverseLevel R φ B ψ C f n).hom =
      (q.whiskerTop (C.level Y n).hom).whiskerBottom (C.level X n).inv := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    simp only [scalarInverseLevel, q, TwoSquare.hComp, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, TwoSquare.mk, Iso.trans_hom, NatTrans.comp_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Iso.symm_hom, asIso_hom, Category.assoc]
  rw [hq, mateEquiv_whiskerTop_whiskerBottom]
  have h := mateEquiv_vcomp (moduleAdj R φ f) (scalarLevelAdj R f n) (scalarBAdj B f)
    (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv)
    (TwoSquare.mk _ _ _ _ (scalarLevelPullInv R B ψ f n))
  have h₁ : mateEquiv (moduleAdj R φ f) (scalarLevelAdj R f n)
      (TwoSquare.mk _ _ _ _ (moduleEvalG R φ f n).inv) =
        TwoSquare.mk _ _ _ _ (moduleEvalP R φ f n).hom := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact congr_app (scalarEvalPull_mate R φ f n) M
  have h₂ : mateEquiv (scalarLevelAdj R f n) (scalarBAdj B f)
      (TwoSquare.mk _ _ _ _ (scalarLevelPullInv R B ψ f n)) =
        TwoSquare.mk _ _ _ _ (scalarLevelDirect R B ψ f n).hom := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    exact congr_app (scalarLevelPullInv_mate R B ψ f n) M
  change mateEquiv (moduleAdj R φ f) (scalarBAdj B f) q = _ at h
  rw [h, h₁, h₂]
  apply NatTrans.ext
  funext M
  simp only [scalarDirectLevel, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.vComp, TwoSquare.mk, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Iso.symm_hom, Category.assoc]

private def scalarInverse (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    C.rho Y ⋙ StrictTower.towerPullback B f ⟶ pull R φ f ⋙ C.rho X :=
  ((mateEquiv (moduleAdj R φ f) (scalarTowerAdj B f)).symm
    (TwoSquare.mk _ _ _ _ (scalarDirect R φ B ψ C f).hom))

private theorem scalarInverse_component (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Modules R φ Y) (n : ℕ) :
    ((scalarInverse R φ B ψ C f).app M).app (op n) =
      (scalarInverseLevel R φ B ψ C f n).hom.app M := by
  apply ((scalarBAdj B f).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  have ht := congrArg (fun q ↦ q.app (op n))
    (unit_mateEquiv_symm (moduleAdj R φ f) (scalarTowerAdj B f)
      (TwoSquare.mk _ _ _ _ (scalarDirect R φ B ψ C f).hom) M)
  have hl := unit_mateEquiv (moduleAdj R φ f) (scalarBAdj B f)
    (TwoSquare.mk
      (C.rho Y ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n))
      (pull R φ f) (StrictTower.modulePullback B f)
      (C.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n))
      (scalarInverseLevel R φ B ψ C f n).hom) M
  change ((C.rho Y).map ((moduleAdj R φ f).unit.app M)).app (op n) ≫
      ((mateEquiv (moduleAdj R φ f) (scalarBAdj B f)
        (TwoSquare.mk
          (C.rho Y ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B Y)).obj (op n))
          (pull R φ f) (StrictTower.modulePullback B f)
          (C.rho X ⋙ (evaluation ℕᵒᵖ (StrictTower.Modules B X)).obj (op n))
          (scalarInverseLevel R φ B ψ C f n).hom)).app
            ((pull R φ f).obj M)) =
    (scalarBAdj B f).unit.app (((C.rho Y).obj M).obj (op n)) ≫
      (StrictTower.moduleDirectImage B f).map
        ((scalarInverseLevel R φ B ψ C f n).hom.app M) at hl
  rw [scalarInverseLevel_mate R φ B ψ C f n] at hl
  change ((C.rho Y).map ((moduleAdj R φ f).unit.app M)).app (op n) ≫
      ((scalarDirect R φ B ψ C f).hom.app ((pull R φ f).obj M)).app (op n) =
    (scalarBAdj B f).unit.app (((C.rho Y).obj M).obj (op n)) ≫
      (StrictTower.moduleDirectImage B f).map
        (((scalarInverse R φ B ψ C f).app M).app (op n)) at ht
  rw [scalarDirect_component R φ B ψ C f ((pull R φ f).obj M) n] at ht
  exact ht.symm.trans hl

private theorem scalarInverse_isIso (C : OrdinaryScalarRestriction R φ B ψ)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : IsIso (scalarInverse R φ B ψ C f) := by
  have (M : Modules R φ Y) (n : ℕᵒᵖ) :
      IsIso (((scalarInverse R φ B ψ C f).app M).app n) := by
    rw [scalarInverse_component R φ B ψ C f M n.unop]
    infer_instance
  have (M : Modules R φ Y) : IsIso ((scalarInverse R φ B ψ C f).app M) :=
    NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

attribute [local irreducible] scalarInverse

private theorem scalarOpenCounit_isIso (C : OrdinaryScalarRestriction R φ B ψ)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] (M : Modules R φ U) :
    IsIso ((scalarTowerOpenAdj B j).counit.app
      ((C.rho X).obj ((extension R φ j).obj M))) := by
  have h (n : ℕᵒᵖ) : IsIso (((scalarTowerOpenAdj B j).counit.app
      ((C.rho X).obj ((extension R φ j).obj M))).app n) := by
    let e := (extensionEvaluation_exists R φ j n.unop).some
    let q : (((C.rho X).obj ((extension R φ j).obj M)).obj n) ≅
        (res (ordinaryScalarMap R B ψ X n.unop)).obj
          ((StrictTower.moduleJ (R n.unop) j).obj ((eval R φ U n.unop).obj M)) :=
      (C.level X n.unop).app ((extension R φ j).obj M) ≪≫
        (res (ordinaryScalarMap R B ψ X n.unop)).mapIso (e.app M)
    have ht := StrictTower.restrictScalars_openCounit_isIso
      (ordinaryScalarMap R B ψ X n.unop) j ((eval R φ U n.unop).obj M)
    change IsIso ((StrictTower.moduleJAdj B j).counit.app
      (((C.rho X).obj ((extension R φ j).obj M)).obj n))
    exact (NatTrans.isIso_app_iff_of_iso (StrictTower.moduleJAdj B j).counit q).2 ht
  exact NatIso.isIso_of_isIso_app _

private def scalarOpenInverse (C : OrdinaryScalarRestriction R φ B ψ)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    C.rho U ⋙ StrictTower.towerJ B j ⟶ extension R φ j ⋙ C.rho X :=
  ((mateEquiv (moduleJAdj R φ j) (scalarTowerOpenAdj B j)).symm
    (TwoSquare.mk _ _ _ _
      (@asIso _ _ _ _ (scalarInverse R φ B ψ C j)
        (scalarInverse_isIso R φ B ψ C j)).inv))

private theorem scalarOpenInverse_isIso (C : OrdinaryScalarRestriction R φ B ψ)
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    IsIso (scalarOpenInverse R φ B ψ C j) := by
  have := moduleJAdj_unit_isIso R φ j
  exact scalarInverseMate_isIso (moduleJAdj R φ j) (scalarTowerOpenAdj B j)
    (@asIso _ _ _ _ (scalarInverse R φ B ψ C j)
      (scalarInverse_isIso R φ B ψ C j)).symm (scalarOpenCounit_isIso R φ B ψ C j)

attribute [local irreducible] scalarOpenInverse

/-- Scalar restriction commutes with inverse/direct images and open extension.
Source: Stacks 03D7 (lemma-adjoint-pullback-pushforward-modules), 03D8 and 03DI
(blueprint: lem-sf-semilinear-scalar-adjunctions).
Proof: compose the prescribed level identifications, normalized evaluation and
single-ring direct-image comparisons to construct d at each level. The restriction
transition equations assemble these components, and their normalizations give the
pointwise section identity. Define b inverse as the inverse adjunction mate of d.
Pasting the evaluation mate with the existing invertible single-ring pullback mate
identifies every component with a composite of isomorphisms, so b is invertible.
The mate correspondence gives the unit and counit equations. The single-sheaf
open-support lemma makes the constant-coefficient open counit invertible at every
level of the restricted varying-ring extension. The inverse open mate of b is
therefore invertible; its inverse defines a, with the required open unit. -/
theorem ordinaryScalarAdjunctions (hψ : ∀ n : ℕ, ψ (n + 1) ≫ φ n = ψ n)
    (C : OrdinaryScalarRestriction R φ B ψ) :
    Nonempty (OrdinaryScalarAdjunctions R φ B ψ C) := by
  have _ := hψ
  let b {X Y : Scheme.{u}} (f : X ⟶ Y) :=
    (@asIso _ _ _ _ (scalarInverse R φ B ψ C f)
      (scalarInverse_isIso R φ B ψ C f)).symm
  let a {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
    (@asIso _ _ _ _ (scalarOpenInverse R φ B ψ C j)
      (scalarOpenInverse_isIso R φ B ψ C j)).symm
  have hm {X Y : Scheme.{u}} (f : X ⟶ Y) :
      (mateEquiv (moduleAdj R φ f) (scalarTowerAdj B f) (b f).inv) =
        (scalarDirect R φ B ψ C f).hom := by
    simp only [b, Iso.symm_inv, asIso_hom, scalarInverse, Equiv.apply_symm_apply]
  refine ⟨{
    b := b
    d := scalarDirect R φ B ψ C
    d_sections := ?_
    mate := hm
    a := a
    open_unit := ?_
  }⟩
  · intro X Y f M n H x
    exact scalarDirect_sections R φ B ψ C f M n H x
  · intro U X j _ M
    apply scalarMateUnit (moduleJAdj R φ j) (scalarTowerOpenAdj B j) (a j) (b j) _ M
    simp only [a, b, Iso.symm_inv, Iso.symm_hom, asIso_hom,
      scalarOpenInverse, Equiv.apply_symm_apply]

end AlgebraicGeometry.ProEtale.VaryingRing
