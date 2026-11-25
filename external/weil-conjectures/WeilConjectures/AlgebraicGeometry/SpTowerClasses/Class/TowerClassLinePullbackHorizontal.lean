/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteTateLineUniversal
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLineTransitionTensor
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLinePullbackLowerTensor

/-! # Horizontal compatibility of the finite root-line comparisons

Source: current classes blueprint, clause (2), scalar extension of the root tower.
(blueprint: lem-sfb-tower-class-line-pullback-horizontal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local implicit_reducible] spCoefficientCommRings Functor.ofOpSequence
  Functor.ofSequence SpTowerShriek.tau MorphismProperty

attribute [local irreducible] Scheme.proEtaleConstantRingComparison
  Scheme.proEtaleRingDirectImageMap

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem evaluated_comp_apply {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u + 1}}
    {M N P : SheafOfModules.{u + 1} R}
    (a : M ⟶ N) (b : N ⟶ P) (U : Cᵒᵖ) (x : M.val.obj U) :
    (a ≫ b).val.app U x = b.val.app U (a.val.app U x) := rfl

private theorem pushforward_map_apply (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (a : M ⟶ N) (U : Y.ProEtᵒᵖ) (x : M.val.obj (chart f U)) :
    ((proEtaleConstantRingPushforward A f).map a).val.app U x =
      a.val.app (chart f U) x := rfl

private theorem restrict_map_heq
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J CommRingCat.{u + 1}} (φ : R ⟶ S)
    {M N : SemilinearSections.Mod.{u + 1, u, u + 1} J S}
    (a : M ⟶ N) (U : Cᵒᵖ)
    (x : ((SemilinearSections.res.{u + 1, u, u + 1} φ).obj M).val.obj U)
    (y : M.val.obj U) (h : HEq x y) :
    HEq (((SemilinearSections.res.{u + 1, u, u + 1} φ).map a).val.app U x)
      (a.val.app U y) := by
  have hx : x = y := eq_of_heq h
  cases hx
  rfl

attribute [local irreducible] lineModule proEtaleRingModulePullback
  proEtaleRingModuleAdjunction

private theorem cancel_conjugate_square
    {C : Type*} [Category C] {A B T V : C}
    (a : A ≅ B) (b : T ≅ V) (f : A ⟶ V) (g : B ⟶ T)
    (h : a.inv ≫ f = g ≫ b.hom) : f ≫ b.inv = a.hom ≫ g := by
  have hh := congrArg (fun k ↦ a.hom ≫ k ≫ b.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using hh

private theorem finiteLine_hom_ext (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (n : ℕ) (κ : ZMod (ℓ ^ (n + 1)) →+* A)
    {N : SheafOfModules.{u + 1}
      ((sheafCompose (Scheme.ProEt.topology T)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (Scheme.tateFiniteCoefficient T A))}
    (f g : Scheme.tateFiniteLine T ℓ A n κ ⟶ N)
    (h : ∀ (U : T.ProEtᵒᵖ)
      (z : (Scheme.proEtaleRootsOfUnitySheaf T (ℓ ^ (n + 1))).obj.obj U),
      f.val.app U (Scheme.tateFiniteTensor T ℓ A n κ U.unop 1 z) =
        g.val.app U (Scheme.tateFiniteTensor T ℓ A n κ U.unop 1 z)) : f = g := by
  obtain ⟨Ψ, _, hp⟩ := finiteTateLine_universal T ℓ A n κ
  apply (Ψ N).injective
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  have hf := hp N f U 1 z
  have hg := hp N g U 1 z
  simpa only [one_smul] using hf.trans ((h U z).trans hg.symm)

/-- The finite coefficient/root formula respects horizontal tower restrictions.

Source: current blueprint `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
scalar extension of the root tower, and the transition calculation in the proof of
`lem-sfb-tower-class-line-pullback-existence`.
(blueprint: lem-sfb-tower-class-line-pullback-horizontal).

Proof: the finite-line universal property reduces equality of linear maps to their
values on generators 1 tensor z. Naturality of the scalar-adjunction unit computes
the line transition on these generators. The rootForget transition equation identifies
the root restriction with the actual roots-tower transition. The actual finite-unit
normalization of Geometry computes the finite adjunct of the lower horizontal path.
Use the assumed level-n normalization there and the level-m normalization on the
other path. Every coefficient map preserves one, and the root direct-image map
commutes with the roots transitions because restriction along a ring map preserves
powers. Thus both adjuncts have the same value on every generator, including on
empty charts. The finite-line universal property gives equality of morphisms, and
cancelling the ordinary pull and line evaluation isomorphisms gives the displayed
horizontal square. No statement about assembly or the tower adjoint is used.
-/
theorem linePullback_components_horizontal
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : SpTowerShriek.Geometry l E b f) (cY : Chern l E Y) (cX : Chern l E X)
    (δ : ∀ n : ℕ,
      (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
        (finiteLine l E Y n) ≅ finiteLine l E X n)
    (hδ : ∀ (n : ℕ) (U : Y.ProEtᵒᵖ)
      (a : (SpTowerShriek.B l E Y n).obj.obj U)
      (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj U),
      (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
        (δ n).hom).val.app U
          (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
            U.unop a z) =
        Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
          (chart f U).unop
          ((Scheme.proEtaleConstantDirectImageMap.{u, u + 2} f CommRingCat.{u + 1}
            (CommRingCat.of (FiniteRing l E n))).hom.app U a)
          (restrictRoot l f n U z)) :
    let d := fun n ↦ (g.ordinaryPullEvaluation n).app (lineModule l E cY) ≪≫
      (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).mapIso
        (lineEvaluation l E cY n) ≪≫ δ n ≪≫ (lineEvaluation l E cX n).symm
    ∀ {m n : ℕ} (h : n ≤ m),
      (SemilinearSections.transition.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app
          (g.pull.obj (lineModule l E cY)) ≫
        (SemilinearSections.res.{u + 1, u, u + 1}
          (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
            (SpTowerShriek.tau l E X) h)).map (d n).hom =
      (d m).hom ≫ (SemilinearSections.transition.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h).app
          (lineModule l E cX) := by
  dsimp only
  intro m n h
  let P := fun k ↦ proEtaleConstantRingPullback (SpTowerShriek.R l E k) f
  let eY := fun k ↦ lineEvaluation l E cY k
  let eX := fun k ↦ lineEvaluation l E cX k
  let p := fun k ↦ (g.ordinaryPullEvaluation k).app (lineModule l E cY)
  let r := SemilinearSections.res.{u + 1, u, u + 1}
    (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
      (SpTowerShriek.tau l E X) h)
  let tY := (SemilinearSections.transition.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
    (SpTowerShriek.tau l E X) h).app (g.pull.obj (lineModule l E cY))
  let tX := (SemilinearSections.transition.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
    (SpTowerShriek.tau l E X) h).app (lineModule l E cX)
  let L := (P m).map (eY m).inv ≫ (p m).inv ≫ tY ≫
    r.map ((p n).hom ≫ (P n).map (eY n).hom ≫ (δ n).hom)
  let R := (δ m).hom ≫ (eX m).inv ≫ tX ≫ r.map (eX n).hom
  have hLR : L = R := by
    apply ((proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).homEquiv _ _).injective
    apply finiteLine_hom_ext Y l (FiniteRing l E m) m (finiteScalar l E m)
    intro U z
    have hL := linePullback_lower_tensor l E f g cY h (δ n).hom
      (fun V w ↦ by simpa only [map_one] using hδ n V 1 w) U z
    have hR := lineEvaluation_transition_tensor l E cX h (chart f U)
      (restrictRoot l f m U z)
    have hc : (eX n).hom.val.app (chart f U)
        ((eX n).inv.val.app (chart f U)
          (Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
            (chart f U).unop 1
            (((roots l X).map (homOfLE h).op).hom.app (chart f U)
              (restrictRoot l f m U z)))) =
        Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
          (chart f U).unop 1
          (((roots l X).map (homOfLE h).op).hom.app (chart f U)
            (restrictRoot l f m U z)) := by
      exact congrArg (fun a : finiteLine l E X n ⟶ finiteLine l E X n ↦
        a.val.app (chart f U)
          (Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
            (chart f U).unop 1
            (((roots l X).map (homOfLE h).op).hom.app (chart f U)
              (restrictRoot l f m U z)))) (eX n).inv_hom_id
    have hr := restrict_map_heq
      (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
        (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
        (SpTowerShriek.tau l E X) h) (eX n).hom (chart f U) _ _ hR
    have hpath : ((eX m).inv ≫ tX ≫ r.map (eX n).hom).val.app (chart f U)
        (Scheme.tateFiniteTensor X l (FiniteRing l E m) m (finiteScalar l E m)
          (chart f U).unop 1 (restrictRoot l f m U z)) =
        Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
          (chart f U).unop 1
          (((roots l X).map (homOfLE h).op).hom.app (chart f U)
            (restrictRoot l f m U z)) := by
      rw [evaluated_comp_apply, evaluated_comp_apply]
      exact eq_of_heq (hr.trans (heq_of_eq hc))
    change (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).homEquiv _ _)
      L).val.app U _ = _ at hL
    refine hL.trans ?_
    dsimp only [R]
    rw [Adjunction.homEquiv_naturality_right, evaluated_comp_apply,
      pushforward_map_apply (SpTowerShriek.R l E m) f
        ((eX m).inv ≫ tX ≫ r.map (eX n).hom) U]
    rw [hδ m U 1 z]
    simp only [map_one]
    exact hpath.symm
  have hsquare := cancel_conjugate_square
    ((p m) ≪≫ (P m).mapIso (eY m)) (r.mapIso (eX n))
    (tY ≫ r.map ((p n).hom ≫ (P n).map (eY n).hom ≫ (δ n).hom))
    ((δ m).hom ≫ (eX m).inv ≫ tX)
    (by simpa only [L, R, Iso.trans_inv, Functor.mapIso_inv,
      Functor.mapIso_hom, Category.assoc] using hLR)
  simpa only [p, P, eY, eX, r, tY, tX, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    Functor.map_comp, Category.assoc] using hsquare

end AlgebraicGeometry.ProEtale.SpTowerClasses
