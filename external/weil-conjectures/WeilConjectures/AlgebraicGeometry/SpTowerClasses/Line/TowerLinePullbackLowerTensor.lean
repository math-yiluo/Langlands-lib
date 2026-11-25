/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassPullback
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Line.TowerLineTransitionTensor
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso

/-! # The lower path of root-line pullback on a finite tensor generator -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory Opposite WeilConjectures
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

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

private theorem adjoint_apply (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (adj : proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f)
    {M : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    {N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (a : (proEtaleConstantRingPullback A f).obj M ⟶ N)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((adj.homEquiv _ _) a).val.app U x =
      a.val.app (chart f U)
        ((adj.unit.app M).val.app U x) := by
  rw [Adjunction.homEquiv_unit, evaluated_comp_apply]
  exact pushforward_map_apply A f a U _

private theorem adjoint_pre_apply (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (adj : proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f)
    {M M' : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    {N : proEtaleRingModules X (proEtaleConstantRing X A)}
    (e : M ⟶ M') (k : (proEtaleConstantRingPullback A f).obj M' ⟶ N)
    (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((adj.homEquiv _ _)
      ((proEtaleConstantRingPullback A f).map e ≫ k)).val.app U x =
      ((adj.homEquiv _ _) k).val.app U
        (e.val.app U x) := by
  rw [Adjunction.homEquiv_naturality_left, evaluated_comp_apply]

private theorem adjoint_pre_post_apply (A : Type u) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (adj : proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f)
    {M M' : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    {N N' : proEtaleRingModules X (proEtaleConstantRing X A)}
    (e : M ⟶ M') (k : (proEtaleConstantRingPullback A f).obj M' ⟶ N)
    (j : N ⟶ N') (U : Y.ProEtᵒᵖ) (x : M.val.obj U) :
    ((adj.homEquiv _ _)
      ((proEtaleConstantRingPullback A f).map e ≫ k ≫ j)).val.app U x =
      j.val.app (chart f U)
        (((adj.homEquiv _ _) k).val.app U
          (e.val.app U x)) := by
  rw [adjoint_pre_apply, Adjunction.homEquiv_naturality_right,
    evaluated_comp_apply, pushforward_map_apply]

omit [Fact l.Prime] in
private theorem root_direct_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (U : Y.ProEtᵒᵖ)
    (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj U) :
    (Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U z =
      restrictRoot l f n U z := by
  apply (Scheme.proEtaleRootsOfUnitySections X (l ^ (n + 1)) (chart f U)).injective
  rw [restrictRoot, AddEquiv.apply_symm_apply]
  exact (Scheme.existsUnique_proEtaleRootsOfUnityDirectImageMap f
    (l ^ (n + 1))).exists.choose_spec U z

private theorem root_direct_transition {X Y : Scheme.{u}} (f : X ⟶ Y)
    {m n : ℕ} (h : n ≤ m) (U : Y.ProEtᵒᵖ)
    (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (m + 1))).obj.obj U) :
    restrictRoot l f n U (((roots l Y).map (homOfLE h).op).hom.app U z) =
      (((roots l X).map (homOfLE h).op).hom.app (chart f U)
        (restrictRoot l f m U z)) := by
  let rho : roots l Y ⟶ roots l X ⋙
      proEtaleSheafDirectImage f AddCommGrpCat.{u + 1} :=
    NatTrans.ofOpSequence (fun k ↦
      Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (k + 1))) (fun k ↦ by
        simpa only [roots, Scheme.proEtaleRootsOfUnityTower, Functor.comp_map,
          Functor.ofOpSequence_map_homOfLE_succ] using
            Scheme.roots_direct_transition f (l ^ (k + 1)) (l ^ (k + 2))
              (pow_pos (Fact.out : l.Prime).pos _) (pow_pos (Fact.out : l.Prime).pos _)
              (pow_dvd_pow l (Nat.le_succ (k + 1))))
  have hn := congrArg (fun k ↦ k.hom.app U z) (rho.naturality (homOfLE h).op)
  change (Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (n + 1))).hom.app U
      (((roots l Y).map (homOfLE h).op).hom.app U z) =
    (((roots l X).map (homOfLE h).op).hom.app (chart f U)
      ((Scheme.proEtaleRootsOfUnityDirectImageMap f (l ^ (m + 1))).hom.app U z)) at hn
  simpa only [root_direct_eq] using hn

attribute [local irreducible] lineModule proEtaleRingModulePullback
  proEtaleRingModuleAdjunction

private theorem actual_unit_transition
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : SpTowerShriek.Geometry l E b f) (M : SpTowerShriek.S l E Y)
    {m n : ℕ} (h : n ≤ m) (U : Y.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E Y m).obj M).val.obj U)
    (y : ((SpTowerShriek.ev l E Y n).obj M).val.obj U)
    (hy : HEq (((SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology Y) (SpTowerShriek.B l E Y)
      (SpTowerShriek.tau l E Y) h).app M).val.app U x) y) :
    HEq
      ((((proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).homEquiv _ _)
        ((g.ordinaryPullEvaluation m).inv.app M ≫
          (SemilinearSections.transition.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
            (SpTowerShriek.tau l E X) h).app (g.pull.obj M) ≫
          (SemilinearSections.res.{u + 1, u, u + 1}
            (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
              (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
              (SpTowerShriek.tau l E X) h)).map
            ((g.ordinaryPullEvaluation n).hom.app M))).val.app U x)
      (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((SpTowerShriek.ev l E Y n).obj M)).val.app U y) := by
  have hu := g.ordinaryUnitTransition
  unfold SpTowerShriek.OrdinaryUnitTransition SpTowerShriek.OrdinaryUnitTransitionModel at hu
  exact hu M h U x y hy

private theorem lowerPath_section (A D : Type u) [CommRing A] [CommRing D]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (am : proEtaleConstantRingPullback A f ⊣ proEtaleConstantRingPushforward A f)
    (an : proEtaleConstantRingPullback D f ⊣ proEtaleConstantRingPushforward D f)
    (φ : proEtaleConstantRing X A ⟶ proEtaleConstantRing X D)
    {Mm Am : proEtaleRingModules Y (proEtaleConstantRing Y A)}
    {Mn An : proEtaleRingModules Y (proEtaleConstantRing Y D)}
    {N : proEtaleRingModules X (proEtaleConstantRing X D)}
    (em : Mm ≅ Am) (en : Mn ≅ An)
    (k : (proEtaleConstantRingPullback A f).obj Mm ⟶
      (SemilinearSections.res.{u + 1, u, u + 1} φ).obj
        ((proEtaleConstantRingPullback D f).obj Mn))
    (δ : (proEtaleConstantRingPullback D f).obj An ⟶ N)
    (U : Y.ProEtᵒᵖ) (a : Am.val.obj U) (y : Mn.val.obj U)
    (hu : HEq (((am.homEquiv _ _) k).val.app U (em.inv.val.app U a))
      ((an.unit.app Mn).val.app U y)) :
    HEq (((am.homEquiv _ _)
      ((proEtaleConstantRingPullback A f).map em.inv ≫ k ≫
        (SemilinearSections.res.{u + 1, u, u + 1} φ).map
          ((proEtaleConstantRingPullback D f).map en.hom ≫ δ))).val.app U a)
      (((an.homEquiv _ _) δ).val.app U (en.hom.val.app U y)) := by
  let j := (proEtaleConstantRingPullback D f).map en.hom ≫ δ
  have hr := restrict_map_heq φ j (chart f U) _ _ hu
  have hj := (adjoint_apply D f an j U y).symm
  have hp := adjoint_pre_apply D f an en.hom δ U y
  have hpath := adjoint_pre_post_apply A f am em.inv k
    ((SemilinearSections.res.{u + 1, u, u + 1} φ).map j) U a
  exact (heq_of_eq hpath).trans
    (hr.trans ((heq_of_eq hj).trans (heq_of_eq hp)))

private theorem map_conjugate
    {A B D : Type*} [Category A] [Category B] [Category D]
    (P : A ⥤ D) (R : B ⥤ D) {a a' : A} {b : B} {c : D}
    (e : a ⟶ a') (p : P.obj a' ⟶ c) (t : c ⟶ R.obj b)
    {b' b'' : B} (q : b ⟶ b') (j : b' ⟶ b'') :
    P.map e ≫ p ≫ t ≫ R.map (q ≫ j) =
      P.map e ≫ (p ≫ t ≫ R.map q) ≫ R.map j := by
  simp only [Functor.map_comp, Category.assoc]

/-- A normalized comparison at the lower level computes the adjunct of the lower
path on each higher-level pure tensor. No comparison at the higher level, target
Chern datum, system isomorphism, or horizontal square is assumed or constructed.

Source: current classes blueprint, clause (2), scalar extension of the roots tower;
step 2 of lem-sfb-tower-class-line-pullback-horizontal.
(blueprint: lem-sfb-tower-line-pullback-lower-tensor).

Proof: the ordinaryUnitTransition equation of the repaired Geometry interface
identifies the finite adjunct of the lower horizontal restriction with the lower-level
unit precomposed with the Y transition. Naturality of the finite adjunction and
lineEvaluation_transition_tensor reduce the path on a unit tensor to the assumed
level-n unit-tensor normalization. The root direct-image maps form a natural
transformation of towers: their section formula is restriction along a ring map,
which preserves powers. Its naturality identifies the resulting root with the X
tower transition of the restricted root. The calculation includes empty charts and
equal indices. Only unit tensors are needed for the finite-line universal property.
-/
theorem linePullback_lower_tensor
    {b : SpTowerShriek.Base l E} {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : SpTowerShriek.Geometry l E b f) (cY : Chern l E Y)
    {m n : ℕ} (h : n ≤ m)
    (δ : (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).obj
      (finiteLine l E Y n) ⟶ finiteLine l E X n)
    (hδ : ∀ (U : Y.ProEtᵒᵖ)
      (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (n + 1))).obj.obj U),
      (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv _ _)
        δ).val.app U
          (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
            U.unop 1 z) =
        Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
          (chart f U).unop
          1
          (restrictRoot l f n U z))
    (U : Y.ProEtᵒᵖ)
    (z : (Scheme.proEtaleRootsOfUnitySheaf Y (l ^ (m + 1))).obj.obj U) :
    (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).homEquiv _ _)
      ((proEtaleConstantRingPullback (SpTowerShriek.R l E m) f).map
          (lineEvaluation l E cY m).inv ≫
        (g.ordinaryPullEvaluation m).inv.app (lineModule l E cY) ≫
        (SemilinearSections.transition.{u + 1, u, u + 1}
          (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
          (SpTowerShriek.tau l E X) h).app (g.pull.obj (lineModule l E cY)) ≫
        (SemilinearSections.res.{u + 1, u, u + 1}
          (SemilinearSections.coefficientMap.{u + 1, u, u + 1}
            (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
            (SpTowerShriek.tau l E X) h)).map
          ((g.ordinaryPullEvaluation n).hom.app (lineModule l E cY) ≫
            (proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).map
              (lineEvaluation l E cY n).hom ≫ δ))).val.app U
      (Scheme.tateFiniteTensor Y l (FiniteRing l E m) m (finiteScalar l E m)
        U.unop 1 z) =
      Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
        (chart f U).unop
        1
        (((roots l X).map (homOfLE h).op).hom.app (chart f U)
          (restrictRoot l f m U z)) := by
  let y := (lineEvaluation l E cY n).inv.val.app U
    (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
      U.unop 1 (((roots l Y).map (homOfLE h).op).hom.app U z))
  have hu := actual_unit_transition l E f g (lineModule l E cY) h U
    ((lineEvaluation l E cY m).inv.val.app U
      (Scheme.tateFiniteTensor Y l (FiniteRing l E m) m (finiteScalar l E m)
        U.unop 1 z)) y (lineEvaluation_transition_tensor l E cY h U z)
  let φ := SemilinearSections.coefficientMap.{u + 1, u, u + 1}
    (Scheme.ProEt.topology X) (SpTowerShriek.B l E X) (SpTowerShriek.tau l E X) h
  let k := (g.ordinaryPullEvaluation m).inv.app (lineModule l E cY) ≫
    (SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
      (SpTowerShriek.tau l E X) h).app (g.pull.obj (lineModule l E cY)) ≫
    (SemilinearSections.res.{u + 1, u, u + 1} φ).map
      ((g.ordinaryPullEvaluation n).hom.app (lineModule l E cY))
  have hpath := lowerPath_section (SpTowerShriek.R l E m) (SpTowerShriek.R l E n) f
    (proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f)
    (proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f) φ
    (lineEvaluation l E cY m) (lineEvaluation l E cY n) k δ U
    (Scheme.tateFiniteTensor Y l (FiniteRing l E m) m (finiteScalar l E m)
      U.unop 1 z) y hu
  have he := map_conjugate
    (proEtaleConstantRingPullback (SpTowerShriek.R l E m) f)
    (SemilinearSections.res.{u + 1, u, u + 1} φ)
    (lineEvaluation l E cY m).inv
    ((g.ordinaryPullEvaluation m).inv.app (lineModule l E cY))
    ((SemilinearSections.transition.{u + 1, u, u + 1}
      (Scheme.ProEt.topology X) (SpTowerShriek.B l E X)
      (SpTowerShriek.tau l E X) h).app (g.pull.obj (lineModule l E cY)))
    ((g.ordinaryPullEvaluation n).hom.app (lineModule l E cY))
    ((proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).map
      (lineEvaluation l E cY n).hom ≫ δ)
  have he' := congrArg
    (fun k ↦ (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E m) f).homEquiv
      _ _) k).val.app U
        (Scheme.tateFiniteTensor Y l (FiniteRing l E m) m (finiteScalar l E m)
          U.unop 1 z)) he
  have hy : (lineEvaluation l E cY n).hom.val.app U y =
      Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
        U.unop 1 (((roots l Y).map (homOfLE h).op).hom.app U z) := by
    exact congrArg
      (fun a : finiteLine l E Y n ⟶ finiteLine l E Y n ↦ a.val.app U
        (Scheme.tateFiniteTensor Y l (FiniteRing l E n) n (finiteScalar l E n)
          U.unop 1 (((roots l Y).map (homOfLE h).op).hom.app U z)))
      (lineEvaluation l E cY n).inv_hom_id
  have hgen := congrArg
    (fun w ↦ (((proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).homEquiv
      _ _) δ).val.app U w) hy
  have hroot := congrArg
    (fun w ↦ Scheme.tateFiniteTensor X l (FiniteRing l E n) n (finiteScalar l E n)
      (chart f U).unop 1 w) (root_direct_transition l f h U z)
  have hnorm := hδ U (((roots l Y).map (homOfLE h).op).hom.app U z)
  exact eq_of_heq ((heq_of_eq he').trans (hpath.trans ((heq_of_eq hgen).trans
    ((heq_of_eq hnorm).trans (heq_of_eq hroot)))))

end AlgebraicGeometry.ProEtale.SpTowerClasses
