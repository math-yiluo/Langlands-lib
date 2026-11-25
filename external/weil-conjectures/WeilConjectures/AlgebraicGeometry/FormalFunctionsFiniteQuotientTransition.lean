/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormalFunctionsFinitePullback
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial

/-! # Adjacent-level naturality of the finite quotient comparison

Source: Stacks Project, Tag 02OD, finite-level identifications, and Tags 01F7 and 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-transition)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem finiteι_transition {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (n : ℕ) :
    formalFibreTransition f y n ≫ formalFunctionsFiniteι f y (n + 1) =
      formalFunctionsFiniteι f y n := by
  apply pullback.hom_ext
  · simp only [Category.assoc, formalFunctionsFiniteι, pullback.lift_fst]
    rw [← Category.assoc]
    simp only [formalFibreTransition, pullback.map, pullback.lift_fst]
    rw [Category.assoc, ← Spec.map_comp]
    congr 2
  · simp only [Category.assoc, formalFunctionsFiniteι_snd]
    exact (formalFibreTransition_ι f y n).symm

set_option backward.isDefEq.respectTransparency.types false in
private theorem pushforward_pasting {A B C D : Scheme.{u}}
    (h : A ⟶ B) (k : B ⟶ C) (g : C ⟶ D) (j : A ⟶ C)
    (i : A ⟶ D) (l : B ⟶ D) (hj : h ≫ k = j) (hi : i = j ≫ g)
    (hl : l = k ≫ g) (hil : i = h ≫ l) (F : A.Modules) :
    (Scheme.Modules.pushforwardCongr hi ≪≫
      (Scheme.Modules.pushforwardComp j g).symm).hom.app F =
    (Scheme.Modules.pushforwardCongr hil ≪≫
      (Scheme.Modules.pushforwardComp h l).symm).hom.app F ≫
      (Scheme.Modules.pushforwardCongr hl ≪≫
        (Scheme.Modules.pushforwardComp k g).symm).hom.app
          ((Scheme.Modules.pushforward h).obj F) ≫
      (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforwardComp h k).hom.app F) ≫
      (Scheme.Modules.pushforward g).map ((Scheme.Modules.pushforwardCongr hj).hom.app F) := by
  subst j
  subst i
  subst l
  ext U
  simp [Scheme.Modules.pushforward_map_app]

private theorem adjoint_triangle {A B C D : Scheme.{u}}
    (h : A ⟶ B) (k : B ⟶ C) (g : C ⟶ D) (j : A ⟶ C)
    (i : A ⟶ D) (l : B ⟶ D) (hj : h ≫ k = j) (hi : i = j ≫ g)
    (hl : l = k ≫ g) (hil : i = h ≫ l)
    (adj : Scheme.Modules.tensorPullback g ⊣ Scheme.Modules.pushforward g)
    {F : D.Modules} {H : B.Modules} {K : A.Modules}
    (u : F ⟶ (Scheme.Modules.pushforward i).obj K)
    (v : F ⟶ (Scheme.Modules.pushforward l).obj H)
    (e : (Scheme.Modules.tensorPullback g).obj F ⟶ (Scheme.Modules.pushforward j).obj K)
    (e' : (Scheme.Modules.tensorPullback g).obj F ⟶ (Scheme.Modules.pushforward k).obj H)
    (t : H ⟶ (Scheme.Modules.pushforward h).obj K)
    (he : adj.homEquiv F _ e = u ≫ (Scheme.Modules.pushforwardCongr hi ≪≫
      (Scheme.Modules.pushforwardComp j g).symm).hom.app K)
    (he' : adj.homEquiv F _ e' = v ≫ (Scheme.Modules.pushforwardCongr hl ≪≫
      (Scheme.Modules.pushforwardComp k g).symm).hom.app H)
    (ht : v ≫ (Scheme.Modules.pushforward l).map t =
      u ≫ (Scheme.Modules.pushforwardCongr hil ≪≫
        (Scheme.Modules.pushforwardComp h l).symm).hom.app K) :
    e = e' ≫ (Scheme.Modules.pushforward k).map t ≫
      (Scheme.Modules.pushforwardComp h k).hom.app K ≫
      (Scheme.Modules.pushforwardCongr hj).hom.app K := by
  apply (adj.homEquiv F _).injective
  rw [Adjunction.homEquiv_naturality_right, he, he']
  let c := Scheme.Modules.pushforwardCongr hl ≪≫
    (Scheme.Modules.pushforwardComp k g).symm
  rw [Functor.map_comp, Category.assoc]
  have hn := c.hom.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [← Category.assoc, ht, Category.assoc]
  congr 1
  rw [Functor.map_comp]
  exact pushforward_pasting h k g j i l hj hi hl hil K

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finiteFMap_transition {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (F : X.Modules) (n : ℕ) :
    formalFunctionsFiniteFMap f y F n =
      formalFunctionsFiniteFMap f y F (n + 1) ≫
        (Scheme.Modules.pushforward (formalFunctionsFiniteι f y (n + 1))).map
          (formalFibreTransitionFMap f y F n) ≫
        (Scheme.Modules.pushforwardComp (formalFibreTransition f y n)
          (formalFunctionsFiniteι f y (n + 1))).hom.app
            ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) ≫
        (Scheme.Modules.pushforwardCongr (finiteι_transition f y n)).hom.app
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) := by
  let g := pullback.snd (Y.fromSpecStalk y) f
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  refine adjoint_triangle (formalFibreTransition f y n)
    (formalFunctionsFiniteι f y (n + 1)) g (formalFunctionsFiniteι f y n)
    (formalFibreι f y n) (formalFibreι f y (n + 1)) (finiteι_transition f y n)
    (formalFunctionsFiniteι_snd f y n).symm
    (formalFunctionsFiniteι_snd f y (n + 1)).symm (formalFibreTransition_ι f y n) adj
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (formalFibreι f y n))).unit.app F)
    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (formalFibreι f y (n + 1)))).unit.app F) _ _ _ ?_ ?_ ?_
  · exact (adj.homEquiv F _).apply_symm_apply _
  · exact (adj.homEquiv F _).apply_symm_apply _
  · exact ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
      (formalFibreι f y (n + 1)))).homEquiv F _).apply_symm_apply _

private theorem cohomology_triangle {A B C : Scheme.{u}}
    (h : A ⟶ B) (k : B ⟶ C) (j : A ⟶ C) (hj : h ≫ k = j)
    {G G' : C.Modules} {H : B.Modules} {F : A.Modules}
    (a : G' ⟶ G) (e : G ⟶ (Scheme.Modules.pushforward j).obj F)
    (e' : G' ⟶ (Scheme.Modules.pushforward k).obj H)
    (t : H ⟶ (Scheme.Modules.pushforward h).obj F)
    (hs : a ≫ e = e' ≫ (Scheme.Modules.pushforward k).map t ≫
      (Scheme.Modules.pushforwardComp h k).hom.app F ≫
      (Scheme.Modules.pushforwardCongr hj).hom.app F) (p : ℕ) :
    (forget₂ _ AddCommGrpCat.{u}).map
      ((RingedSpace.moduleCohomology C.toRingedSpace p).map a) ≫
      Scheme.Modules.moduleCohomologyFMap j e p =
    Scheme.Modules.moduleCohomologyFMap k e' p ≫
      Scheme.Modules.moduleCohomologyFMap h t p := by
  subst j
  have hc : (Scheme.Modules.pushforwardCongr (rfl : h ≫ k = h ≫ k)).hom.app F =
      𝟙 _ := by
    ext U
    simp
  rw [hc, Category.comp_id] at hs
  rw [Scheme.Modules.moduleCohomologyFMap_source_naturality, hs]
  exact Scheme.Modules.moduleCohomologyFMap_comp h k e' t p

/-- Any family of sheaf maps factoring the finite pullback units respects adjacent
quotient transitions after applying the cohomology h-maps. The maps are not assumed
invertible, and the statement makes no assertion of linearity over the local ring.

Source: Stacks Project, Tag 02OD, finite-level identifications; Tags 01F7 and 01FB.
(blueprint: lem-weil-pbc-formal-functions-finite-quotient-transition)
Proof: Write j_n for the finite fibre immersion into the local base change and t_n for
the transition from fibre n to fibre n+1. Pullback uniqueness gives t_n followed by
j_(n+1) = j_n. The adjunction equations defining formalFunctionsFiniteFMap and
formalFibreTransitionFMap identify the composite unit through these two morphisms
with the unit for j_n, with the canonical composition identification of direct images.
Precompose the desired sheaf square with the quotient projection at level n+1.
The quotient-transition cokernel equation identifies its left side with the level-n
unit. The unit equations for e and for the transition identify its right side with
the same map. Cancel the epimorphic quotient projection to obtain the sheaf square.
Apply moduleCohomologyFMap_source_naturality to the quotient transition and
moduleCohomologyFMap_comp to t_n and j_(n+1). Transport across their equality with j_n
using the canonical pushforward congruence. The sheaf square then yields the displayed
identity of additive maps. This does not use surjectivity of a map on cohomology; only
the sheaf quotient projection is cancelled. It applies to n = 0, every p, and the zero
module exactly as to all other levels. -/
theorem formalFunctions_finite_quotient_transition {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : X.Modules) (y : Y) (p : ℕ) :
    let X' := pullback (Y.fromSpecStalk y) f
    let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
    let J := (Scheme.IdealSheafData.ofIdealTop
      ((maximalIdeal (Y.presheaf.stalk y)).map
        (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap
          (pullback.fst (Y.fromSpecStalk y) f)
    let C := RingedSpace.moduleCohomology X'.toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
          (pullback.fst (Y.fromSpecStalk y) f).appTop).hom
    let S := formalCompletionSystem J F' ⋙ C
    let T := formalFibreCohomologySystem f y F p ⋙ ModuleCat.restrictScalars
      (algebraMap (Y.presheaf.stalk y)
        (AdicCompletion (maximalIdeal (Y.presheaf.stalk y)) (Y.presheaf.stalk y)))
    ∀ (e : ∀ n : ℕ, formalModuleQuotient J (n + 1) F' ⟶
        (Scheme.Modules.pushforward (formalFunctionsFiniteι f y n)).obj
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F)),
      (∀ n : ℕ, formalModuleQuotientπ J (n + 1) F' ≫ e n =
        formalFunctionsFiniteFMap f y F n) →
      ∀ (n : ℕ) (x : S.obj (op (n + 1))),
        (show T.obj (op n) from
          (Scheme.Modules.moduleCohomologyFMap (formalFunctionsFiniteι f y n) (e n) p).hom
            ((S.map (homOfLE (Nat.le_succ n)).op) x)) =
          (T.map (homOfLE (Nat.le_succ n)).op)
            (show T.obj (op (n + 1)) from
              (Scheme.Modules.moduleCohomologyFMap (formalFunctionsFiniteι f y (n + 1))
                (e (n + 1)) p).hom x) := by
  dsimp only
  intro e he n x
  let F' := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
  let J := (Scheme.IdealSheafData.ofIdealTop
    ((maximalIdeal (Y.presheaf.stalk y)).map
      (Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv.hom)).comap
        (pullback.fst (Y.fromSpecStalk y) f)
  let a := formalModuleQuotientMap J (𝟙 F') (Nat.succ_le_succ (Nat.le_succ n))
  have hq : formalModuleQuotientπ J (n + 2) F' ≫ a =
      formalModuleQuotientπ J (n + 1) F' := by
    simp [a, formalModuleQuotientMap, formalModuleQuotientπ]
  have hs : a ≫ e n = e (n + 1) ≫
      (Scheme.Modules.pushforward (formalFunctionsFiniteι f y (n + 1))).map
        (formalFibreTransitionFMap f y F n) ≫
      (Scheme.Modules.pushforwardComp (formalFibreTransition f y n)
        (formalFunctionsFiniteι f y (n + 1))).hom.app
          ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) ≫
      (Scheme.Modules.pushforwardCongr (finiteι_transition f y n)).hom.app
        ((Scheme.Modules.tensorPullback (formalFibreι f y n)).obj F) := by
    have : Epi (formalModuleQuotientπ J (n + 2) F') :=
      inferInstanceAs (Epi (cokernel.π _))
    apply (cancel_epi (formalModuleQuotientπ J (n + 2) F')).1
    rw [← Category.assoc, hq, he n]
    rw [← Category.assoc, he (n + 1)]
    exact finiteFMap_transition f y F n
  have hc := cohomology_triangle (formalFibreTransition f y n)
    (formalFunctionsFiniteι f y (n + 1)) (formalFunctionsFiniteι f y n)
    (finiteι_transition f y n) a (e n) (e (n + 1))
    (formalFibreTransitionFMap f y F n) hs p
  have hx := congrArg (fun z ↦ z.hom x) hc
  simp only [Functor.comp_map, formalFibreCohomologySystem,
    Functor.ofOpSequence_map_homOfLE_succ]
  exact hx


end AlgebraicGeometry
