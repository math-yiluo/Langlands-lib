/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

import WeilConjectures.AlgebraicGeometry.FlatBaseChangeMapSectionsLift
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionDegreeZero
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapPasting
import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeOpenSquareIso
import WeilConjectures.AlgebraicGeometry.FlatBaseChangeResolutionIso

/-! # Ordinary flat exchange with a prescribed adjunction

Source: Stacks Project, Tags 02KH and 02N7.
(blueprint: lem-weil-pbc-ordinary-flat-exchange-prescribed-adjunction).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChange_isIso_of_iso_top {A B A' A'' T : Scheme.{u}}
    (p : A ⟶ B) (p' : A' ⟶ T) (p'' : A'' ⟶ T) (h : T ⟶ B) (v : A' ⟶ A)
    (e : A'' ≅ A') (w : v ≫ p = p' ≫ h) (we : e.hom ≫ p' = p'') (F : A.Modules)
    (hbc : IsIso (Scheme.Modules.moduleBaseChangeMap p p' h v w F)) :
    IsIso (Scheme.Modules.moduleBaseChangeMap p p'' h (e.hom ≫ v)
      (by rw [Category.assoc, w, ← Category.assoc, we]) F) := by
  have w' : e.hom ≫ p' = p'' ≫ 𝟙 T := by simpa only [Category.comp_id] using we
  have hrange : Set.range e.hom = p' ⁻¹' Set.range (𝟙 T) := by
    have hs : Function.Surjective e.hom := by
      intro x
      refine ⟨e.inv x, ?_⟩
      exact congrArg (fun k : A' ⟶ A' ↦ k x) e.inv_hom_id
    rw [Set.range_eq_univ.mpr hs]
    change Set.univ = p' ⁻¹' Set.range (id : T → T)
    rw [Set.range_id, Set.preimage_univ]
  have hi : IsIso (Scheme.Modules.moduleBaseChangeMap p' p'' (𝟙 T) e.hom w'
      ((Scheme.Modules.tensorPullback v).obj F)) :=
    Scheme.Modules.moduleBaseChangeMap_open_square_isIso p' p'' (𝟙 T) e.hom w' hrange _
  have hout : IsIso (Scheme.Modules.moduleBaseChangeMap p p'' (𝟙 T ≫ h) (e.hom ≫ v)
      ((Category.assoc e.hom v p).trans
        ((congrArg (fun k ↦ e.hom ≫ k) w).trans
          ((Category.assoc e.hom p' h).symm.trans
            ((congrArg (fun k ↦ k ≫ h) w').trans (Category.assoc p'' (𝟙 T) h))))) F) := by
    rw [Scheme.Modules.moduleBaseChangeMap_pasting p p' p'' h v (𝟙 T) e.hom w w' F]
    infer_instance
  have heq : 𝟙 T ≫ h = h := Category.id_comp h
  cases heq
  exact hout

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The prescribed composite adjunction comparison requires additional elaboration.
/-- Ordinary flat exchange, normalized for the supplied adjunction on f.
Source: Stacks Project, Tags 02KH (part (1), degree zero) and 02N7 (mate construction).
(blueprint: lem-weil-pbc-ordinary-flat-exchange-prescribed-adjunction).

Proof: Choose tensor-pullback adjunctions on g, q and p. The sectionwise
pushforward-composition isomorphisms and the cartesian-square equation give an
isomorphism q_* f_* = p_* g_*. Its conjugate under the composite adjunctions
(g^* followed by p^*) and (f^* followed by q^*) gives c, using the supplied
adjunction on f. Take the horizontal mate under the adjunctions on q and g to
obtain B. Naturality follows from the unit, counit and composition comparisons.
For the unit identity, use unit_conjugateEquiv_symm on the composite adjunctions.
Expand their units: the f,q unit followed by the pushforward square equals the
g,p unit followed by the pushforward of c. Take the g-adjoint of the claimed
left side. Naturality of the g-unit moves the f-unit to the front; the defining
adjoint equation for B turns the remaining map into f_* of the q-unit followed
by the pushforward square. Substitute the composite-unit equation. This is the
g-adjoint of the claimed right side, so injectivity of homEquiv proves equality.
In degree zero the resolution-defined comparison of 02N7 is precisely this mate:
transport through the canonical zeroth-derived-functor identifications, evaluate
on an augmented resolution, and use its augmentation equation. Degree-zero flat
base change (02KH) makes B invertible for every quasi-coherent M, since proper f
is quasi-compact and quasi-separated. The definition of B uses only the chosen
adjunctions and the pushforward comparison, so it is natural on all modules,
including non-quasi-coherent modules. Empty schemes and zero modules require no
separate case: the same unit and counit equations apply. -/
theorem ordinary_flat_exchange_prescribed_adjunction
    {X Y S : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : S ⟶ Y) [Flat g]
    (adj : Scheme.Modules.tensorPullback f ⊣ Scheme.Modules.pushforward f) :
    let p := pullback.snd f g
    let q := pullback.fst f g
    let adjR := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)
    let c := (conjugateIsoEquiv
      (adj.comp (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp adjR)).symm
        (Scheme.Modules.pushforwardComp q f ≪≫
          Scheme.Modules.pushforwardCongr pullback.condition ≪≫
          (Scheme.Modules.pushforwardComp p g).symm)
    let B : Scheme.Modules.pushforward f ⋙ Scheme.Modules.tensorPullback g ⟶
        Scheme.Modules.tensorPullback q ⋙ Scheme.Modules.pushforward p :=
      { app := fun M ↦ Scheme.Modules.moduleBaseChangeMap f p g q pullback.condition M
        naturality := fun _ _ a ↦
          Scheme.Modules.moduleBaseChangeMap_naturality f p g q pullback.condition a }
    (∀ (M : X.Modules), M.IsQuasicoherent → IsIso (B.app M)) ∧
      (∀ (N : Y.Modules),
        (Scheme.Modules.tensorPullback g).map (adj.unit.app N) ≫
          B.app ((Scheme.Modules.tensorPullback f).obj N) =
        adjR.unit.app ((Scheme.Modules.tensorPullback g).obj N) ≫
          (Scheme.Modules.pushforward p).map (c.hom.app N)) := by
  classical
  dsimp only
  constructor
  · intro M hM
    have := hM
    have := Scheme.Modules.enoughInjectives (X := X)
    have := Scheme.Modules.enoughInjectives (X := pullback g f)
    let I := injectiveResolution M
    let J := injectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj M)
    obtain ⟨t, ht⟩ := Scheme.Modules.flatBaseChangeResolutionLift f g I J
    have hi := Scheme.Modules.flatBaseChangeResolutionBeta_isIso f g M I J t ht 0
    have he := Scheme.Modules.flatBaseChangeResolutionBeta_degree_zero f g M I J t ht
    have hcomp : IsIso (Scheme.Modules.moduleBaseChangeMap f (pullback.fst g f) g
        (pullback.snd g f) pullback.condition.symm M ≫
          (Scheme.Modules.pushforward (pullback.fst g f)).toRightDerivedZero.app
            ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj M)) := by
      rw [← he]
      infer_instance
    have hbc : IsIso (Scheme.Modules.moduleBaseChangeMap f (pullback.fst g f) g
        (pullback.snd g f) pullback.condition.symm M) :=
      IsIso.of_isIso_comp_right _
        ((Scheme.Modules.pushforward (pullback.fst g f)).toRightDerivedZero.app
          ((Scheme.Modules.tensorPullback (pullback.snd g f)).obj M))
    have hout := baseChange_isIso_of_iso_top f (pullback.fst g f) (pullback.snd f g)
      g (pullback.snd g f) (pullbackSymmetry f g) pullback.condition.symm
      (pullbackSymmetry_hom_comp_fst f g) M hbc
    have hall : ∀ w : ((pullbackSymmetry f g).hom ≫ pullback.snd g f) ≫ f =
        pullback.snd f g ≫ g,
      IsIso (Scheme.Modules.moduleBaseChangeMap f (pullback.snd f g) g
        ((pullbackSymmetry f g).hom ≫ pullback.snd g f) w M) := fun _ ↦ hout
    have htransport := congrArg (fun v ↦ ∀ w : v ≫ f = pullback.snd f g ≫ g,
      IsIso (Scheme.Modules.moduleBaseChangeMap f (pullback.snd f g) g v w M))
        (pullbackSymmetry_hom_comp_snd f g)
    exact (htransport.mp hall) pullback.condition
  · intro N
    apply ((Classical.choose
      (Scheme.Modules.exists_tensorPullbackAdjunction g)).homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_left]
    unfold Scheme.Modules.moduleBaseChangeMap
    dsimp only [Functor.comp_obj, Functor.id_obj]
    erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    have key := unit_conjugateEquiv_symm
      (adj.comp (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
        (pullback.fst f g))))
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
        (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction
          (pullback.snd f g))))
      (Scheme.Modules.pushforwardComp (pullback.fst f g) f ≪≫
        Scheme.Modules.pushforwardCongr pullback.condition ≪≫
        (Scheme.Modules.pushforwardComp (pullback.snd f g) g).symm).hom N
    simpa only [Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
      Functor.map_comp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
      conjugateIsoEquiv, Equiv.coe_fn_symm_mk] using key

end AlgebraicGeometry
