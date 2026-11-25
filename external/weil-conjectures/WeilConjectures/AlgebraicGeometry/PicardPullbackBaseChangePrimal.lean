/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Primal base change for a module pulled back from the base

Source: Stacks Project, Tag 0BDP, projection-formula paragraph; Tag 01E8.
(blueprint: lem-sc-picard-pullback-base-change-primal)
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable abbrev adj {A B : Scheme.{u}} (k : A ⟶ B) :=
  Classical.choose (Modules.exists_tensorPullbackAdjunction k)

private noncomputable def squareIso {A B A' B' : Scheme.{u}}
    (p : A ⟶ B) (p' : A' ⟶ B') (h : B' ⟶ B) (v : A' ⟶ A)
    (w : v ≫ p = p' ≫ h) :
    Modules.pushforward v ⋙ Modules.pushforward p ≅
      Modules.pushforward p' ⋙ Modules.pushforward h :=
  Modules.pushforwardComp v p ≪≫ Modules.pushforwardCongr w ≪≫
    (Modules.pushforwardComp p' h).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem baseChange_unit {A B A' B' : Scheme.{u}}
    (p : A ⟶ B) (p' : A' ⟶ B') (h : B' ⟶ B) (v : A' ⟶ A)
    (w : v ≫ p = p' ≫ h) (N : B.Modules) :
    (Modules.tensorPullback h).map ((adj p).unit.app N) ≫
        Modules.moduleBaseChangeMap p p' h v w ((Modules.tensorPullback p).obj N) =
      (adj p').unit.app ((Modules.tensorPullback h).obj N) ≫
        (Modules.pushforward p').map
          (((conjugateIsoEquiv ((adj p).comp (adj v))
            ((adj h).comp (adj p'))).symm (squareIso p p' h v w)).hom.app N) := by
  apply ((adj h).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left]
  unfold Modules.moduleBaseChangeMap
  dsimp only [adj]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  erw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  have key := unit_conjugateEquiv_symm ((adj p).comp (adj v))
    ((adj h).comp (adj p')) (squareIso p p' h v w).hom N
  simpa only [Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj, Functor.map_comp,
    squareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc,
    conjugateIsoEquiv, Equiv.coe_fn_symm_mk, adj] using key

private theorem unit_precomp_iso {A A' B : Scheme.{u}} (e : A' ≅ A)
    (p : A ⟶ B) (p' : A' ⟶ B) (w : e.hom ≫ p = p') (N : B.Modules)
    (hp : IsIso ((adj p).unit.app N)) : IsIso ((adj p').unit.app N) := by
  let eqv : A'.Modules ≌ A.Modules :=
    CategoryTheory.Equivalence.mk (Modules.pushforward e.hom) (Modules.pushforward e.inv)
      (Modules.pushforwardComp e.hom e.inv ≪≫
        Modules.pushforwardCongr e.hom_inv_id ≪≫ Modules.pushforwardId A').symm
      (Modules.pushforwardComp e.inv e.hom ≪≫
        Modules.pushforwardCongr e.inv_hom_id ≪≫ Modules.pushforwardId A)
  have : (Modules.pushforward e.hom).IsEquivalence := eqv.isEquivalence_functor
  have : IsIso ((adj e.hom).unit.app ((Modules.tensorPullback p).obj N)) :=
    inferInstance
  let q := Modules.pushforwardComp e.hom p ≪≫ Modules.pushforwardCongr w
  let c := (conjugateIsoEquiv ((adj p).comp (adj e.hom)) (adj p')).symm q
  have key := unit_conjugateEquiv_symm ((adj p).comp (adj e.hom))
    (adj p') q.hom N
  have hi : IsIso (((adj p).comp (adj e.hom)).unit.app N ≫ q.hom.app _) := by
    rw [Adjunction.comp_unit_app]
    infer_instance
  have hi' : IsIso ((adj p').unit.app N ≫ (Modules.pushforward p').map (c.hom.app N)) := by
    convert hi using 1
    exact key.symm
  exact IsIso.of_isIso_comp_right _ ((Modules.pushforward p').map (c.hom.app N))

private theorem tensorPullback_finiteLocallyFree {A B : Scheme.{u}} (h : A ⟶ B)
    (N : B.Modules) [N.IsFiniteLocallyFree] :
    ((Modules.tensorPullback h).obj N).IsFiniteLocallyFree := by
  let c := (adj h).leftAdjointUniq (Modules.pullbackPushforwardAdjunction h)
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} (c.app N).symm

/-- The primal base-change map for a pulled-back finite locally free module is invertible.
Source: Stacks Project, Tag 0BDP, projection-formula paragraph.
(blueprint: lem-sc-picard-pullback-base-change-primal)
Proof: The finite-locally-free unit theorem applies to N at g and to h^*N at h ≫ g;
pullback preserves finite local freeness by uniqueness of left adjoints and the proved
abstract-pullback instance. Pasting the pullback squares identifies the iterated
pullback with X ×_S T'. Pushforward along that scheme isomorphism is an equivalence.
The conjugate-adjunction unit identity transports the second unit to the iterated
pullback. The same identity, for the two composite adjunctions of the square, gives
h^*η_p followed by base change = η_p' followed by the pushforward of the pullback
comparison isomorphism. The two units are invertible, so base change on p^*N is
invertible by cancellation. Naturality then transports invertibility along e.
This argument also covers rank zero and empty schemes. -/
theorem picard_pullback_base_change_primal {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N))
    {T' : Scheme.{u}} (h : T' ⟶ T) :
      IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
        pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj E)) := by
  obtain ⟨e⟩ := e
  let p := pullback.snd f g
  let p' := pullback.snd p h
  let v := pullback.fst p h
  have hp : IsIso ((adj p).unit.app N) :=
    isIso_tensorPullback_unit_of_finiteLocallyFree p (hO g) N
  have hfree : ((Modules.tensorPullback h).obj N).IsFiniteLocallyFree :=
    tensorPullback_finiteLocallyFree h N
  have hpbar : IsIso ((adj (pullback.snd f (h ≫ g))).unit.app
      ((Modules.tensorPullback h).obj N)) :=
    isIso_tensorPullback_unit_of_finiteLocallyFree _ (hO (h ≫ g)) _
  let sq := (IsPullback.of_hasPullback p h).paste_horiz
    (IsPullback.of_hasPullback f g)
  have hp' : IsIso ((adj p').unit.app ((Modules.tensorPullback h).obj N)) :=
    unit_precomp_iso sq.isoPullback _ p' sq.isoPullback_hom_snd _ hpbar
  have hi : IsIso (Modules.moduleBaseChangeMap p p' h v pullback.condition
      ((Modules.tensorPullback p).obj N)) := by
    have hc : IsIso ((Modules.tensorPullback h).map ((adj p).unit.app N) ≫
        Modules.moduleBaseChangeMap p p' h v pullback.condition
          ((Modules.tensorPullback p).obj N)) := by
      rw [baseChange_unit]
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((Modules.tensorPullback h).map ((adj p).unit.app N)) _
  have he := Modules.moduleBaseChangeMap_naturality p p' h v pullback.condition e.hom
  have hc : IsIso (Modules.moduleBaseChangeMap p p' h v pullback.condition
      ((Modules.tensorPullback (pullback.fst f g)).obj E) ≫
        (Modules.pushforward p').map ((Modules.tensorPullback v).map e.hom)) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((Modules.pushforward p').map ((Modules.tensorPullback v).map e.hom))

end AlgebraicGeometry.Scheme
