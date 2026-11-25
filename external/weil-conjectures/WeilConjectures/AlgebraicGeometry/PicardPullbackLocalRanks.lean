/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
import WeilConjectures.AlgebraicGeometry.PullbackDualFiniteLocallyFree
import WeilConjectures.AlgebraicGeometry.Modules.DualRank
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank

/-! # Common local ranks for a pulled-back module

Source: Stacks Project, Tags 0BDP and 01E8.
(blueprint: lem-sc-picard-pullback-local-ranks)
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorComparison {A B : Scheme.{u}} (a : A ⟶ B) :
    Modules.tensorPullback a ≅ Modules.pullback a :=
  (Classical.choose (Modules.exists_tensorPullbackAdjunction a)).leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction a)

private theorem pullback_finiteLocallyFree {A B : Scheme.{u}} (a : A ⟶ B)
    (M : B.Modules) [M.IsFiniteLocallyFree] :
    ((Modules.pullback a).obj M).IsFiniteLocallyFree := by
  classical
  choose U I hI ht e using Modules.exists_mem_over_iso_free M
  let V (x : A) := a ⁻¹ᵁ U (a x)
  have (x : A) : Finite (I (a x)) := inferInstance
  refine Modules.isFiniteLocallyFree_of_restrict_iso_free _ (fun x ↦ (V x).ι) ?_
    (fun x ↦ I (a x)) fun x ↦ ⟨?_⟩
  · refine eq_top_iff.mpr fun x _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨x, ?_⟩
    rw [Scheme.Opens.opensRange_ι]
    exact ht (a x)
  · exact (Modules.restrictFunctorIsoPullback (V x).ι).app _ ≪≫
      (Modules.pullbackComp (V x).ι a).app M ≪≫
      (Modules.pullbackCongr (morphismRestrict_ι a (U (a x))).symm).app M ≪≫
      (Modules.pullbackComp (a ∣_ U (a x)) (U (a x)).ι).symm.app M ≪≫
      (Modules.pullback (a ∣_ U (a x))).mapIso
        ((Modules.restrictFunctorIsoPullback (U (a x)).ι).symm.app M ≪≫
          Modules.overIsoFreeEquiv M _ _ (e (a x)).some) ≪≫
      Modules.pullbackFreeIso _ _

private theorem tensor_finiteLocallyFree {A B : Scheme.{u}} (a : A ⟶ B)
    (M : B.Modules) [M.IsFiniteLocallyFree] :
    ((Modules.tensorPullback a).obj M).IsFiniteLocallyFree := by
  have := pullback_finiteLocallyFree a M
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} ((tensorComparison a).app M).symm

private theorem tensor_rank {A B : Scheme.{u}} (a : A ⟶ B)
    (M : B.Modules) (r : ℕ) [M.IsFiniteLocallyFreeOfRank r] :
    ((Modules.tensorPullback a).obj M).IsFiniteLocallyFreeOfRank r :=
  SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} ((tensorComparison a).app M).symm

private noncomputable def tensorDual {A B : Scheme.{u}} (a : A ⟶ B)
    (M : B.Modules) [M.IsFiniteLocallyFree] :
    (Modules.tensorPullback a).obj (Modules.dual M) ≅
      Modules.dual ((Modules.tensorPullback a).obj M) :=
  (tensorComparison a).app (Modules.dual M) ≪≫
    (Modules.nonempty_pullback_dual_iso_of_isFiniteLocallyFree a M).some ≪≫
      (Modules.dualFunctor A).mapIso ((tensorComparison a).app M).op

private noncomputable def presentation_baseChange {X S T : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (E : X.Modules) (N : T.Modules)
    (e : (Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N)
    {T' : Scheme.{u}} (h : T' ⟶ T) :
    (Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E ≅
      (Modules.tensorPullback (pullback.snd f (h ≫ g))).obj
        ((Modules.tensorPullback h).obj N) := by
  let b : pullback f (h ≫ g) ⟶ pullback f g :=
    pullback.lift (pullback.fst f (h ≫ g)) (pullback.snd f (h ≫ g) ≫ h)
      (by simp only [Category.assoc, pullback.condition])
  have hb₁ : b ≫ pullback.fst f g = pullback.fst f (h ≫ g) := by
    exact pullback.lift_fst _ _ _
  have hb₂ : b ≫ pullback.snd f g = pullback.snd f (h ≫ g) ≫ h := by
    exact pullback.lift_snd _ _ _
  exact (eqToIso (congrArg (fun a ↦ (Modules.tensorPullback a).obj E) hb₁)).symm ≪≫
    (Modules.nonempty_tensorPullbackComp b (pullback.fst f g)).some.app E ≪≫
    (Modules.tensorPullback b).mapIso e ≪≫
    (Modules.nonempty_tensorPullbackComp b (pullback.snd f g)).some.symm.app N ≪≫
    eqToIso (congrArg (fun a ↦ (Modules.tensorPullback a).obj N) hb₂) ≪≫
    (Modules.nonempty_tensorPullbackComp (pullback.snd f (h ≫ g)) h).some.app N

/-- A pulled-back finite locally free module and its two direct images have one
common finite rank locally after every change of base.
Source: Stacks Project, Tag 0BDP, projection-formula paragraph, using Tag 01E8.
(blueprint: lem-sc-picard-pullback-local-ranks)

Proof: For h : T' → T, form the canonical map X_{T'} → X_T by the pullback
universal property. The composition isomorphisms of tensor pullback and the
commutative projection squares transport e to q'^*E ≅ p'^*h^*N. Finite locally
free modules remain finite locally free under pullback: pull back their finite
local frames. In such frames the dual is the coordinate dual free module, and
pullback of the dual identifies with the dual of the pullback. Thus also
q'^*(E^dual) ≅ p'^*((h^*N)^dual). The finite-locally-free unit theorem for p',
using hO at h ≫ g, identifies the two direct images with h^*N and its dual.
Choose an open U containing t on which h^*N has a finite frame of size r.
Its coordinate dual frame has the same size. Transport these frames across the
two direct-image identifications and restrict to U. Pulling the original frame
up to X_U gives q_U^*E a frame of size r too. These three frames give exactly
the three displayed fixed-rank predicates. Empty T' has no point to check;
the empty frame handles r = 0, including an empty X_U. -/
theorem picard_pullback_local_ranks {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N)) :
    ∀ {T' : Scheme.{u}} (h : T' ⟶ T) (t : T'),
      ∃ U : T'.Opens, t ∈ U ∧ ∃ r : ℕ,
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback U.ι).obj
            ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
              ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj E))) r ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback U.ι).obj
            ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
              ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj
                (Modules.dual E)))) r ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Modules.tensorPullback (pullback.fst f (U.ι ≫ h ≫ g))).obj E) r := by
  classical
  intro T' h t
  obtain ⟨e⟩ := e
  let M := (Modules.tensorPullback h).obj N
  have : M.IsFiniteLocallyFree := tensor_finiteLocallyFree h N
  have : (Modules.dual M).IsFiniteLocallyFree := Modules.IsFiniteLocallyFree.dual M
  let p := pullback.snd f (h ≫ g)
  let q := pullback.fst f (h ≫ g)
  let e' : (Modules.tensorPullback q).obj E ≅ (Modules.tensorPullback p).obj M :=
    presentation_baseChange f g E N e h
  have : ((Modules.tensorPullback p).obj M).IsFiniteLocallyFree :=
    tensor_finiteLocallyFree p M
  let ed : (Modules.tensorPullback q).obj (Modules.dual E) ≅
      (Modules.tensorPullback p).obj (Modules.dual M) :=
    tensorDual q E ≪≫ (Modules.dualFunctor _).mapIso e'.symm.op ≪≫ (tensorDual p M).symm
  let adj := Classical.choose (Modules.exists_tensorPullbackAdjunction p)
  have : IsIso (adj.unit.app M) :=
    isIso_tensorPullback_unit_of_finiteLocallyFree p (hO (h ≫ g)) M
  have : IsIso (adj.unit.app (Modules.dual M)) :=
    isIso_tensorPullback_unit_of_finiteLocallyFree p (hO (h ≫ g)) (Modules.dual M)
  let d : M ≅ (Modules.pushforward p).obj ((Modules.tensorPullback q).obj E) :=
    asIso (adj.unit.app M) ≪≫ (Modules.pushforward p).mapIso e'.symm
  let dd : Modules.dual M ≅
      (Modules.pushforward p).obj ((Modules.tensorPullback q).obj (Modules.dual E)) :=
    asIso (adj.unit.app (Modules.dual M)) ≪≫ (Modules.pushforward p).mapIso ed.symm
  obtain ⟨U, I, hI, ht, ⟨frame⟩⟩ := Modules.exists_mem_over_iso_free M t
  let r := Fintype.card I
  let frame' : (Modules.tensorPullback U.ι).obj M ≅
      SheafOfModules.free (ULift.{u} (Fin r)) :=
    (tensorComparison U.ι).app M ≪≫ (Modules.restrictFunctorIsoPullback U.ι).symm.app M ≪≫
      Modules.overIsoFreeEquiv M U I frame ≪≫ SheafOfModules.freeFunctor.mapIso
        ((Fintype.equivFin I).trans Equiv.ulift.symm).toIso
  have hMr : ((Modules.tensorPullback U.ι).obj M).IsFiniteLocallyFreeOfRank r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} frame'.symm
  have hMd : ((Modules.tensorPullback U.ι).obj (Modules.dual M)).IsFiniteLocallyFreeOfRank r := by
    have := Modules.isFiniteLocallyFreeOfRank_dual ((Modules.tensorPullback U.ι).obj M) r
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u} (tensorDual U.ι M).symm
  refine ⟨U, ht, r, ?_, ?_, ?_⟩
  · exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Modules.tensorPullback U.ι).mapIso d)
  · exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
      ((Modules.tensorPullback U.ι).mapIso dd)
  · have hp := tensor_rank (pullback.snd f (U.ι ≫ (h ≫ g)))
      ((Modules.tensorPullback U.ι).obj M) r
    simpa only [Category.assoc] using
      (SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
        (presentation_baseChange f (h ≫ g) E M e' U.ι).symm)

end AlgebraicGeometry.Scheme
