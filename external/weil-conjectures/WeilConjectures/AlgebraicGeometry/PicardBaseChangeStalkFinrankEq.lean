/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
public import WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeRank
import Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.Modules.RestrictionStalkExtensionIso
import all WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatchConjunction
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Modules.TensorPullbackStalk
import WeilConjectures.AlgebraicGeometry.TensorPullback

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section

private noncomputable def tensorComparison {A B : Scheme.{u}} (a : A ⟶ B) :
    tensorPullback a ≅ pullback a :=
  (nonempty_tensorPullbackAdjunction a).some.leftAdjointUniq
    (pullbackPushforwardAdjunction a)

/-- Pull back a local frame and compare the resulting restricted stalk with the original stalk.
Source: Stacks Project, Tags 01C6 and 0098. The open-immersion stalk-ring map is invertible;
the additive stalk comparison is semilinear over its inverse, hence preserves rank. -/
private theorem finrank_tensorPullback_stalk_of_local_rank {A B : Scheme.{u}}
    (a : A ⟶ B) (M : B.Modules) (U : B.Opens) (x : A) (hx : a x ∈ U) (r : ℕ)
    (hr : ((tensorPullback U.ι).obj M).IsFiniteLocallyFreeOfRank r) :
    Module.finrank (A.presheaf.stalk x)
      (((tensorPullback a).obj M).presheaf.stalk x) = r := by
  let N := (tensorPullback a).obj M
  let W := a ⁻¹ᵁ U
  let z : W.toScheme := ⟨x, hx⟩
  let c := a ∣_ U
  let e : N.restrict W.ι ≅ (pullback c).obj ((tensorPullback U.ι).obj M) :=
    (restrictFunctorIsoPullback W.ι).app N ≪≫
      (pullback W.ι).mapIso ((tensorComparison a).app M) ≪≫
      (pullbackComp W.ι a).app M ≪≫
      (pullbackCongr (morphismRestrict_ι a U).symm).app M ≪≫
      (pullbackComp c U.ι).symm.app M ≪≫
      (pullback c).mapIso ((tensorComparison U.ι).symm.app M)
  have := hr
  have hNr : (N.restrict W.ι).IsFiniteLocallyFreeOfRank r :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
  have := hNr
  have hlocal := finiteLocallyFreeOfRank_stalk_finrank (N.restrict W.ι) r z
  let d : (N.restrict W.ι).presheaf.stalk z ≃+ N.presheaf.stalk (W.ι z) :=
    AddEquiv.ofBijective ((restrictStalkNatIso W.ι z).hom.app N).hom
      (ConcreteCategory.bijective_of_isIso ((restrictStalkNatIso W.ι z).hom.app N))
  have heq := rank_eq_of_equiv_equiv (inv (W.ι.stalkMap z)) d
    (ConcreteCategory.bijective_of_isIso (inv (W.ι.stalkMap z)))
    (AlgebraicGeometry.restriction_stalk_smul W.ι z N)
  have hfin := congrArg Cardinal.toNat heq
  exact hfin.symm.trans hlocal

end

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/-- Associativity transports the iterated direct image to the composite base change. -/
private noncomputable def iteratedDirectImageIso {X S T T' : Scheme.{u}}
    (f : X ⟶ S) (g : T ⟶ S) (h : T' ⟶ T) (F : X.Modules) :
    (Modules.pushforward (pullback.snd (pullback.snd f g) h)).obj
        ((Modules.tensorPullback (pullback.fst (pullback.snd f g) h)).obj
          ((Modules.tensorPullback (pullback.fst f g)).obj F)) ≅
      (Modules.pushforward (pullback.snd f (h ≫ g))).obj
        ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F) := by
  let e := pullbackLeftPullbackSndIso f g h
  let q := pullback.fst f (h ≫ g)
  let p := pullback.snd f (h ≫ g)
  let v := pullback.fst (pullback.snd f g) h
  let q₀ := pullback.fst f g
  let p' := pullback.snd (pullback.snd f g) h
  have hq : e.hom ≫ q = v ≫ q₀ := pullbackLeftPullbackSndIso_hom_fst f g h
  have hp : e.hom ≫ p = p' := pullbackLeftPullbackSndIso_hom_snd f g h
  let a : (Modules.tensorPullback v).obj ((Modules.tensorPullback q₀).obj F) ≅
      (Modules.tensorPullback e.hom).obj ((Modules.tensorPullback q).obj F) :=
    ((Modules.nonempty_tensorPullbackComp v q₀).some.app F).symm ≪≫
      (eqToIso (congrArg (fun k ↦ (Modules.tensorPullback k).obj F) hq)).symm ≪≫
      (Modules.nonempty_tensorPullbackComp e.hom q).some.app F
  let eqv : (pullback (pullback.snd f g) h).Modules ≌
      (pullback f (h ≫ g)).Modules :=
    CategoryTheory.Equivalence.mk (Modules.pushforward e.hom) (Modules.pushforward e.inv)
      (Modules.pushforwardComp e.hom e.inv ≪≫
        Modules.pushforwardCongr e.hom_inv_id ≪≫ Modules.pushforwardId _).symm
      (Modules.pushforwardComp e.inv e.hom ≪≫
        Modules.pushforwardCongr e.inv_hom_id ≪≫ Modules.pushforwardId _)
  have : (Modules.pushforward e.hom).IsEquivalence := eqv.isEquivalence_functor
  let adj := (Modules.nonempty_tensorPullbackAdjunction e.hom).some
  have : IsIso adj.unit := inferInstance
  exact (Modules.pushforward p').mapIso a ≪≫
    (Modules.pushforwardCongr hp).symm.app _ ≪≫
    (Modules.pushforwardComp e.hom p).symm.app _ ≪≫
    (Modules.pushforward p).mapIso (asIso (adj.unit.app _)).symm

/-- A proper direct image has zero stalk outside the image. -/
private theorem pushforward_stalk_subsingleton_of_not_mem_range
    {A B : Scheme.{u}} (a : A ⟶ B) [IsProper a] (M : A.Modules) (y : B)
    (hy : y ∉ Set.range a) :
    Subsingleton (((Modules.pushforward a).obj M).presheaf.stalk y) := by
  let N := (Modules.pushforward a).obj M
  let U : B.Opens := ⟨(Set.range a)ᶜ, a.isClosedMap.isClosed_range.isOpen_compl⟩
  have hyU : y ∈ U := hy
  have hz (m : N.presheaf.stalk y) : m = 0 := by
    obtain ⟨V, hVU, hyV, m, rfl⟩ := N.presheaf.exists_le_germ_eq m hyU
    have he : a ⁻¹ᵁ V = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      exact (hVU hx) ⟨x, rfl⟩
    have hs : Subsingleton Γ(N, V) := by
      change Subsingleton Γ(M, a ⁻¹ᵁ V)
      rw [he]
      exact ⟨fun a b ↦ TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩
        (fun _ : PEmpty.{1} ↦ ⊥) ⊥ (fun i ↦ i.elim) (fun _ hx ↦ hx.elim) a b
        fun i ↦ i.elim⟩
    have := hs
    rw [Subsingleton.elim m 0, map_zero]
  exact ⟨fun m n ↦ (hz m).trans (hz n).symm⟩

private theorem stalk_finrank_of_local_rank {A : Scheme.{u}} (M : A.Modules)
    (U : A.Opens) (x : A) (hx : x ∈ U) (r : ℕ)
    (hr : ((Modules.tensorPullback U.ι).obj M).IsFiniteLocallyFreeOfRank r) :
    Module.finrank (A.presheaf.stalk x) (M.presheaf.stalk x) = r := by
  have h := Modules.finrank_tensorPullback_stalk_of_local_rank (𝟙 A) M U x hx r hr
  let e := (RingedSpace.moduleStalkFunctor A.toRingedSpace x).mapIso
    ((Modules.nonempty_tensorPullbackId A).some.app M)
  exact e.toLinearEquiv.finrank_eq.symm.trans h

/-- The source and target stalks have equal finrank, without asserting freeness.
Source: Stacks Project, Tag 0BDP, local rank reduction, expanded using
Tags 01C6 and 0098. This is the rank-comparison part of the original argument.

Proof: apply hR to the identity at h(t), obtaining a neighbourhood V and rank r,
and to h at t, obtaining W and rank s. Local frames, the pullback stalk formula,
and associativity of fibre products identify the finrank of P_t with r and that
of Q_t with s. To compare r and s, first suppose the fibre over h(t) is nonempty.
For a point x in that fibre, the tensor product of kappa(x) and kappa(t) over
kappa(h(t)) is nonzero (fields are faithfully flat). Choose a prime of this
tensor product to obtain a point y of the iterated fibre product over x and t.
At y the pulled-back E has rank r from V and rank s from W. The stalk formula
transports the frames to this same local ring. Invariant basis number over the
nonzero scheme local ring gives r = s. Thus the two computed finranks coincide.
If the fibre is empty, the proper projection X times_S T to T has closed image
omitting h(t). On its open complement the direct image of either F is zero.
Its pullback along h is zero, and the base-changed projection also has empty
inverse image over the inverse-image open. Hence both stalks are zero and
both finranks are zero, regardless of the r and s selected by hR on empty
preimages. This handles rank zero as well; empty T' has no point to check.
(blueprint: lem-sc-picard-base-change-stalk-finrank-eq) -/
theorem picardRankMatch_baseChange_stalk_finrank_eq {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g) {T' : Scheme.{u}} (h : T' ⟶ T)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) (t : T') :
    let P := (Modules.tensorPullback h).obj
      ((Modules.pushforward (pullback.snd f g)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    let Q := (Modules.pushforward (pullback.snd (pullback.snd f g) h)).obj
      ((Modules.tensorPullback (pullback.fst (pullback.snd f g) h)).obj
        ((Modules.tensorPullback (pullback.fst f g)).obj F))
    Module.finrank (T'.presheaf.stalk t) (P.presheaf.stalk t) =
      Module.finrank (T'.presheaf.stalk t) (Q.presheaf.stalk t) := by
  classical
  let N := (Modules.pushforward (pullback.snd f g)).obj
    ((Modules.tensorPullback (pullback.fst f g)).obj F)
  let C := (Modules.pushforward (pullback.snd f (h ≫ g))).obj
    ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F)
  obtain ⟨U, htU, r, hNrE, hNrD, hEr⟩ := hR (𝟙 T) (h t)
  obtain ⟨V, htV, s, hCsE, hCsD, hEs⟩ := hR h t
  have hNr : ((Modules.tensorPullback U.ι).obj N).IsFiniteLocallyFreeOfRank r := by
    rcases hF with rfl | rfl
    · exact hNrE
    · exact hNrD
  have hCs : ((Modules.tensorPullback V.ι).obj C).IsFiniteLocallyFreeOfRank s := by
    rcases hF with rfl | rfl
    · exact hCsE
    · exact hCsD
  have hP := Modules.finrank_tensorPullback_stalk_of_local_rank h N U t htU r hNr
  have hC := stalk_finrank_of_local_rank C V t htV s hCs
  let e := (RingedSpace.moduleStalkFunctor T'.toRingedSpace t).mapIso
    (iteratedDirectImageIso f g h F)
  have hQ := e.toLinearEquiv.finrank_eq.trans hC
  change Module.finrank (T'.presheaf.stalk t)
      (((Modules.tensorPullback h).obj N).presheaf.stalk t) = _
  apply hP.trans
  apply Eq.trans (b := s) _ hQ.symm
  by_cases hne : h t ∈ Set.range (pullback.snd f g)
  · let W : T'.Opens := h ⁻¹ᵁ U ⊓ V
    have htW : t ∈ W := ⟨htU, htV⟩
    let k : W.toScheme ⟶ S := W.ι ≫ h ≫ g
    let a : W.toScheme ⟶ U.toScheme :=
      T'.homOfLE (show W ≤ h ⁻¹ᵁ U from inf_le_left) ≫ (h ∣_ U)
    let b : W.toScheme ⟶ V.toScheme := T'.homOfLE inf_le_right
    have ha : a ≫ U.ι ≫ g = k := by
      dsimp [a, k]
      rw [Category.assoc, ← Category.assoc (h ∣_ U) U.ι g, morphismRestrict_ι,
        ← Category.assoc, ← Category.assoc, Scheme.homOfLE_ι, Category.assoc]
    have hb : b ≫ V.ι ≫ h ≫ g = k := by
      simp [b, k, ← Category.assoc]
    let ar := pullback.map f k f (U.ι ≫ g) (𝟙 X) a (𝟙 S)
      (by simp) (by simpa using ha.symm)
    let bs := pullback.map f k f (V.ι ≫ h ≫ g) (𝟙 X) b (𝟙 S)
      (by simp) (by simpa using hb.symm)
    have har : ar ≫ pullback.fst f (U.ι ≫ g) = pullback.fst f k := by
      simp [ar]
    have hbs : bs ≫ pullback.fst f (V.ι ≫ h ≫ g) = pullback.fst f k := by
      simp [bs]
    have hr : ((Modules.tensorPullback (pullback.fst f k)).obj E).IsFiniteLocallyFreeOfRank
        r := by
      simpa only [har] using Modules.isFiniteLocallyFreeOfRank_tensorPullback_comp ar
        (pullback.fst f (U.ι ≫ g)) E r hEr
    have hs : ((Modules.tensorPullback (pullback.fst f k)).obj E).IsFiniteLocallyFreeOfRank
        s := by
      simpa only [hbs] using Modules.isFiniteLocallyFreeOfRank_tensorPullback_comp bs
        (pullback.fst f (V.ι ≫ h ≫ g)) E s hEs
    obtain ⟨x, hx⟩ := hne
    have hxt : f ((pullback.fst f g) x) = k ⟨t, htW⟩ := by
      change (pullback.fst f g ≫ f) x = (h ≫ g) t
      rw [pullback.condition, Hom.comp_apply, hx]
      rfl
    obtain ⟨z, _, _⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := k)
      ((pullback.fst f g) x) (⟨t, htW⟩ : W.toScheme) hxt
    have := hr
    have er := Modules.finiteLocallyFreeOfRank_stalk_finrank
      ((Modules.tensorPullback (pullback.fst f k)).obj E) r z
    have := hs
    have es := Modules.finiteLocallyFreeOfRank_stalk_finrank
      ((Modules.tensorPullback (pullback.fst f k)).obj E) s z
    exact er.symm.trans es
  · have hN0 : Module.finrank (T.presheaf.stalk (h t)) (N.presheaf.stalk (h t)) = 0 := by
      have := pushforward_stalk_subsingleton_of_not_mem_range (pullback.snd f g)
        ((Modules.tensorPullback (pullback.fst f g)).obj F) (h t) hne
      exact Module.finrank_zero_of_subsingleton
    have htne : t ∉ Set.range (pullback.snd f (h ≫ g)) := by
      intro ⟨x, hx⟩
      apply hne
      rw [Scheme.Pullback.range_snd]
      change g (h t) ∈ Set.range f
      refine ⟨(pullback.fst f (h ≫ g)) x, ?_⟩
      change (pullback.fst f (h ≫ g) ≫ f) x = _
      rw [pullback.condition, Hom.comp_apply, hx]
      rfl
    have hC0 : Module.finrank (T'.presheaf.stalk t) (C.presheaf.stalk t) = 0 := by
      have := pushforward_stalk_subsingleton_of_not_mem_range (pullback.snd f (h ≫ g))
        ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F) t htne
      exact Module.finrank_zero_of_subsingleton
    exact ((stalk_finrank_of_local_rank N U (h t) htU r hNr).symm.trans hN0).trans
      (hC.symm.trans hC0).symm

end AlgebraicGeometry.Scheme
