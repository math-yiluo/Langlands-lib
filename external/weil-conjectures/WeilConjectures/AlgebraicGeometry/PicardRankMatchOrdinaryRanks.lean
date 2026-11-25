/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatch
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent
import WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeStalkFinrank
import WeilConjectures.AlgebraicGeometry.PicardBaseChangeStalkFinrankEq

/-! # Ordinary ranks under iterated Picard base change

Source: Stacks Project, Tag 0BDP, first three proof paragraphs.
(blueprint: lem-sc-picard-rank-match-ordinary-ranks).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
private noncomputable def tensorComparison {A B : Scheme.{u}} (h : A ⟶ B) :
    Modules.tensorPullback h ≅ Modules.pullback h :=
  (Modules.nonempty_tensorPullbackAdjunction h).some.leftAdjointUniq
    (Modules.pullbackPushforwardAdjunction h)

private theorem finiteLocallyFree_of_localTensorRanks {T : Scheme.{u}} (N : T.Modules)
    (hlocal : ∀ t : T, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ,
      ((Modules.tensorPullback U.ι).obj N).IsFiniteLocallyFreeOfRank r) :
    N.IsFiniteLocallyFree := by
  classical
  choose U ht r hU using hlocal
  apply Modules.isFiniteLocallyFree_of_isOpenImmersion N (fun t ↦ (U t).ι)
  · apply eq_top_iff.mpr
    intro t _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨t, by
      rw [Scheme.Opens.opensRange_ι]
      exact ht t⟩
  · intro t
    have := hU t
    have := SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((Modules.tensorPullback (U t).ι).obj N) (r t)
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u}
      ((tensorComparison (U t).ι).app N)

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

-- Compare ranks across open restriction using the additive stalk isomorphism
-- and the invertible structure-ring stalk map.
private theorem restriction_finrank {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (x : U.toScheme) :
    Module.finrank (U.toScheme.presheaf.stalk x) ((M.restrict U.ι).presheaf.stalk x) =
      Module.finrank (X.presheaf.stalk (U.ι x)) (M.presheaf.stalk (U.ι x)) := by
  let N := M.restrict U.ι
  let e := (Modules.restrictStalkNatIso U.ι x).app M
  let j : N.presheaf.stalk x ≃+ M.presheaf.stalk (U.ι x) :=
    AddEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom)
  have hi (V : U.toScheme.Opens) (hx : x ∈ V) (a : Γ(U.toScheme, V)) :
      (inv (U.ι.stalkMap x)) (U.toScheme.presheaf.germ V x hx a) =
        X.presheaf.germ (U.ι ''ᵁ V) (U.ι x) (by simpa) ((U.ι.appIso V).inv a) := by
    apply (ConcreteCategory.bijective_of_isIso (U.ι.stalkMap x)).1
    simp only [IsIso.inv_hom_id_apply]
    rw [Scheme.Hom.germ_stalkMap_apply]
    change U.toScheme.presheaf.germ V x hx a =
      ((U.ι.appIso V).inv ≫ U.ι.app _ ≫ U.toScheme.presheaf.germ _ x _) a
    rw [Scheme.Hom.appIso_inv_app_assoc]
    exact (U.toScheme.presheaf.germ_res_apply (eqToHom (U.ι.preimage_image_eq V)) x
      (by simpa) a).symm
  have hc (a : U.toScheme.presheaf.stalk x) (m : N.presheaf.stalk x) :
      j (a • m) = (inv (U.ι.stalkMap x)) a • j m := by
    obtain ⟨V, hxV, a, rfl⟩ := U.toScheme.presheaf.exists_germ_eq a
    obtain ⟨W, hxW, m, rfl⟩ := N.presheaf.exists_germ_eq m
    have hx : x ∈ V ⊓ W := ⟨hxV, hxW⟩
    rw [← U.toScheme.presheaf.germ_res_apply
      (homOfLE inf_le_left : V ⊓ W ⟶ V) x hx a,
      ← N.presheaf.germ_res_apply (homOfLE inf_le_right : V ⊓ W ⟶ W) x hx m]
    erw [← PresheafOfModules.germ_smul (R := U.toScheme.presheaf) N.val]
    rw [hi]
    have hg (s : Γ(N, V ⊓ W)) :
        j (N.presheaf.germ (V ⊓ W) x hx s) =
          M.presheaf.germ (U.ι ''ᵁ (V ⊓ W)) (U.ι x) (by simpa) s :=
      ConcreteCategory.congr_hom
        (Modules.germ_restrictStalkNatIso_hom_app U.ι x M hx) s
    erw [hg, hg]
    exact PresheafOfModules.germ_smul (R := X.presheaf) M.val _ _ _ _ _
  exact congrArg Cardinal.toNat (rank_eq_of_equiv_equiv
    (fun a ↦ (inv (U.ι.stalkMap x)) a) j
    (ConcreteCategory.bijective_of_isIso (inv (U.ι.stalkMap x))) hc)

private theorem fixedRank_of_finrank {X : Scheme.{u}} (M : X.Modules)
    [M.IsFiniteLocallyFree] (r : ℕ)
    (h : ∀ x : X, Module.finrank (X.presheaf.stalk x) (M.presheaf.stalk x) = r) :
    M.IsFiniteLocallyFreeOfRank r := by
  classical
  have hf (x : X) : ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin r))) := by
    obtain ⟨U, I, hI, hx, ⟨e⟩⟩ := Modules.exists_mem_over_iso_free M x
    let := hI
    let e' : M.restrict U.ι ≅ SheafOfModules.free (ULift.{u} (Fin (Fintype.card I))) :=
      Modules.overIsoFreeEquiv M U I e ≪≫ SheafOfModules.freeFunctor.mapIso
        ((Fintype.equivFin I).trans Equiv.ulift.symm).toIso
    have : (M.restrict U.ι).IsFiniteLocallyFreeOfRank (Fintype.card I) :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e'.symm
    have hn : Fintype.card I = r :=
      (Modules.finiteLocallyFreeOfRank_stalk_finrank
        (M.restrict U.ι) (Fintype.card I) ⟨x, hx⟩).symm.trans
          ((restriction_finrank M U ⟨x, hx⟩).trans (h x))
    refine ⟨U, hx, ⟨Modules.overIsoFreeEquiv M U I e ≪≫ ?_⟩⟩
    exact SheafOfModules.freeFunctor.mapIso
      ((Fintype.equivFin I).trans ((finCongr hn).trans Equiv.ulift.symm)).toIso
  choose U hx e using hf
  apply Modules.isFiniteLocallyFreeOfRank_of_restrict_iso_free M (fun x ↦ (U x).ι)
  · apply eq_top_iff.mpr
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, by
      rw [Scheme.Opens.opensRange_ι]
      exact hx x⟩
  · exact e

/-- The ordinary direct image is finite locally free, and its further direct images
have one fixed rank on each sufficiently small base neighbourhood.
Source: Stacks Project, Tag 0BDP, rank decomposition and the ordinary rank dictionary.
(blueprint: lem-sc-picard-rank-match-ordinary-ranks).

Proof:
1. Apply the universal rank test to the identity of T. The canonical isomorphism
   between X times_S T and X times_S (id_T followed by g), and identity tensor
   pullback, identify its first two tests with restrictions of the direct images of
   E and its dual. These local fixed-rank frames give finite local freeness of M.
2. For each s choose this neighbourhood V and rank r. The third test gives rank r
   to E over X_V. Separate V into its intersection with the image of p and its
   complement. The image of p is clopen: p is proper, and flat of finite presentation.
   Keep the part containing s. On the empty-fibre part every further direct image
   is zero, and use rank zero for all further tests.
3. On the nonempty-fibre part, apply the universal rank test after any k:Y to V.
   Around each y it supplies a rank n for the further ordinary direct image and E
   on its inverse image. The fibre above y is nonempty: a nonempty scheme over
   kappa(k(y)) remains nonempty after extension to kappa(y). Choose a fibre point.
   Its local ring is nonzero. Pulling the two frames of E to this point gives free
   modules of ranks r and n, so invariant basis number gives r=n. The dual has the
   same rank, since dualizing a finite free frame preserves its size.
4. Pullback associativity identifies the iterated fibre product with X times_S Y,
   and identifies the iterated tensor pullback of F with its direct pullback.
   Transport the rank tests across these isomorphisms. Fixed-rank finite local
   freeness is local on Y, so the pointwise neighbourhoods give rank r globally on Y.
   This argument includes r=0; on empty Y every fixed-rank condition is vacuous. -/
theorem picardRankMatch_ordinary_ranks {X S T : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [IsProper f] [LocallyOfFinitePresentation f]
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S)
    (hR : PicardUniversalRankMatch f E g)
    (F : X.Modules) (hF : F = E ∨ F = Modules.dual E) :
    let G := (Modules.tensorPullback (pullback.fst f g)).obj F
    let M := (Modules.pushforward (pullback.snd f g)).obj G
    M.IsFiniteLocallyFree ∧
      ∀ s : T, ∃ U : T.Opens, s ∈ U ∧ ∃ r : ℕ,
        ∀ (Y : Scheme.{u}) (k : Y ⟶ U.toScheme),
          SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
            ((Modules.pushforward (pullback.snd (pullback.snd f g) (k ≫ U.ι))).obj
              ((Modules.tensorPullback (pullback.fst (pullback.snd f g) (k ≫ U.ι))).obj G))
            r := by
  classical
  dsimp only
  let G := (Modules.tensorPullback (pullback.fst f g)).obj F
  let M := (Modules.pushforward (pullback.snd f g)).obj G
  have hDirect {T' : Scheme.{u}} (h : T' ⟶ T) :
      ((Modules.pushforward (pullback.snd f (h ≫ g))).obj
        ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F)).IsFiniteLocallyFree := by
    apply finiteLocallyFree_of_localTensorRanks
    intro t
    obtain ⟨V, ht, n, he, hd, _⟩ := hR h t
    refine ⟨V, ht, n, ?_⟩
    rcases hF with rfl | rfl
    · exact he
    · exact hd
  have hM : M.IsFiniteLocallyFree := by
    exact (congrArg (fun k : T ⟶ S ↦
      ((Modules.pushforward (pullback.snd f k)).obj
        ((Modules.tensorPullback (pullback.fst f k)).obj F)).IsFiniteLocallyFree)
      (Category.id_comp g)).mp
        (hDirect (𝟙 T))
  refine ⟨hM, ?_⟩
  intro s
  obtain ⟨U, hs, r, hE, hD, _⟩ := hR (𝟙 T) s
  have hr : ((Modules.tensorPullback U.ι).obj M).IsFiniteLocallyFreeOfRank r := by
    have he : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f ((𝟙 T) ≫ g))).obj
            ((Modules.tensorPullback (pullback.fst f ((𝟙 T) ≫ g))).obj F))) r := by
      rcases hF with rfl | rfl
      · exact hE
      · exact hD
    exact (congrArg (fun a : T ⟶ S ↦
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι).obj
          ((Modules.pushforward (pullback.snd f a)).obj
            ((Modules.tensorPullback (pullback.fst f a)).obj F))) r)
      (Category.id_comp g)).mp he
  refine ⟨U, hs, r, ?_⟩
  intro Y k
  let h := k ≫ U.ι
  let Q := (Modules.pushforward (pullback.snd (pullback.snd f g) h)).obj
    ((Modules.tensorPullback (pullback.fst (pullback.snd f g) h)).obj G)
  have hQ : Q.IsFiniteLocallyFree := by
    have := hDirect h
    exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} (iteratedDirectImageIso f g h F).symm
  have hP : ((Modules.tensorPullback h).obj M).IsFiniteLocallyFreeOfRank r := by
    have := hr
    have hU : ((Modules.pullback U.ι).obj M).IsFiniteLocallyFreeOfRank r :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso ((tensorComparison U.ι).app M)
    have := hU
    have hK : ((Modules.tensorPullback k).obj
        ((Modules.tensorPullback U.ι).obj M)).IsFiniteLocallyFreeOfRank r := by
      exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        (((Modules.tensorPullback k).mapIso ((tensorComparison U.ι).app M)) ≪≫
          (tensorComparison k).app _).symm
    let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback U.ι ⋙ Modules.tensorPullback k).obj M) r := hK
    exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((Modules.nonempty_tensorPullbackComp k U.ι).some.app M).symm
  have := hQ
  apply fixedRank_of_finrank Q r
  intro y
  have := hP
  exact (picardRankMatch_baseChange_stalk_finrank_eq f E g hR h F hF y).symm.trans
    (Modules.finiteLocallyFreeOfRank_stalk_finrank _ r y)

end AlgebraicGeometry.Scheme
