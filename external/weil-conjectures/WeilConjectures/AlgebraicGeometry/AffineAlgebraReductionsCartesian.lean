/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.CommAlgebraSheaf

import WeilConjectures.AlgebraicGeometry.AffineAlgebraLocalMaps
import Mathlib.RingTheory.Ideal.Maps

/-! # Recovering a finite system from compatible affine algebra reductions

Source: Stacks Project, Lemma 09ZT, final sentence, and Morphisms, Lemma 01S8
(blueprint: lem-weil-pbc-affine-algebra-reductions-cartesian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option autoImplicit false

set_option hygiene false in
local notation "𝒪⁎" g:max => Under.mk (⟨(g).c⟩ : Scheme.sheaf _ ⟶
  (TopCat.Sheaf.pushforward CommRingCat.{u} (g).base).obj (Scheme.sheaf _))

-- The local correspondence determines the global morphism uniquely.
open TopologicalSpace in
private theorem unique_over_map_of_algebra {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S) [IsAffineHom g] (α : (𝒪⁎g : S.CommAlgebraSheaf) ⟶ 𝒪⁎f) :
    ∃ h : X ⟶ Y, ∃ w : h ≫ g = f,
      (∀ U : S.affineOpens,
        h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
          (by rw [← w, Scheme.Hom.comp_preimage]) = α.right.hom.app (op U.1)) ∧
      ∀ (h' : X ⟶ Y) (w' : h' ≫ g = f),
        (∀ U : S.affineOpens,
          h'.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
            (by rw [← w', Scheme.Hom.comp_preimage]) = α.right.hom.app (op U.1)) →
        h' = h := by
  obtain ⟨k, hw, hc, ha⟩ := affine_algebra_local_maps f g α
  let 𝒰 := X.openCoverOfIsOpenCover (fun U : S.affineOpens ↦ f ⁻¹ᵁ U.1)
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top S))
  let h : X ⟶ Y := 𝒰.glueMorphisms k hc
  have hi (U : S.affineOpens) : (f ⁻¹ᵁ U.1).ι ≫ h = k U :=
    𝒰.ι_glueMorphisms k hc U
  have w : h ≫ g = f := by
    apply 𝒰.hom_ext
    intro U
    change (f ⁻¹ᵁ U.1).ι ≫ h ≫ g = (f ⁻¹ᵁ U.1).ι ≫ f
    rw [← Category.assoc, hi, hw]
  have haGlobal : ∀ U : S.affineOpens,
      h.appLE (g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1)
        (by rw [← w, Scheme.Hom.comp_preimage]) = α.right.hom.app (op U.1) := by
    intro U
    have e : ⊤ ≤ k U ⁻¹ᵁ (g ⁻¹ᵁ U.1) := by
      rw [← Scheme.Hom.comp_preimage, hw, Scheme.Hom.comp_preimage]
      simp
    have ea := ha U e
    simp only [← hi U] at ea
    rw [Scheme.Hom.comp_appLE] at ea
    simp only [Scheme.Opens.ι_appLE] at ea
    apply (cancel_mono (f ⁻¹ᵁ U.1).topIso.inv).mp
    simp only [Scheme.Hom.appLE, Scheme.Opens.topIso_inv, Category.assoc,
      ← Functor.map_comp] at ea ⊢
    convert ea using 1
    congr 1
  refine ⟨h, w, haGlobal, ?_⟩
  intro h' w' ha'
  symm
  apply Scheme.hom_ext_of_forall
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (show f x ∈ (⊤ : S.Opens) from trivial) isOpen_univ
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU.preimage g
  have hh : h.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by rw [← w, Scheme.Hom.comp_preimage]) =
    h'.resLE (g ⁻¹ᵁ U) (f ⁻¹ᵁ U)
      (by rw [← w', Scheme.Hom.comp_preimage]) := by
    apply ext_of_isAffine
    simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    rw [haGlobal ⟨U, hU⟩, ha' ⟨U, hU⟩]
  simpa only [Scheme.Hom.resLE_comp_ι] using congrArg (· ≫ (g ⁻¹ᵁ U).ι) hh

private theorem quotient_pushout {R S A T : CommRingCat.{u}}
    (q : R ⟶ S) (a : R ⟶ A) (d : S ⟶ T) (b : A ⟶ T)
    (w : q ≫ d = a ≫ b) (hq : Function.Surjective q.hom)
    (hb : Function.Surjective b.hom)
    (hk : RingHom.ker b.hom = (RingHom.ker q.hom).map a.hom) :
    IsPushout q a d b := by
  classical
  have hker (s : PushoutCocone q a) : RingHom.ker b.hom ≤ RingHom.ker s.inr.hom := by
    rw [hk, Ideal.map_le_iff_le_comap]
    intro x hx
    change s.inr (a x) = 0
    have e := congrArg (fun t : R ⟶ s.pt ↦ t x) s.condition
    simpa only [CommRingCat.comp_apply, RingHom.mem_ker.mp hx, map_zero] using e.symm
  let desc (s : PushoutCocone q a) : T ⟶ s.pt :=
    CommRingCat.ofHom (b.hom.liftOfSurjective hb ⟨s.inr.hom, hker s⟩)
  have fac (s : PushoutCocone q a) : b ≫ desc s = s.inr := by
    apply CommRingCat.hom_ext
    exact b.hom.liftOfSurjective_comp hb ⟨s.inr.hom, hker s⟩
  have facq (s : PushoutCocone q a) : d ≫ desc s = s.inl := by
    ext x
    obtain ⟨y, rfl⟩ := hq x
    have e := congrArg (fun t : R ⟶ T ↦ t y) w
    change desc s (d (q y)) = s.inl (q y)
    rw [show d (q y) = b (a y) from e]
    change (b ≫ desc s) (a y) = s.inl (q y)
    rw [fac]
    exact (congrArg (fun t : R ⟶ s.pt ↦ t y) s.condition).symm
  apply IsPushout.of_isColimit (c := PushoutCocone.mk d b w)
  refine PushoutCocone.IsColimit.mk w desc facq fac ?_
  intro s m _ hm
  ext x
  obtain ⟨y, rfl⟩ := hb x
  exact congrArg (fun t : A ⟶ s.pt ↦ t y) (hm.trans (fac s).symm)

private theorem affine_pullback_of_pushout
    {P Y Z X : Scheme.{u}} [IsAffine P] [IsAffine Y] [IsAffine Z] [IsAffine X]
    (v : P ⟶ Y) (f : P ⟶ Z) (g : Y ⟶ X) (j : Z ⟶ X)
    (h : IsPushout g.appTop j.appTop v.appTop f.appTop) : IsPullback v f g j := by
  apply (isPullback_SpecMap_of_isPushout _ _ _ _ h).of_iso'
    P.isoSpec Y.isoSpec Z.isoSpec X.isoSpec <;>
    simp only [Scheme.isoSpec, asIso_hom, Scheme.toSpecΓ_naturality]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A fixed morphism of affine schemes over X is the base change along a closed
immersion if its section maps present the quotient by the extended base ideal.
Source: Stacks Project, Lemma 09ZT, final sentence; Morphisms, Lemmas 01S8 and 01SA.
(blueprint: lem-weil-pbc-affine-algebra-reductions-cartesian, step 2).

Proof: Cover X by affine opens U = Spec R. Since j is a closed immersion, its
inverse image is Spec(R/J), where J is the kernel of j.app U. Both g inverse U and
(f followed by j) inverse U are affine. Identify the first coordinate ring with
B(U) using alpha. The section formula for v identifies its ring map with b(U)
after this isomorphism. Surjectivity and the kernel equation identify the second
coordinate ring with B(U)/(J B(U)), by the ring first isomorphism theorem.
The square of coordinate rings is a pushout: B(U)/(J B(U)) is
B(U) tensor_R (R/J). Taking Spec gives a pullback square on this chart with the
specified maps, since v is over X. Pullback squares can be checked after restriction
to an open cover of X, so the original square is cartesian. This uses no flatness;
J = 0, J = R, empty charts and zero coordinate rings all satisfy the same quotient
and pushout calculation. No morphism is constructed or chosen in this criterion. -/
private theorem affine_algebra_quotient_isPullback
    {X Y X' Y' : Scheme.{u}}
    (j : X' ⟶ X) [IsClosedImmersion j]
    (f : Y' ⟶ X') [IsAffineHom f]
    (g : Y ⟶ X) [IsAffineHom g]
    (B : X.CommAlgebraSheaf) (α : B ≅ 𝒪⁎g)
    (b : B ⟶ 𝒪⁎(f ≫ j))
    (hb : ∀ (U : X.Opens), IsAffineOpen U →
      Function.Surjective (b.right.hom.app (op U)).hom ∧
      RingHom.ker (b.right.hom.app (op U)).hom =
        (RingHom.ker (j.app U).hom).map (B.hom.hom.app (op U)).hom)
    (v : Y' ⟶ Y) (w : v ≫ g = f ≫ j)
    (hv : ∀ U : X.affineOpens,
      v.appLE (g ⁻¹ᵁ U.1) ((f ≫ j) ⁻¹ᵁ U.1)
        (by rw [← w, Scheme.Hom.comp_preimage]) =
      α.inv.right.hom.app (op U.1) ≫ b.right.hom.app (op U.1)) :
    IsPullback v f g j := by
  classical
  have local_sq (U : X.affineOpens) :
      IsPullback
        (v.resLE (g ⁻¹ᵁ U.1) ((f ≫ j) ⁻¹ᵁ U.1)
          (by rw [← w, Scheme.Hom.comp_preimage]))
        (f.resLE (j ⁻¹ᵁ U.1) ((f ≫ j) ⁻¹ᵁ U.1)
          (by rw [Scheme.Hom.comp_preimage]))
        (g ∣_ U.1) (j ∣_ U.1) := by
    let V := g ⁻¹ᵁ U.1
    let W := j ⁻¹ᵁ U.1
    let T := (f ≫ j) ⁻¹ᵁ U.1
    have ev : T ≤ v ⁻¹ᵁ V := by
      change (f ≫ j) ⁻¹ᵁ U.1 ≤ v ⁻¹ᵁ (g ⁻¹ᵁ U.1)
      rw [← w, Scheme.Hom.comp_preimage]
    have ef : T ≤ f ⁻¹ᵁ W := le_rfl
    let vU := v.resLE V T ev
    let fU := f.resLE W T ef
    have : IsAffine V.toScheme := U.2.preimage g
    have : IsAffine W.toScheme := U.2.preimage j
    have : IsAffine T.toScheme := U.2.preimage (f ≫ j)
    have : IsAffine U.1.toScheme := U.2
    have hp : IsPushout (j.app U.1) (B.hom.hom.app (op U.1))
        (f.appLE W T ef) (b.right.hom.app (op U.1)) := by
      apply quotient_pushout
      · have e := (congrArg (fun t ↦ t.hom.app (op U.1)) b.w).symm
        change (f ≫ j).app U.1 = _ at e
        rw [Scheme.Hom.comp_app] at e
        have he : f.appLE W T ef = f.app W := by
          exact f.appLE_eq_app
        rw [he]
        simpa only [TopCat.Sheaf.comp_app] using e
      · exact j.app_surjective U.1 U.2
      · exact (hb U.1 U.2).1
      · exact (hb U.1 U.2).2
    let eB : B.right.obj.obj (op U.1) ≅ Γ(V.toScheme, ⊤) :=
      asIso (α.hom.right.hom.app (op U.1)) ≪≫ V.topIso.symm
    have htop : IsPushout (j ∣_ U.1).appTop (g ∣_ U.1).appTop fU.appTop vU.appTop := by
      apply hp.of_iso U.1.topIso.symm W.topIso.symm eB T.topIso.symm
      · change j.app U.1 ≫ W.topIso.inv =
          U.1.topIso.inv ≫ (j ∣_ U.1).appTop
        rw [Scheme.Hom.appTop, ← Scheme.Hom.resLE_eq_morphismRestrict,
          Scheme.Hom.resLE_app_top]
        simp only [Iso.inv_hom_id_assoc, Scheme.Hom.appLE_eq_app]
        rfl
      · change B.hom.hom.app (op U.1) ≫
            α.hom.right.hom.app (op U.1) ≫ V.topIso.inv =
          U.1.topIso.inv ≫ (g ∣_ U.1).appTop
        have e := congrArg (fun t ↦ t.hom.app (op U.1)) α.hom.w
        change B.hom.hom.app (op U.1) ≫ α.hom.right.hom.app (op U.1) =
          g.app U.1 at e
        rw [← Category.assoc, e]
        rw [Scheme.Hom.appTop, ← Scheme.Hom.resLE_eq_morphismRestrict,
          Scheme.Hom.resLE_app_top]
        simp only [Iso.inv_hom_id_assoc, Scheme.Hom.appLE_eq_app]
        rfl
      · change f.appLE W T ef ≫ T.topIso.inv = W.topIso.inv ≫ fU.appTop
        dsimp [fU]
        rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
        simp only [Iso.inv_hom_id_assoc]
      · change b.right.hom.app (op U.1) ≫ T.topIso.inv =
          (α.hom.right.hom.app (op U.1) ≫ V.topIso.inv) ≫ vU.appTop
        dsimp [vU]
        rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
        simp only [Category.assoc, Iso.inv_hom_id_assoc]
        rw [hv U]
        have e := congrArg (fun t ↦ t.right.hom.app (op U.1)) α.hom_inv_id
        simp only [Under.comp_right, TopCat.Sheaf.comp_app] at e
        change α.hom.right.hom.app (op U.1) ≫ α.inv.right.hom.app (op U.1) = 𝟙 _ at e
        simp only [← Category.assoc, e, Category.id_comp]
    exact affine_pullback_of_pushout vU fU (g ∣_ U.1) (j ∣_ U.1) htop.flip
  let V : X.affineOpens → Y.Opens := fun U ↦ g ⁻¹ᵁ U.1
  let cover := Y.openCoverOfIsOpenCover V
    (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top X))
  apply Scheme.isPullback_of_openCover v f g j cover
  intro U
  let T := (f ≫ j) ⁻¹ᵁ U.1
  let W := j ⁻¹ᵁ U.1
  have ev : T ≤ v ⁻¹ᵁ V U := by
    change (f ≫ j) ⁻¹ᵁ U.1 ≤ v ⁻¹ᵁ (g ⁻¹ᵁ U.1)
    rw [← w, Scheme.Hom.comp_preimage]
  have hs := (local_sq U).paste_vert (isPullback_morphismRestrict j U.1)
  have hi : IsPullback T.ι (v.resLE (V U) T ev) v (cover.f U) := by
    apply IsPullback.flip
    apply IsOpenImmersion.isPullback
    · exact (v.resLE_comp_ι ev).symm
    · change v ⁻¹ᵁ (V U).ι.opensRange = T.ι.opensRange
      simp only [Scheme.Opens.opensRange_ι]
      exact congrArg (fun h ↦ h ⁻¹ᵁ U.1) w
  have hs' : IsPullback (v.resLE (V U) T ev) (T.ι ≫ f) ((V U).ι ≫ g) j := by
    simpa only [Scheme.Hom.resLE_comp_ι, morphismRestrict_ι] using hs
  apply hs'.of_iso' hi.isoPullback.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Iso.refl_hom, Category.comp_id]
    exact hi.isoPullback_inv_snd
  · simp only [Iso.refl_hom, Category.comp_id]
    change hi.isoPullback.inv ≫ T.ι ≫ f = pullback.fst v (cover.f U) ≫ f
    rw [hi.isoPullback_inv_fst_assoc]
  · rfl
  · simp



/-- Compatible quotient maps from an affine structure algebra give compatible
cartesian morphisms of the reduction schemes into its realization.
Source: Stacks Project, Lemma 09ZT, final sentence; Morphisms, Lemmas 01S8 and 01SA.

Proof: For each affine U in X, identify Y over U with Spec B(U) using α, and Yn over
j_n inverse U with Spec O_Yn(r_n inverse U). The ring map b_n(U) induces a morphism
to Y over U, because b_n is an O_X-algebra morphism. Naturality of b_n glues these
local morphisms to u_n : Yn to Y. The surjectivity and kernel formulas identify its
source on each chart with Spec of B(U)/ker(j_n.app U)B(U), the base change of Y to Xn.
Thus the square is cartesian, detected on the affine cover. The displayed compatibility
of b_n(U) with gn sharp implies gn followed by u_(n+1) equals u_n on every chart,
hence globally. Empty charts and zero rings give empty spectra and pose no exception.
(blueprint: lem-weil-pbc-affine-algebra-reductions-cartesian). -/
theorem affine_algebra_reductions_cartesian
    {X Y : Scheme.{u}} (Xn Yn : ℕ → Scheme.{u})
    (j : ∀ n, Xn n ⟶ X) [∀ n, IsClosedImmersion (j n)]
    (fnY : ∀ n, Yn n ⟶ Xn n) [∀ n, IsAffineHom (fnY n)]
    (gn : ∀ n, Yn n ⟶ Yn (n + 1))
    (hw : ∀ n, gn n ≫ (fnY (n + 1) ≫ j (n + 1)) = fnY n ≫ j n)
    (g : Y ⟶ X) [IsAffineHom g]
    (B : X.CommAlgebraSheaf) (α : B ≅ 𝒪⁎g)
    (b : ∀ n, B ⟶ 𝒪⁎(fnY n ≫ j n))
    (hb : ∀ (n : ℕ) (U : X.Opens), IsAffineOpen U →
      Function.Surjective ((b n).right.hom.app (op U)).hom ∧
      RingHom.ker ((b n).right.hom.app (op U)).hom =
        (RingHom.ker ((j n).app U).hom).map (B.hom.hom.app (op U)).hom)
    (hcompat : ∀ (n : ℕ) (U : X.Opens),
      (b (n + 1)).right.hom.app (op U) ≫
        (gn n).appLE ((fnY (n + 1) ≫ j (n + 1)) ⁻¹ᵁ U)
          ((fnY n ≫ j n) ⁻¹ᵁ U)
          (by rw [← Scheme.Hom.comp_preimage, hw n]) =
        (b n).right.hom.app (op U)) :
    ∃ u : ∀ n, Yn n ⟶ Y,
      (∀ n, IsPullback (u n) (fnY n) g (j n)) ∧
      (∀ n, gn n ≫ u (n + 1) = u n) := by
  classical
  have hm (n : ℕ) : ∃ (v : Yn n ⟶ Y) (w : v ≫ g = fnY n ≫ j n),
      (∀ U : X.affineOpens,
        v.appLE (g ⁻¹ᵁ U.1) ((fnY n ≫ j n) ⁻¹ᵁ U.1)
          (by rw [← w, Scheme.Hom.comp_preimage]) =
        (α.inv ≫ b n).right.hom.app (op U.1)) ∧
      ∀ (v' : Yn n ⟶ Y) (w' : v' ≫ g = fnY n ≫ j n),
        (∀ U : X.affineOpens,
          v'.appLE (g ⁻¹ᵁ U.1) ((fnY n ≫ j n) ⁻¹ᵁ U.1)
            (by rw [← w', Scheme.Hom.comp_preimage]) =
          (α.inv ≫ b n).right.hom.app (op U.1)) → v' = v :=
    unique_over_map_of_algebra (fnY n ≫ j n) g (α.inv ≫ b n)
  choose v w ha hu using hm
  refine ⟨v, ?_, ?_⟩
  · intro n
    apply affine_algebra_quotient_isPullback (j n) (fnY n) g B α (b n)
      (hb n) (v n) (w n)
    intro U
    simpa only [Under.comp_right, TopCat.Sheaf.comp_app] using ha n U
  · intro n
    have w' : (gn n ≫ v (n + 1)) ≫ g = fnY n ≫ j n := by
      rw [Category.assoc, w, hw]
    apply hu n (gn n ≫ v (n + 1)) w'
    intro U
    rw [← Scheme.Hom.appLE_comp_appLE (gn n) (v (n + 1))
      (g ⁻¹ᵁ U.1) ((fnY (n + 1) ≫ j (n + 1)) ⁻¹ᵁ U.1)
      ((fnY n ≫ j n) ⁻¹ᵁ U.1)
      (by rw [← w (n + 1), Scheme.Hom.comp_preimage])
      (by rw [← Scheme.Hom.comp_preimage, hw n])]
    rw [ha (n + 1) U]
    simp only [Under.comp_right, TopCat.Sheaf.comp_app, Category.assoc]
    rw [hcompat]

end AlgebraicGeometry
