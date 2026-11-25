/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PicardUniversalSingleRankMatch
import all WeilConjectures.AlgebraicGeometry.PicardUniversalRankMatchConjunction
import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # Source locality of one universal direct-image rank condition

Source: Stacks Project, Tag 0BDP, first three proof paragraphs, local rank conditions.
(blueprint: lem-sc-picard-single-rank-source-local).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

private noncomputable def tensorRestrict {A B : Scheme.{u}} (a : A ⟶ B)
    [IsOpenImmersion a] : Modules.tensorPullback a ≅ Modules.restrictFunctor a :=
  (tensorIso a) ≪≫ (Modules.restrictFunctorIsoPullback a).symm

-- Sectionwise proof adapted from the private helper of the same name in
-- WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections.
private noncomputable def pushforward_restrict_square {T' X' : Scheme.{u}}
    {X T : Scheme.{u}} (f : X ⟶ T) (g : T' ⟶ T) [IsOpenImmersion g]
    (g' : X' ⟶ X) [IsOpenImmersion g']
    (f' : X' ⟶ T') (sq : IsPullback g' f' f g) :
    Modules.pushforward f ⋙ Modules.restrictFunctor g ≅
      Modules.restrictFunctor g' ⋙ Modules.pushforward f' := by
  unfold Modules.restrictFunctor Modules.pushforward
  refine SheafOfModules.pushforwardComp _ _ ≪≫ ?_ ≪≫
    (SheafOfModules.pushforwardComp _ _).symm
  let e : g.opensFunctor ⋙ TopologicalSpace.Opens.map f.base ≅
      TopologicalSpace.Opens.map f'.base ⋙ g'.opensFunctor :=
    NatIso.ofComponents (fun W ↦ eqToIso
      (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip W).symm)
  refine SheafOfModules.pushforwardCongr₂ _ e.symm ?_
  ext W x
  change X.presheaf.map
      (eqToHom (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
        sq.flip W.unop)).op
      (f.app (g ''ᵁ W.unop) ((g.appIso W.unop).inv x)) =
    (g'.appIso (f' ⁻¹ᵁ W.unop)).inv (f'.app W.unop x)
  have h : f.app (g ''ᵁ W.unop) ≫
      X.presheaf.map (eqToHom
        (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
          sq.flip W.unop)).op ≫ (g'.appIso (f' ⁻¹ᵁ W.unop)).hom =
      (g.appIso W.unop).hom ≫ f'.app W.unop := by
    simp only [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE,
      Scheme.Hom.map_appLE, Scheme.Hom.appLE_comp_appLE]
    congr 1
    exact sq.w
  have hx := ConcreteCategory.congr_hom h ((g.appIso W.unop).inv x)
  apply (ConcreteCategory.bijective_of_isIso (g'.appIso (f' ⁻¹ᵁ W.unop)).hom).1
  simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply,
    Iso.hom_inv_id_apply] using hx

-- Keep the square abstract here so elaboration does not unfold chosen pullback cones.
private noncomputable def directImageOpenIso {X X' T A S : Scheme.{u}}
    (p : X ⟶ T) (i : A ⟶ T) [IsOpenImmersion i]
    (j : X' ⟶ X) [IsOpenImmersion j] (p' : X' ⟶ A)
    (sq : IsPullback j p' p i) (q : X ⟶ S) (q' : X' ⟶ S)
    (hq : j ≫ q = q') (F : S.Modules) :
    (Modules.tensorPullback i).obj
      ((Modules.pushforward p).obj ((Modules.tensorPullback q).obj F)) ≅
    (Modules.pushforward p').obj ((Modules.tensorPullback q').obj F) := by
  refine (tensorRestrict i).app _ ≪≫
    (pushforward_restrict_square p i j p' sq).app _ ≪≫
    (Modules.pushforward p').mapIso (?_)
  refine ((tensorRestrict j).app _).symm ≪≫
    (Classical.choice (Modules.nonempty_tensorPullbackComp j q)).symm.app F ≪≫
      eqToIso (by rw [hq])

/-- Local single-rank conditions on a neighbourhood of every test point imply the condition.
No flatness, properness, connectedness or finite local freeness assumptions are needed.
Source: Stacks Project, Tag 0BDP, first three proof paragraphs, local rank conditions.
(blueprint: lem-sc-picard-single-rank-source-local).

Proof:
1. Fix a further test h:T' to T and a point t'. Choose V around h(t') on which
   the condition holds. Its inverse image V' is an open neighbourhood of t'.
   Restrict h to a map V' to V, and apply the universal local condition on V at t'.
2. This supplies a still smaller open U in V', a rank r, and the direct-image and
   reference-module rank-r witnesses there. Regard U as an open subscheme of T'
   using the composite of open immersions.
3. Open base change identifies the restriction of p_*q^*F to V' with the direct
   image for the restricted test map. Tensor pullback composes up to its canonical
   isomorphism. These isomorphisms transport both rank witnesses to U as an open
   of T'. Hence the defining condition holds for h and t'. Empty test schemes
   have no points, so the conclusion is vacuous. -/
theorem picardUniversalSingleRankMatch_of_source_local {X S T : Scheme.{u}}
    (f : X ⟶ S) (E F : X.Modules) (g : T ⟶ S)
    (hlocal : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧
      PicardUniversalSingleRankMatch f E F (V.ι ≫ g)) :
    PicardUniversalSingleRankMatch f E F g := by
  intro T' h t
  obtain ⟨V, htV, hV⟩ := hlocal (h t)
  let A := h ⁻¹ᵁ V
  let v : A.toScheme ⟶ V.toScheme := h ∣_ V
  have htA : t ∈ A := htV
  obtain ⟨U, htU, r, hFr, hEr⟩ := hV v ⟨t, htA⟩
  have hv : v ≫ V.ι ≫ g = A.ι ≫ h ≫ g := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
  have hFr' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback U.ι).obj
        ((Modules.pushforward (pullback.snd f (A.ι ≫ h ≫ g))).obj
          ((Modules.tensorPullback (pullback.fst f (A.ι ≫ h ≫ g))).obj F))) r := by
    convert hFr using 1
    exact congrArg (fun k : A.toScheme ⟶ S ↦
      (Modules.tensorPullback U.ι).obj
        ((Modules.pushforward (pullback.snd f k)).obj
          ((Modules.tensorPullback (pullback.fst f k)).obj F))) hv.symm
  have hvU : U.ι ≫ v ≫ V.ι ≫ g = U.ι ≫ A.ι ≫ h ≫ g := by rw [hv]
  have hEr' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Modules.tensorPullback (pullback.fst f (U.ι ≫ A.ι ≫ h ≫ g))).obj E) r := by
    exact (congrArg (fun k : U.toScheme ⟶ S ↦
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback (pullback.fst f k)).obj E) r) hvU).mp hEr
  let j := U.ι ≫ A.ι
  let W := j.opensRange
  let e := IsOpenImmersion.isoOfRangeEq j W.ι (by simp [W])
  have he : e.inv ≫ U.ι ≫ A.ι = W.ι := by
    simpa [j] using IsOpenImmersion.isoOfRangeEq_inv_fac j W.ι (by simp [W])
  have htW : t ∈ W := ⟨⟨⟨t, htA⟩, htU⟩, rfl⟩
  refine ⟨W, htW, r, ?_, ?_⟩
  · let M := (Modules.pushforward (pullback.snd f (h ≫ g))).obj
        ((Modules.tensorPullback (pullback.fst f (h ≫ g))).obj F)
    let jX : pullback f (A.ι ≫ h ≫ g) ⟶ pullback f (h ≫ g) :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ A.ι) (by
        rw [Category.assoc]; exact pullback.condition)
    have hjX : jX ≫ pullback.fst f (h ≫ g) =
        pullback.fst f (A.ι ≫ h ≫ g) := by simp [jX]
    have sq : IsPullback jX (pullback.snd f (A.ι ≫ h ≫ g))
        (pullback.snd f (h ≫ g)) A.ι := by
      apply IsPullback.of_right (h₁₂ := pullback.fst f (h ≫ g)) (h₂₂ := h ≫ g)
      · simpa [jX] using IsPullback.of_hasPullback f (A.ι ≫ h ≫ g)
      · simp [jX]
      · exact IsPullback.of_hasPullback f (h ≫ g)
    have : IsOpenImmersion jX := MorphismProperty.of_isPullback sq.flip inferInstance
    let c := directImageOpenIso (pullback.snd f (h ≫ g)) A.ι jX
      (pullback.snd f (A.ι ≫ h ≫ g)) sq (pullback.fst f (h ≫ g))
      (pullback.fst f (A.ι ≫ h ≫ g)) hjX F
    let := hFr'
    have hUr : ((Modules.tensorPullback U.ι).obj
        ((Modules.tensorPullback A.ι).obj M)).IsFiniteLocallyFreeOfRank r :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
        ((Modules.tensorPullback U.ι).mapIso c.symm)
    obtain ⟨ccomp⟩ := Modules.nonempty_tensorPullbackComp U.ι A.ι
    have hUr' : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Modules.tensorPullback A.ι ⋙ Modules.tensorPullback U.ι).obj M) r := hUr
    let := hUr'
    have hjr : ((Modules.tensorPullback j).obj M).IsFiniteLocallyFreeOfRank r :=
      SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso (ccomp.app M).symm
    have hWr := Modules.isFiniteLocallyFreeOfRank_tensorPullback_comp e.inv j M r hjr
    simpa only [j, Category.assoc, he] using hWr
  · have ha : e.inv ≫ (U.ι ≫ A.ι ≫ h ≫ g) = W.ι ≫ h ≫ g := by
      rw [← Category.assoc e.inv U.ι, ← Category.assoc (e.inv ≫ U.ι) A.ι]
      rw [Category.assoc e.inv U.ι A.ι, he]
    let q : pullback f (W.ι ≫ h ≫ g) ⟶
        pullback f (U.ι ≫ A.ι ≫ h ≫ g) :=
      pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ e.inv) (by
        rw [Category.assoc, ha]; exact pullback.condition)
    have hq : q ≫ pullback.fst f (U.ι ≫ A.ι ≫ h ≫ g) =
        pullback.fst f (W.ι ≫ h ≫ g) := by simp [q]
    simpa only [hq] using
      Modules.isFiniteLocallyFreeOfRank_tensorPullback_comp q
        (pullback.fst f (U.ι ≫ A.ι ≫ h ≫ g)) E r hEr'

end AlgebraicGeometry.Scheme
