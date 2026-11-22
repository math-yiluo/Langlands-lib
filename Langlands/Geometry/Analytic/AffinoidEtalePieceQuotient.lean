import Langlands.Geometry.Analytic.AffinoidPointRelationQuotient
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Langlands.Geometry.Analytic.SpaceAnalytificationEtaleReflection

/-! # Quotients of affinoid pieces of étale charts -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open SaturatedAtlasPresentation

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "M" => localizedAffinoidSpectrum (K := K)

private abbrev spectrumMap {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B) :
    M B ⟶ M A := SmallAffinoidSpectrum.localizedMapEquiv.{u, u} A B f

private theorem kernelPair_piece_isPullback
    {C : Type*} [Category* C] {P E X Y W R : C}
    {p : P ⟶ E} {q : P ⟶ W} {e : E ⟶ X} {F : X ⟶ Y} {b : W ⟶ Y} [Mono b]
    {r s : R ⟶ P}
    (hP : IsPullback p q (e ≫ F) b) (hR : IsPullback r s (p ≫ e) (p ≫ e)) :
    IsPullback (s ≫ p) r e (p ≫ e) := by
  let : Mono p := hP.mono_fst_of_mono
  have hw : (s ≫ p) ≫ e = r ≫ p ≫ e := (Category.assoc _ _ _).trans hR.w.symm
  have hLift (c : PullbackCone e (p ≫ e)) :
      ∃ l : c.pt ⟶ R, l ≫ (s ≫ p) = c.fst ∧ l ≫ r = c.snd := by
    have hc : c.fst ≫ (e ≫ F) = (c.snd ≫ q) ≫ b := by
      rw [← Category.assoc c.fst e F, c.condition]
      simp only [Category.assoc, hP.w]
    let z := hP.lift c.fst (c.snd ≫ q) hc
    have hz : z ≫ p = c.fst := hP.lift_fst _ _ _
    have hcomm : c.snd ≫ p ≫ e = z ≫ p ≫ e := by
      rw [← Category.assoc z, hz, c.condition]
    let l := hR.lift c.snd z hcomm
    refine ⟨l, ?_, hR.lift_fst _ _ _⟩
    rw [← Category.assoc, show l ≫ s = z from hR.lift_snd _ _ _, hz]
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun c => (hLift c).choose) (fun c => (hLift c).choose_spec.1)
    (fun c => (hLift c).choose_spec.2) (fun c m hm₁ hm₂ => by
      apply hR.hom_ext
      · exact hm₂.trans (hLift c).choose_spec.2.symm
      · apply (cancel_mono p).mp
        simpa only [Category.assoc] using hm₁.trans (hLift c).choose_spec.1.symm))

/-- Quotient data of an affinoid piece with a finite étale cover and its
map to the ambient localized analytic space. -/
structure AffinoidEtalePieceQuotient {B : PresentedAffinoidAlgebra K}
    {Y : LocalizedCategory.{u, u, u} (K := K)} (a : M B ⟶ Y) where
  algebra : PresentedAffinoidAlgebra K
  coverMap : BoundedAlgHom K algebra B
  cover_finiteBanach : coverMap.IsFiniteBanach
  cover_finiteEtale : coverMap.AlgebraicallyFiniteEtale
  cover_surjective : Function.Surjective (BanachSpectrum.comap coverMap.toBoundedRingHom)
  map : M algebra ⟶ Y
  cover_comp_map : spectrumMap coverMap ≫ map = a
  equalizes {T : LocalizedCategory.{u, u, u} (K := K)} (l r : T ⟶ M B) :
    l ≫ a = r ≫ a → l ≫ spectrumMap coverMap = r ≫ spectrumMap coverMap

set_option backward.isDefEq.respectTransparency false in
/-- An affinoid piece of an étale map over a monic affinoid target test
admits a quotient over the ambient analytification. -/
def affinoidEtalePieceQuotient
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} {A B : PresentedAffinoidAlgebra K}
    {Y : LocalizedCategory.{u, u, u} (K := K)} {p : PointFamily K X Y}
    (hp : IsAnalytification K X Y p) (hs : IsSeparated X) (ht : LocallyOfFiniteTypeOverBase X)
    (x : RingPoints K X B) (f : BoundedAlgHom K A B)
    (hf : f.IsFiniteBanach) (hfEt : f.AlgebraicallyFiniteEtale)
    {E Z : LocalizedCategory.{u, u, u} (K := K)} (e : E ⟶ Y) (he : etale e)
    (u₀ : M B ⟶ E) (hu : u₀ ≫ e = affinoidPointHom hp hs ht B x)
    (F : Y ⟶ Z) (b : M A ⟶ Z) [Mono b]
    (hP : IsPullback u₀ (spectrumMap f) (e ≫ F) b) :
    AffinoidEtalePieceQuotient (affinoidPointHom hp hs ht B x) := by
  let V := affinoidPointRelation hs f hf x
  have hw : affinoidPointHom hp hs ht B x ≫ F = spectrumMap f ≫ b := by
    rw [← hu, Category.assoc]
    exact hP.w
  have hR := V.localized_isPullback hp hs ht F b hw
  have hRu : IsPullback (spectrumMap V.first) (spectrumMap V.second)
      (u₀ ≫ e) (u₀ ≫ e) := by
    rw [hu]
    exact hR
  have hV₁ := etale_snd_of_isPullback_of_etalePullbacks K localizedEtalePullbackBaseChange
    (kernelPair_piece_isPullback hP hRu) he
  have hV₂ := etale_snd_of_isPullback_of_etalePullbacks K localizedEtalePullbackBaseChange
    (kernelPair_piece_isPullback hP hRu.flip) he
  let Q := V.finiteEtaleQuotient hfEt hV₁ hV₂
  let href := V.exists_descendedPoint Q
  let z := href.choose
  have hz := href.choose_spec
  let m := affinoidPointHom hp hs ht Q.algebra z
  refine ⟨Q.algebra, Q.coverMap, Q.coverMap_isFiniteBanach, Q.coverMap_finiteEtale,
    Q.coverMap_spectrum_surjective, m, ?_, ?_⟩
  · exact (affinoidPointHom_changeRing hp hs ht Q.coverMap z).symm.trans
      (congrArg (affinoidPointHom hp hs ht B) hz)
  intro T l r h
  have hmatch : spectrumMap V.first ≫ spectrumMap Q.coverMap =
      spectrumMap V.second ≫ spectrumMap Q.coverMap := by
    rw [← SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} Q.coverMap V.first,
      ← SmallAffinoidSpectrum.localizedMapEquiv_comp.{u, u} Q.coverMap V.second]
    apply congrArg (SmallAffinoidSpectrum.localizedMapEquiv.{u, u} Q.algebra V.algebra)
    exact BoundedAlgHom.ext (RingHom.congr_fun (congrArg CommRingCat.Hom.hom Q.relation_isPushout.w))
  let j := hR.lift l r h
  have hl : j ≫ spectrumMap V.first = l := hR.lift_fst l r h
  have hr : j ≫ spectrumMap V.second = r := hR.lift_snd l r h
  simpa only [← Category.assoc, hl, hr] using congrArg (j ≫ ·) hmatch

end Langlands.Analytic.SpaceAnalytification
