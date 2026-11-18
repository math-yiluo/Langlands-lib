import Langlands.Geometry.Analytic.AnalyticOpenImmersionTargetTopology
import Langlands.Geometry.Analytic.EtaleGeometricPointPullbacks

/-! # Étale target descent of open immersions from morphism descent -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A map with image in an open immersion lifts uniquely through the immersion. -/
theorem openImmersion.existsUnique_lift_of_range
    {X Y T : LocalizedCategory.{u, v, w} (K := K)}
    {f : X ⟶ Y} (hf : openImmersion f) (t : T ⟶ Y)
    (ht : ∀ z, localizedSpaceFunctor.map t z ∈ Set.range (localizedSpaceFunctor.map f)) :
    ∃! a : T ⟶ X, a ≫ f = t := by
  obtain ⟨U, hU, e, rfl⟩ := hf
  let D := (presentationOf Y).openDomain U hU
  have hmem (z : localizedSpaceFunctor.obj T) :
      localizedSpaceFunctor.map t z ∈ D.carrier := by
    obtain ⟨x, hx⟩ := ht z
    rw [Functor.map_comp, TopCat.comp_app, domainι_apply] at hx
    exact hx ▸ (localizedSpaceFunctor.map e.hom x).property
  let a := domainLift D t hmem ≫ e.inv
  have ha : a ≫ (e.hom ≫ domainι Y D) = t := by simp [a]
  exact ⟨a, ha, fun _ hb => (cancel_mono (e.hom ≫ domainι Y D)).1 (hb.trans ha.symm)⟩

variable {X Y T : LocalizedCategory.{u, u, u} (K := K)}
  {ι : Type w} {V P : ι → LocalizedCategory.{u, u, u} (K := K)}
  {f : X ⟶ Y} {g : ∀ i, V i ⟶ Y}
  {p : ∀ i, P i ⟶ X} {q : ∀ i, P i ⟶ V i}

/-- Étale pullbacks and the analytic Hom sheaf property give the universal
factorization through a map whose pullbacks are open immersions. -/
theorem existsUnique_lift_of_openImmersion_etalePullbacks
    (hBase : LocalizedEtalePullbackStatement.{u, u} K)
    (hHom : ∀ (S Z : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj Z))
    (h : ∀ i, IsPullback (p i) (q i) f (g i)) (hg : ∀ i, etale (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (z : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) z = y)
    (hq : ∀ i, openImmersion (q i)) (t : T ⟶ Y)
    (ht : ∀ z, localizedSpaceFunctor.map t z ∈ Set.range (localizedSpaceFunctor.map f)) :
    ∃! a : T ⟶ X, a ≫ f = t := by
  classical
  choose W r s hW hs using fun i => hBase (g i) t (hg i)
  have localLift (i : ι) {Z : LocalizedCategory.{u, u, u} (K := K)} (b : Z ⟶ W i) :
      ∃! a : Z ⟶ X, a ≫ f = b ≫ s i ≫ t := by
    have hrange : localizedSpaceFunctor.map (g i) ⁻¹' Set.range (localizedSpaceFunctor.map f) =
        Set.range (localizedSpaceFunctor.map (q i)) := by
      simpa only [Set.image_univ, Set.preimage_univ] using
        preimage_image_eq_image_preimage_of_isPullback (h i) Set.univ
    have hcomp : (b ≫ r i) ≫ g i = (b ≫ s i) ≫ t := by
      rw [Category.assoc, (hW i).w, Category.assoc]
    obtain ⟨c, hc, huniq⟩ := (hq i).existsUnique_lift_of_range (b ≫ r i) (by
      intro z
      rw [← hrange]
      simpa only [Set.mem_preimage, ← TopCat.comp_app, ← Functor.map_comp, hcomp] using
        ht (localizedSpaceFunctor.map (b ≫ s i) z))
    refine ⟨c ≫ p i, ?_, ?_⟩
    · change (c ≫ p i) ≫ f = b ≫ s i ≫ t
      rw [Category.assoc, (h i).w, ← Category.assoc, hc, hcomp, Category.assoc]
    · intro a ha
      have hcomm : a ≫ f = (b ≫ r i) ≫ g i := by
        rw [ha, Category.assoc, (hW i).w]
      let l := (h i).lift a (b ≫ r i) hcomm
      have hl : l = c := huniq l ((h i).lift_snd _ _ _)
      rw [← hl]
      exact ((h i).lift_fst _ _ _).symm
  let B : EtaleSite T := MorphismProperty.Over.mk ⊤ (𝟙 T) (etale_of_isIso _)
  let C (i : ι) : EtaleSite T := MorphismProperty.Over.mk ⊤ (s i) (hs i)
  let π (i : ι) : C i ⟶ B := MorphismProperty.Over.homMk (s i) (Category.comp_id _)
  have hπ : Presieve.ofArrows C π ∈ etalePrecoverage T B := by
    apply ofArrows_mem_etalePrecoverage_iff.mpr
    intro z
    obtain ⟨i, x, hx⟩ := hcover (localizedSpaceFunctor.map t z)
    obtain ⟨y, _, hy⟩ := exists_point_of_isPullback (r i) (s i) (g i) t (hW i) x z hx
    exact ⟨i, y, hy⟩
  let F (Z : LocalizedCategory.{u, u, u} (K := K)) :=
    (MorphismProperty.Over.forget etale ⊤ T ⋙ Over.forget T).op ⋙ yoneda.obj Z
  have hSheaf (Z : LocalizedCategory.{u, u, u} (K := K)) :
      (Presieve.ofArrows C π).IsSheafFor (F Z) :=
    (hHom T Z).isSheafFor_of_mem_precoverage hπ
  choose a ha using fun i => (localLift i (𝟙 (W i))).exists
  have ha' (i : ι) : a i ≫ f = s i ≫ t := by simpa only [Category.id_comp] using ha i
  have hCompatible : Presieve.Arrows.Compatible (F X) π a := by
    intro i j Z bi bj hb
    let bi' : Z.left ⟶ W i := bi.left
    let bj' : Z.left ⟶ W j := bj.left
    change bi' ≫ a i = bj' ≫ a j
    have hb' : bi' ≫ s i = bj' ≫ s j := congrArg (fun m => m.left) hb
    apply (localLift i bi').unique
    · rw [Category.assoc, ha' i]
    · rw [Category.assoc, ha' j, ← Category.assoc, ← hb', Category.assoc]
  obtain ⟨l, hl, huniq⟩ :=
    (Presieve.isSheafFor_arrows_iff (π := π) (P := F X)).mp (hSheaf X) a hCompatible
  let l' : T ⟶ X := l
  have hl' (i : ι) : s i ≫ l' = a i := hl i
  have hlf : l' ≫ f = t := by
    apply (hSheaf Y).isSeparatedFor.ext
    rintro _ _ ⟨i⟩
    change s i ≫ (l' ≫ f) = s i ≫ t
    rw [← Category.assoc, hl' i, ha' i]
  refine ⟨l', hlf, fun m hm => huniq m fun i => ?_⟩
  change s i ≫ m = a i
  apply (localLift i (𝟙 (W i))).unique
  · rw [Category.assoc, hm, Category.id_comp]
  · exact ha i

section OpenImage

variable
    (hBase : LocalizedEtalePullbackStatement.{u, u} K)
    (hHom : ∀ (S Z : LocalizedCategory.{u, u, u} (K := K)),
      Presieve.IsSheaf (etaleTopology S)
        ((MorphismProperty.Over.forget _ _ S ⋙ Over.forget S).op ⋙ yoneda.obj Z))
    (h : ∀ i, IsPullback (p i) (q i) f (g i)) (hg : ∀ i, etale (g i))
    (hcover : ∀ y : localizedSpaceFunctor.obj Y,
      ∃ (i : ι) (z : localizedSpaceFunctor.obj (V i)),
        localizedSpaceFunctor.map (g i) z = y)
    (hq : ∀ i, openImmersion (q i))

/-- With étale pullbacks and analytic Hom descent, the open image lift
of a map whose étale target pullbacks are open immersions is an isomorphism. -/
def openImageIsoOfEtalePullbacks :
    X ≅ domainObj Y (openImageDomainOfEtalePullbacks h hg hcover hq) := by
  let D := openImageDomainOfEtalePullbacks h hg hcover hq
  let a := openImageLiftOfEtalePullbacks h hg hcover hq
  have ha : a ≫ domainι Y D = f := openImageLiftOfEtalePullbacks_comp h hg hcover hq
  have hmem (z : localizedSpaceFunctor.obj (domainObj Y D)) :
      localizedSpaceFunctor.map (domainι Y D) z ∈ Set.range (localizedSpaceFunctor.map f) := by
    rw [domainι_apply]
    exact z.property
  obtain ⟨b, hb⟩ := Classical.indefiniteDescription _
    (existsUnique_lift_of_openImmersion_etalePullbacks hBase hHom h hg hcover hq _ hmem).exists
  have hab : a ≫ b = 𝟙 X :=
    (existsUnique_lift_of_openImmersion_etalePullbacks hBase hHom h hg hcover hq
      f (fun z => ⟨z, rfl⟩)).unique (by rw [Category.assoc, hb, ha]) (Category.id_comp _)
  have hba : b ≫ a = 𝟙 (domainObj Y D) := by
    apply (cancel_mono (domainι Y D)).1
    rw [Category.assoc, ha, hb, Category.id_comp]
  exact ⟨a, b, hab, hba⟩

include hBase hHom h hg hcover hq in
/-- Open immersions descend along a jointly surjective étale target family
when localized étale pullbacks and the analytic Hom sheaf property are supplied. -/
theorem openImmersion_of_etalePullbacks_of_homSheaf : openImmersion f :=
  ⟨_, isOpen_range_of_openImmersion_etalePullbacks h hg hcover hq,
    openImageIsoOfEtalePullbacks hBase hHom h hg hcover hq,
    openImageLiftOfEtalePullbacks_comp h hg hcover hq⟩

end OpenImage

end Langlands.Analytic.SaturatedAtlasPresentation
