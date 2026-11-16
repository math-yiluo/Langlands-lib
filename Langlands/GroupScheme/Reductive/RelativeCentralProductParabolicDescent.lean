import Langlands.GroupScheme.Reductive.RelativeCentralProductParabolicInverse
import Langlands.GroupScheme.Reductive.MultiplicationBaseChange
import Langlands.GroupScheme.SubgroupFunctor.EtaleComparison

/-! # Descent of relative parabolic extensions in a central product -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {P G : GroupScheme S}

/-- Relative parabolicity after an etale map descends to its open image. -/
theorem IsRelativeParabolicSubgroup.of_etaleImage (hG : IsReductive G)
    (j : P ⟶ G) {V : Scheme.{u}} (q : V ⟶ S) [Etale q]
    (h : IsRelativeParabolicSubgroup ((GroupScheme.baseChange q).map j)) :
    IsRelativeParabolicSubgroup
      ((GroupScheme.baseChange (TorusIsomorphismLocus.etaleImage q).ι).map j) := by
  let U := TorusIsomorphismLocus.etaleImage q
  let q' : V ⟶ U := IsOpenImmersion.lift U.ι q (by
    simp [U, TorusIsomorphismLocus.etaleImage])
  have hq' : q' ≫ U.ι = q := IsOpenImmersion.lift_fac _ _ _
  have : Surjective q' := ⟨fun ⟨x, ⟨y, hy⟩⟩ =>
    ⟨y, by
      apply U.ι.injective
      change (q' ≫ U.ι) y = x
      rw [hq']
      exact hy⟩⟩
  have : Etale (q' ≫ U.ι) := by rw [hq']; infer_instance
  have : Etale q' := Etale.of_comp q' U.ι
  apply IsRelativeParabolicSubgroup.of_etale_surjective (hG.baseChange U.ι) q'
  let eP := Descent.pullbackComparison U.ι q' q hq' P
  let eG := Descent.pullbackComparison U.ι q' q hq' G
  have ht := (h.iso_comp eP).comp_iso eG.symm
  have he : eP.hom ≫ (GroupScheme.baseChange q).map j ≫ eG.inv =
      (GroupScheme.baseChange q').map ((GroupScheme.baseChange U.ι).map j) := by
    rw [← Category.assoc, ← Descent.pullbackComparison_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simpa only [Iso.symm_hom, Category.assoc, he] using ht

/-- Relative parabolicity can be checked on any etale covering family. -/
theorem IsRelativeParabolicSubgroup.of_etaleCover (hG : IsReductive G)
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S) (j : P ⟶ G)
    (h : ∀ a, IsRelativeParabolicSubgroup ((GroupScheme.baseChange (𝒰.f a)).map j)) :
    IsRelativeParabolicSubgroup j := by
  let : ∀ a, Etale (𝒰.f a) := 𝒰.map_prop
  let O : 𝒰.I₀ → S.Opens := fun a => TorusIsomorphismLocus.etaleImage (𝒰.f a)
  let 𝒱 := S.openCoverOfIsOpenCover O (by
    apply TopologicalSpace.IsOpenCover.mk
    apply top_le_iff.mp
    intro s _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨a, t, ht⟩ := 𝒰.exists_eq s
    exact ⟨a, t, ht⟩)
  apply IsRelativeParabolicSubgroup.of_openCover hG 𝒱 j
  intro a
  exact IsRelativeParabolicSubgroup.of_etaleImage hG j (𝒰.f a) (h a)

namespace CentralProductParabolic.RelativeExtension

variable {D Z P' : GroupScheme S} {d : D ⟶ G} {i' : P' ⟶ D}

/-- Central-product uniqueness makes arbitrary local extensions agree on
pairwise overlaps, with the canonical iterated-base-change comparison. -/
theorem overlap_range_eq {K : Precoverage Scheme.{u}}
    (𝒰 : Scheme.Cover.{u} K S)
    (w : ∀ a, RelativeExtension ((GroupScheme.baseChange (𝒰.f a)).map d)
      ((GroupScheme.baseChange (𝒰.f a)).map i'))
    (hG : IsReductive G) (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _))) (a b : 𝒰.I₀) :
    SubgroupFunctor.range
      ((GroupScheme.baseChange (pullback.fst (𝒰.f a) (𝒰.f b))).map (w a).inclusion) =
    SubgroupFunctor.range
      ((GroupScheme.baseChange (pullback.snd (𝒰.f a) (𝒰.f b))).map (w b).inclusion ≫
        (SubgroupFunctor.CoverDescent.overlapSquareIso 𝒰 a b G).inv) := by
  let eD := SubgroupFunctor.CoverDescent.overlapSquareIso 𝒰 a b D
  let eG := SubgroupFunctor.CoverDescent.overlapSquareIso 𝒰 a b G
  let eP := SubgroupFunctor.CoverDescent.overlapSquareIso 𝒰 a b P'
  let v := ((w a).baseChange (hG.baseChange (𝒰.f a))
    (pullback.fst (𝒰.f a) (𝒰.f b))).transport eD eG eP
      (SubgroupFunctor.CoverDescent.overlapSquareIso_naturality 𝒰 a b d)
      (SubgroupFunctor.CoverDescent.overlapSquareIso_naturality 𝒰 a b i')
  let v' := (w b).baseChange (hG.baseChange (𝒰.f b))
    (pullback.snd (𝒰.f a) (𝒰.f b))
  let z₁ := (GroupScheme.baseChange (𝒰.f b)).map z
  have hz₁ : IsCentral z₁ := hz.baseChange (𝒰.f b)
  have hp₁ : IsCentralIsogeny (prodHom z₁ ((GroupScheme.baseChange (𝒰.f b)).map d)
      (hz₁.commute_values _)) :=
    (isCentralIsogeny_baseChange_prodHom_iff (𝒰.f b) z d _ _).mp
      (hprod.baseChange (𝒰.f b))
  let q := pullback.snd (𝒰.f a) (𝒰.f b)
  let z₂ := (GroupScheme.baseChange q).map z₁
  have hz₂ : IsCentral z₂ := hz₁.baseChange q
  have hp₂ : IsCentralIsogeny
      (prodHom z₂ ((GroupScheme.baseChange q).map ((GroupScheme.baseChange (𝒰.f b)).map d))
        (hz₂.commute_values _)) :=
    (isCentralIsogeny_baseChange_prodHom_iff q z₁
      ((GroupScheme.baseChange (𝒰.f b)).map d) _ _).mp (hp₁.baseChange q)
  have heq := v'.range_unique v ((hG.baseChange (𝒰.f b)).baseChange q) z₂ hz₂ hp₂
  change SubgroupFunctor.range
    ((GroupScheme.baseChange (pullback.snd (𝒰.f a) (𝒰.f b))).map (w b).inclusion) =
    SubgroupFunctor.range
      ((GroupScheme.baseChange (pullback.fst (𝒰.f a) (𝒰.f b))).map (w a).inclusion ≫
        eG.hom) at heq
  have hback := (SubgroupFunctor.range_comp_iso_eq_iff _ _ eG.symm).mpr heq
  simpa only [Iso.symm_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    hback.symm

/-- Descent produces an actual extension from local extensions along an
arbitrary etale covering family. -/
def ofEtaleCover [Mono i'.hom.hom]
    (𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S)
    (w : ∀ a, RelativeExtension ((GroupScheme.baseChange (𝒰.f a)).map d)
      ((GroupScheme.baseChange (𝒰.f a)).map i'))
    (hG : IsReductive G) (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _))) :
    RelativeExtension d i' := by
  let F := fun a => SubgroupFunctor.range (w a).inclusion
  have hF : SubgroupFunctor.CoverDescent.IsMatching 𝒰 F :=
    SubgroupFunctor.CoverDescent.isMatching_of_overlap_range_eq 𝒰
      (fun a => (w a).group) (fun a => (w a).inclusion)
      (fun a b => overlap_range_eq 𝒰 w hG z hz hprod a b)
  have hc : ∀ a, (F a).IsClosedRepresentable := fun a =>
    ⟨(w a).group, (w a).inclusion, ⟨(w a).parabolic.mono, rfl⟩,
      relativeParabolicClosed _ _ _ _ (hG.baseChange (𝒰.f a)) (w a).parabolic⟩
  let R := SubgroupFunctor.CoverDescent.closedRepresentativeEtale 𝒰 F hF hc
  have hlocal (a : 𝒰.I₀) :
      SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f a)).map R.hom) =
        SubgroupFunctor.range (w a).inclusion := by
    rw [SubgroupFunctor.range_baseChangeHom, R.represents.2,
      SubgroupFunctor.CoverDescent.baseChange_subgroup 𝒰 F hF a]
  have hR : IsRelativeParabolicSubgroup R.hom := by
    apply IsRelativeParabolicSubgroup.of_etaleCover hG 𝒰
    intro a
    exact (w a).parabolic.of_range_eq (R.represents.baseChange (𝒰.f a)).1
      (hlocal a).symm
  let : Mono R.hom.hom.hom := R.represents.1
  let : Mono (subgroupIntersectionFst d R.hom).hom.hom :=
    (subgroupIntersection_isPullback d R.hom).mono_fst_of_mono
  have hI : SubgroupFunctor.range (subgroupIntersectionFst d R.hom) =
      SubgroupFunctor.range i' := by
    apply (SubgroupFunctor.range_eq_iff_baseChange_etaleCover 𝒰 _ _).mpr
    intro a
    rw [range_subgroupIntersectionFst_eq_comap, SubgroupFunctor.baseChange_comap,
      R.represents.2, SubgroupFunctor.CoverDescent.baseChange_subgroup 𝒰 F hF a,
      (w a).inverseImage, SubgroupFunctor.range_baseChangeHom]
  refine ⟨R.group, R.hom, hR, ?_⟩
  rw [← range_subgroupIntersectionFst_eq_comap, hI]

end CentralProductParabolic.RelativeExtension

namespace CentralProductParabolic

variable {D Z P' : GroupScheme S}

/-- Construct an ambient relative parabolic extending a supplied relative
parabolic of a reductive closed factor in a central product. -/
def relativeExtension (hG : IsReductive G) (hD : IsReductive D)
    (d : D ⟶ G) (hd : IsClosedSubgroup d) (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i' : P' ⟶ D) (hi' : IsRelativeParabolicSubgroup i') : RelativeExtension d i' := by
  apply Classical.choice
  let : Mono i'.hom.hom := hi'.mono
  obtain ⟨𝒰, h𝒰⟩ := relativeParabolicEtaleLocalDynamic S D P' i' hD hi'
  choose χ hχ using h𝒰
  exact ⟨RelativeExtension.ofEtaleCover 𝒰 (fun a =>
    RelativeExtension.ofDynamic (hG.baseChange (𝒰.f a))
      ((GroupScheme.baseChange (𝒰.f a)).map d) (hd.baseChange (𝒰.f a))
      ((GroupScheme.baseChange (𝒰.f a)).map i') (χ a) (hχ a).2)
        hG z hz hprod⟩

/-- Every relative parabolic of a reductive closed factor in a supplied
central product is an actual ambient intersection, with the corresponding
central isogeny onto the ambient parabolic. -/
theorem exists_relative_inverse (hG : IsReductive G) (hD : IsReductive D)
    (d : D ⟶ G) (hd : IsClosedSubgroup d) (z : Z ⟶ G) (hz : IsCentral z)
    (hprod : IsCentralIsogeny (prodHom z d (hz.commute_values _)))
    (i' : P' ⟶ D) (hi' : IsRelativeParabolicSubgroup i') :
    ∃ (P : GroupScheme S) (i : P ⟶ G) (e : Z ⊗ P' ⟶ P),
      IsRelativeParabolicSubgroup i ∧ IsCentralIsogeny e ∧
      e ≫ i = prodHom z (i' ≫ d) (hz.commute_values _) ∧
      SubgroupFunctor.range (subgroupIntersectionFst d i) = SubgroupFunctor.range i' := by
  let w := relativeExtension hG hD d hd z hz hprod i' hi'
  let : Mono i'.hom.hom := hi'.mono
  let : Mono w.inclusion.hom.hom := w.parabolic.mono
  obtain ⟨e, he, heq⟩ := exists_centralIsogeny_of_intersection_range_eq z hz d hprod
    w.inclusion (IsRelativeParabolicSubgroup.central_range_le hG w.inclusion w.parabolic z hz)
      i' w.intersection_range
  exact ⟨w.group, w.inclusion, e, w.parabolic, he, heq, w.intersection_range⟩

end CentralProductParabolic
end Langlands.GroupScheme
