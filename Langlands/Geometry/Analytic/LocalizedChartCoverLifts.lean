import Langlands.Geometry.Analytic.FieldPointRepresentativeChartFactorization
import Langlands.Geometry.Analytic.QuotientDomainGluing
import Langlands.Geometry.Analytic.SaturatedTopChartComparison

/-! # Lifts on covers by actual small chart spectra -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits Set

namespace Langlands.Analytic.SaturatedAtlasPresentation

open IndexedAffinoidAtlas.OriginalChartDomain
open SourceCategory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : SaturatedAtlasPresentation.{u, v, v} K}

/-- The small spectrum of the original chart algebra is isomorphic to the
actual domain object of the chart. -/
def smallChartDomainIso (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) :
    A.smallChartSpectrum i ≅ A.originalDomain (ofChart i) :=
  smallSpectrumIso (A₀ := A.originalDomain (ofChart i))
    (A.presentation.chartTopIndex i) (A.presentation.chartTop_contains i)

omit [CompleteSpace K] in
private theorem eqToHom_eq_transport_id {R S : PresentedAffinoidAlgebra K} (e : R = S) :
    (eqToHom e : R ⟶ S) = (e ▸ BoundedAlgHom.id K R : BoundedAlgHom K R S) := by
  cases e
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The comparison with the domain object respects the small chart inclusion. -/
theorem smallChartDomainIso_hom_comp_inclusion (A : SaturatedAtlasPresentation.{u, v, v} K)
    (i : A.presentation.atlas.Index) :
    (A.smallChartDomainIso i).hom ≫ A.originalDomainInclusion (ofChart i) =
      A.smallChartSpectrumInclusion i := by
  let R := A.presentation.atlas.algebra i
  let : Small.{v} (BanachSpectrum R) := A.chartSpectrum_small i
  let c := SmallAffinoidSpectrum.globalIndex.{u, v} R
  have h : (smallChartDomainIso A i).hom =
      TopChartPresentation.ofTopPullback
        (A := (SmallAffinoidSpectrum.saturated R).globalChartPresentation c
          (SmallAffinoidSpectrum.globalRange R))
        (B := TopChartPresentation.ofChart A.presentation i)
        ((SmallAffinoidSpectrum.globalAlgebra R).symm ▸ BoundedAlgHom.id K R) := by
    unfold smallChartDomainIso smallSpectrumIso topChartIsoOfAlgebraEq ofTopAlgebraMap
    exact congrArg (TopChartPresentation.ofTopPullback
      (A := (SmallAffinoidSpectrum.saturated R).globalChartPresentation c
        (SmallAffinoidSpectrum.globalRange R))
      (B := TopChartPresentation.ofChart A.presentation i))
      (eqToHom_eq_transport_id (SmallAffinoidSpectrum.globalAlgebra R).symm)
  rw [h]
  rfl

private theorem comparison_map_domainInclusion (A : SaturatedAtlasPresentation.{u, v, v} K)
    (D : A.presentation.atlas.OriginalChartDomain) :
    comparisonFunctor.map (SourceCategory.domainInclusion A D) =
      localizationFunctor.map (A.originalDomainInclusion D) :=
  sourceHomEquiv.apply_symm_apply _

private theorem localized_eq_of_domainCover
    {B : SaturatedAtlasPresentation.{u, v, v} K} {ι : Type w}
    (D : ι → A.presentation.atlas.OriginalChartDomain)
    (hD : AtlasTopology.LocallyRefines (range (fun k => (D k).carrier)) {univ})
    (f g : localizationFunctor.obj A ⟶ localizationFunctor.obj B)
    (h : ∀ k, localizationFunctor.map (A.originalDomainInclusion (D k)) ≫ f =
        localizationFunctor.map (A.originalDomainInclusion (D k)) ≫ g) :
    f = g := by
  let f' : ofPresentation A ⟶ ofPresentation B := sourceHomEquiv.symm f
  let g' : ofPresentation A ⟶ ofPresentation B := sourceHomEquiv.symm g
  have hf : comparisonFunctor.map f' = f := sourceHomEquiv.apply_symm_apply f
  have hg : comparisonFunctor.map g' = g := sourceHomEquiv.apply_symm_apply g
  have heq : f' = g' := eq_of_domainCover D hD f' g' (fun k => by
    apply comparisonFunctor.map_injective
    rw [Functor.map_comp, Functor.map_comp, hf, hg, comparison_map_domainInclusion]
    exact h k)
  exact hf.symm.trans ((congrArg comparisonFunctor.map heq).trans hg)

/-- A cover by small spectra of charts detects equality of localized maps. -/
theorem localizedHom_ext_of_chartCover {ι : Type w}
    (i : ι → A.presentation.atlas.Index)
    (hi : AtlasTopology.LocallyRefines
      (range (fun k => range (A.presentation.atlas.chart (i k)))) {univ})
    {Y : LocalizedCategory.{u, v, v} (K := K)}
    (f g : localizationFunctor.obj A ⟶ Y)
    (h : ∀ k, localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) ≫ f =
        localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) ≫ g) :
    f = g := by
  obtain ⟨B, hB⟩ := localizedObjectEquiv.surjective Y
  change localizationFunctor.obj B = Y at hB
  subst Y
  apply localized_eq_of_domainCover (fun k => ofChart (i k)) hi f g
  intro k
  let e := localizationFunctor.mapIso (A.smallChartDomainIso (i k))
  apply (cancel_epi e.hom).mp
  change localizationFunctor.map (A.smallChartDomainIso (i k)).hom ≫
      (localizationFunctor.map (A.originalDomainInclusion (ofChart (i k))) ≫ f) =
    localizationFunctor.map (A.smallChartDomainIso (i k)).hom ≫
      (localizationFunctor.map (A.originalDomainInclusion (ofChart (i k))) ≫ g)
  rw [← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    smallChartDomainIso_hom_comp_inclusion]
  exact h k

/-- For jointly monic projections, local lifts on a quasinet of small chart
spectra glue to a lift in the localized category. -/
theorem exists_lift_of_chartCover {ι : Type w}
    (i : ι → A.presentation.atlas.Index)
    (hi : AtlasTopology.LocallyRefines
      (range (fun k => range (A.presentation.atlas.chart (i k)))) {univ})
    {V Y Z : LocalizedCategory.{u, v, v} (K := K)}
    (p : V ⟶ Y) (q : V ⟶ Z)
    (hmono : ∀ (T : LocalizedCategory.{u, v, v} (K := K)) (f g : T ⟶ V),
      f ≫ p = g ≫ p → f ≫ q = g ≫ q → f = g)
    (a : localizationFunctor.obj A ⟶ Y) (b : localizationFunctor.obj A ⟶ Z)
    (hlocal : ∀ k, ∃ l : localizationFunctor.obj (A.smallChartSpectrum (i k)) ⟶ V,
      l ≫ p = localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) ≫ a ∧
      l ≫ q = localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) ≫ b) :
    ∃ l : localizationFunctor.obj A ⟶ V, l ≫ p = a ∧ l ≫ q = b := by
  classical
  obtain ⟨V₀, hV⟩ := localizedObjectEquiv.surjective V
  obtain ⟨Y₀, hY⟩ := localizedObjectEquiv.surjective Y
  obtain ⟨Z₀, hZ⟩ := localizedObjectEquiv.surjective Z
  change localizationFunctor.obj V₀ = V at hV
  change localizationFunctor.obj Y₀ = Y at hY
  change localizationFunctor.obj Z₀ = Z at hZ
  subst V Y Z
  choose l hl₁ hl₂ using hlocal
  let D := fun k => ofChart (i k)
  let e := fun k => localizationFunctor.mapIso (A.smallChartDomainIso (i k))
  let δ := fun k => (e k).inv ≫ l k
  have hd (k : ι) :
      (e k).inv ≫ localizationFunctor.map (A.smallChartSpectrumInclusion (i k)) =
        localizationFunctor.map (A.originalDomainInclusion (D k)) := by
    rw [← smallChartDomainIso_hom_comp_inclusion, Functor.map_comp]
    change (e k).inv ≫ (e k).hom ≫ _ = _
    rw [Iso.inv_hom_id_assoc]
  have hδ₁ (k : ι) : δ k ≫ p = localizationFunctor.map (A.originalDomainInclusion (D k)) ≫ a := by
    dsimp only [δ]
    rw [Category.assoc, hl₁, ← Category.assoc, hd]
  have hδ₂ (k : ι) : δ k ≫ q = localizationFunctor.map (A.originalDomainInclusion (D k)) ≫ b := by
    dsimp only [δ]
    rw [Category.assoc, hl₂, ← Category.assoc, hd]
  let nested {S T : A.presentation.atlas.OriginalChartDomain} (hST : S ≤ T) :
      localizationFunctor.obj (A.originalDomain S) ⟶ localizationFunctor.obj (A.originalDomain T) :=
    comparisonFunctor.map (domainMap hST)
  have hnested {S T : A.presentation.atlas.OriginalChartDomain} (hST : S ≤ T) :
      nested hST ≫ localizationFunctor.map (A.originalDomainInclusion T) =
        localizationFunctor.map (A.originalDomainInclusion S) := by
    have h := (Functor.map_comp comparisonFunctor (domainMap hST)
      (SourceCategory.domainInclusion A T)).symm.trans
        (congrArg comparisonFunctor.map (domainMap_inclusion hST))
    exact (congrArg (nested hST ≫ ·) (comparison_map_domainInclusion A T).symm).trans
      (h.trans (comparison_map_domainInclusion A S))
  have hrestrict {S : A.presentation.atlas.OriginalChartDomain} {k : ι} (hS : S ≤ D k)
      {U : LocalizedCategory.{u, v, v} (K := K)} (r : localizationFunctor.obj V₀ ⟶ U)
      (c : localizationFunctor.obj A ⟶ U)
      (hr : δ k ≫ r = localizationFunctor.map (A.originalDomainInclusion (D k)) ≫ c) :
      (nested hS ≫ δ k) ≫ r =
        localizationFunctor.map (A.originalDomainInclusion S) ≫ c := by
    calc
      _ = nested hS ≫ (δ k ≫ r) := Category.assoc _ _ _
      _ = nested hS ≫ (localizationFunctor.map (A.originalDomainInclusion (D k)) ≫ c) :=
        congrArg (nested hS ≫ ·) hr
      _ = _ := (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c) (hnested hS))
  let localMap (k : ι) : ofPresentation (A.originalDomain (D k)) ⟶ ofPresentation V₀ :=
    sourceHomEquiv.symm (δ k)
  have hlocalMap (k : ι) : comparisonFunctor.map (localMap k) = δ k :=
    sourceHomEquiv.apply_symm_apply _
  let family : QuotientDomainMatchingFamily A V₀ D :=
    { localMap := localMap
      overlap := fun k j => by
        apply comparisonFunctor.map_injective
        rw [Functor.map_comp, Functor.map_comp, hlocalMap, hlocalMap]
        change nested (inf_le_left : D k ⊓ D j ≤ D k) ≫ δ k =
          nested (inf_le_right : D k ⊓ D j ≤ D j) ≫ δ j
        exact hmono _ _ _
          ((hrestrict inf_le_left p a (hδ₁ k)).trans (hrestrict inf_le_right p a (hδ₁ j)).symm)
          ((hrestrict inf_le_left q b (hδ₂ k)).trans (hrestrict inf_le_right q b (hδ₂ j)).symm) }
  let L : localizationFunctor.obj A ⟶ localizationFunctor.obj V₀ :=
    comparisonFunctor.map (family.glue hi)
  have hL (k : ι) : localizationFunctor.map (A.originalDomainInclusion (D k)) ≫ L = δ k := by
    have h := congrArg comparisonFunctor.map (family.glue_restrict hi k)
    rw [Functor.map_comp, comparison_map_domainInclusion] at h
    exact h.trans (hlocalMap k)
  refine ⟨L, localized_eq_of_domainCover D hi _ _ (fun k => ?_),
    localized_eq_of_domainCover D hi _ _ (fun k => ?_)⟩
  · rw [← Category.assoc, hL, hδ₁]
  · rw [← Category.assoc, hL, hδ₂]

end Langlands.Analytic.SaturatedAtlasPresentation
