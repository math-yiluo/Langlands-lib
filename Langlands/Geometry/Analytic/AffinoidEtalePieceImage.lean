import Langlands.Geometry.Analytic.AffinoidEtalePieceQuotient
import Langlands.Geometry.Analytic.EtaleCoverHomExt
import Langlands.Geometry.Analytic.LocalizedChartCoverLifts
import Langlands.Geometry.Analytic.LocalizedPullbackPoints
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteTensorComparison.Proof

/-! # Recognizing the image domain of an affinoid étale piece -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open _root_.CategoryTheory _root_.CategoryTheory.Limits Set
open SaturatedAtlasPresentation PresentedAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

local notation "M" => localizedAffinoidSpectrum (K := K)

private abbrev spectrumMap {A B : PresentedAffinoidAlgebra K} (f : BoundedAlgHom K A B) :
    M B ⟶ M A := SmallAffinoidSpectrum.localizedMapEquiv.{u, u} A B f

private theorem epi_of_surjective_etale {X Y : LocalizedCategory.{u, u, u} (K := K)} (g : X ⟶ Y)
    (he : etale g) (hs : Function.Surjective (localizedSpaceFunctor.map g)) : Epi g := by
  constructor
  intro Z f₁ f₂ h
  exact etaleCoverHomExt (fun _ : Unit => g) (fun _ => he)
    (fun x => ⟨(), hs x⟩) _ _ (fun _ => h)

private theorem spectrumMap_surjective {A B : PresentedAffinoidAlgebra K}
    (f : BoundedAlgHom K A B)
    (hs : Function.Surjective (BanachSpectrum.comap f.toBoundedRingHom)) :
    Function.Surjective (localizedSpaceFunctor.map (spectrumMap f)) := by
  intro x
  obtain ⟨z, rfl⟩ := (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} A).surjective x
  obtain ⟨y, hy⟩ := hs z
  exact ⟨SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} B y,
    (SmallAffinoidSpectrum.map_spectrumHomeomorph.{u, u} f y).trans
      (congrArg (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} A) hy)⟩

private theorem spectrumMap_etale {A B : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K A B)
    (hf : g.IsFiniteBanach) (he : g.AlgebraicallyFiniteEtale) : etale (spectrumMap g) :=
  SmallAffinoidSpectrum.map_etale_of_finite_pointwiseEtale.{u, u} g
    AffinoidPushout.finiteBanachPushout AffinoidPushout.finiteTensorComparison hf
    he.isEtaleAtPoint

private theorem epi_snd_of_pullback {X Y Z P : LocalizedCategory.{u, u, u} (K := K)}
    {f : X ⟶ Z} {g : Y ⟶ Z} {p : P ⟶ X} {q : P ⟶ Y} (h : IsPullback p q f g)
    (he : etale q) (hs : Function.Surjective (localizedSpaceFunctor.map f)) : Epi q := by
  apply epi_of_surjective_etale q he
  intro y
  obtain ⟨x, hx⟩ := hs (localizedSpaceFunctor.map g y)
  obtain ⟨z, -, hz⟩ := exists_point_of_isPullback _ _ _ _ h x y hx
  exact ⟨z, hz⟩

namespace AffinoidEtalePieceQuotient

variable {B : PresentedAffinoidAlgebra K} {Y : LocalizedCategory.{u, u, u} (K := K)}
  {a : localizedAffinoidSpectrum B ⟶ Y}
  (Q : AffinoidEtalePieceQuotient a)

/-- The quotient spectrum's map into the ambient space is monic. -/
theorem mono_map : Mono Q.map := by
  let π := spectrumMap Q.coverMap
  have hπ := spectrumMap_etale Q.coverMap Q.cover_finiteBanach Q.cover_finiteEtale
  have hπs := spectrumMap_surjective Q.coverMap Q.cover_surjective
  constructor
  intro T l r h
  obtain ⟨S, p, q, hp, hq⟩ := localizedEtalePullbackBaseChange π l hπ
  obtain ⟨S', p', q', hp', hq'⟩ := localizedEtalePullbackBaseChange π (q ≫ r) hπ
  let : Epi q := epi_snd_of_pullback hp hq hπs
  let : Epi q' := epi_snd_of_pullback hp' hq' hπs
  apply (cancel_epi q).mp
  apply (cancel_epi q').mp
  have hq'l : q' ≫ q ≫ l = (q' ≫ p) ≫ π := by
    rw [Category.assoc, hp.w]
  have hq'r : q' ≫ q ≫ r = p' ≫ π := hp'.w.symm
  have hpt : (q' ≫ p) ≫ a = p' ≫ a := by
    rw [← Q.cover_comp_map, ← Category.assoc, ← Category.assoc, ← hq'l, ← hq'r]
    simp only [Category.assoc, h]
  exact hq'l.trans ((Q.equalizes (q' ≫ p) p' hpt).trans hq'r.symm)

private theorem exists_lift_of_finite_chart
    {A : PresentedAffinoidAlgebra K} {T : LocalizedCategory.{u, u, u} (K := K)} (i : T ⟶ Y) [Mono i]
    (j : M Q.algebra ⟶ T) (hj : j ≫ i = Q.map)
    (b : M A ⟶ T)
    {C : PresentedAffinoidAlgebra K} (g : BoundedAlgHom K A C)
    (hf : g.IsFiniteBanach) (he : g.AlgebraicallyFiniteEtale)
    (hs : Function.Surjective (BanachSpectrum.comap g.toBoundedRingHom))
    (r : M C ⟶ M B) (hr : r ≫ a = spectrumMap g ≫ b ≫ i) :
    ∃ s : M A ⟶ M Q.algebra, s ≫ j = b := by
  let P₁ := spectrumMap (AffinoidPushout.leftMap g g)
  let P₂ := spectrumMap (AffinoidPushout.rightMap g g)
  have hpb := SmallAffinoidSpectrum.pushout_localized_isPullback.{u, u} g g
  have hComm : P₁ ≫ spectrumMap g = P₂ ≫ spectrumMap g := hpb.w
  have h₁ : (P₁ ≫ r) ≫ a = (P₂ ≫ r) ≫ a := by
    simp only [Category.assoc, hr]
    simpa only [Category.assoc] using congrArg (· ≫ b ≫ i) hComm
  have hmatch : P₁ ≫ r ≫ spectrumMap Q.coverMap = P₂ ≫ r ≫ spectrumMap Q.coverMap := by
    simpa only [Category.assoc] using Q.equalizes (P₁ ≫ r) (P₂ ≫ r) h₁
  obtain ⟨s, hFac, -⟩ := SmallAffinoidSpectrum.finiteAffinoidLocalizedHomDescent.{u, u} K
    g hf ((RingHom.Etale.iff_flat_and_formallyUnramified).mp he.2).1 hs
    (r ≫ spectrumMap Q.coverMap) hmatch
  have hFac' : spectrumMap g ≫ s = r ≫ spectrumMap Q.coverMap := hFac
  let : Epi (spectrumMap g) :=
    epi_of_surjective_etale _ (spectrumMap_etale g hf he) (spectrumMap_surjective g hs)
  refine ⟨s, (cancel_mono i).mp ((cancel_epi (spectrumMap g)).mp ?_)⟩
  change spectrumMap g ≫ (s ≫ j) ≫ i = spectrumMap g ≫ b ≫ i
  calc
    _ = (spectrumMap g ≫ s) ≫ Q.map := by simp only [Category.assoc, hj]
    _ = r ≫ a := by rw [hFac', Category.assoc, Q.cover_comp_map]
    _ = _ := hr

set_option backward.isDefEq.respectTransparency false in
/-- If every small chart of the proposed image has a finite étale surjective
affinoid test cover through the original piece, the quotient is isomorphic
to this image. -/
def isoOfFiniteChartCovers (T : SaturatedAtlasPresentation.{u, u, u} K)
    (i : localizationFunctor.obj T ⟶ Y) [Mono i]
    (j : M Q.algebra ⟶ localizationFunctor.obj T) (hj : j ≫ i = Q.map)
    (hCovers : ∀ k : T.presentation.atlas.Index,
      ∃ (C : PresentedAffinoidAlgebra K)
        (g : BoundedAlgHom K (T.presentation.atlas.algebra k) C) (r : M C ⟶ M B),
        g.IsFiniteBanach ∧ g.AlgebraicallyFiniteEtale ∧
          Function.Surjective (BanachSpectrum.comap g.toBoundedRingHom) ∧
          r ≫ a = spectrumMap g ≫ localizationFunctor.map (T.smallChartSpectrumInclusion k) ≫ i) :
    M Q.algebra ≅ localizationFunctor.obj T := by
  let : Mono Q.map := Q.mono_map
  let : Mono j := ⟨fun l r h => (cancel_mono Q.map).mp (by
    rw [← hj, ← Category.assoc, ← Category.assoc, h])⟩
  have hRefines : AtlasTopology.LocallyRefines
      (range fun k : T.presentation.atlas.Index => range (T.presentation.atlas.chart k)) {univ} := by
    intro W hW x _
    obtain rfl := mem_singleton_iff.mp hW
    obtain ⟨τ, hτ, hsub, hx, hn⟩ := T.presentation.atlas.isNet_chartFamily.1 x
    exact ⟨τ, hτ, hsub, fun S hS => ⟨subset_univ _, hx S hS⟩,
      by simpa only [nhdsWithin_univ] using hn⟩
  let hLift := exists_lift_of_chartCover (fun k : T.presentation.atlas.Index => k)
    hRefines j j (fun _ _ _ h _ => (cancel_mono j).mp h) (𝟙 _) (𝟙 _) (fun k => by
      obtain ⟨C, g, r, hf, he, hs, hr⟩ := hCovers k
      obtain ⟨s, h⟩ := Q.exists_lift_of_finite_chart i j hj
        (localizationFunctor.map (T.smallChartSpectrumInclusion k)) g hf he hs r hr
      simpa only [Category.comp_id] using Exists.intro s (And.intro h h))
  let l := hLift.choose
  have hl : l ≫ j = 𝟙 _ := hLift.choose_spec.1
  exact ⟨j, l, (cancel_mono j).mp (by rw [Category.assoc, hl, Category.comp_id, Category.id_comp]), hl⟩

end AffinoidEtalePieceQuotient

end Langlands.Analytic.SpaceAnalytification
