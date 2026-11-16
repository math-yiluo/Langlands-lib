import Langlands.Geometry.Analytic.AnalyticFibreProduct
import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover
import Langlands.Geometry.Analytic.LocalActionLifts

/-! # Finite chart covers and compactness of constructed fibre products -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FibreProduct

open Set CategoryTheory
open AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-- A finite family of actual pair charts covering the glued space. -/
structure FinitePairCover where
  pairs : Set (PairIndex f g)
  finite : pairs.Finite
  covers : (⋃ p ∈ pairs, range ((chartSystem f g).chart p)) = univ

/-- Compact factors have a finite cover of their glued fibre product by pair
charts, using the published finite-pair decomposition over each pair of charts. -/
theorem nonempty_finitePairCover [CompactSpace A.space] [CompactSpace B.space]
    [T2Space C.space] (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) : Nonempty (FinitePairCover f g) := by
  classical
  obtain ⟨σ, hσ, hσa, hσcov⟩ :=
    A.atlas.isNet_chartFamily.1.exists_finite_cover_of_isCompact isCompact_univ
  obtain ⟨τ, hτ, hτb, hτcov⟩ :=
    B.atlas.isNet_chartFamily.1.exists_finite_cover_of_isCompact isCompact_univ
  let : Finite σ := hσ.to_subtype
  let : Finite τ := hτ.to_subtype
  have ha : ∀ V : σ, ∃ i, range (A.atlas.chart i) = V.val := fun V => hσa V.property
  have hb : ∀ W : τ, ∃ j, range (B.atlas.chart j) = W.val := fun W => hτb W.property
  choose a ha using ha
  choose b hb using hb
  choose Q hQ hQsub hQeq using fun (V : σ) (W : τ) =>
    exists_finite_pairs f g hA hB (a V) (b W)
  refine ⟨{
    pairs := ⋃ V : σ, ⋃ W : τ, Q V W
    finite := finite_iUnion fun V => finite_iUnion fun W => hQ V W
    covers := ?_
  }⟩
  apply eq_univ_of_forall
  intro z
  obtain ⟨V, hVσ, hzV⟩ := hσcov (mem_univ (fst f g z))
  obtain ⟨W, hWτ, hzW⟩ := hτcov (mem_univ (snd f g z))
  have hz : z ∈ fst f g ⁻¹' range (A.atlas.chart (a ⟨V, hVσ⟩)) ∩
      snd f g ⁻¹' range (B.atlas.chart (b ⟨W, hWτ⟩)) := by
    rw [ha, hb]
    exact ⟨hzV, hzW⟩
  rw [hQeq] at hz
  obtain ⟨p, hpQ, hzp⟩ := mem_iUnion₂.mp hz
  exact mem_iUnion₂.mpr ⟨p, mem_iUnion.mpr ⟨⟨V, hVσ⟩,
    mem_iUnion.mpr ⟨⟨W, hWτ⟩, hpQ⟩⟩, hzp⟩

/-- A chosen finite cover of the glued space by its actual pair charts. -/
def finitePairCover [CompactSpace A.space] [CompactSpace B.space]
    [T2Space C.space] (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) : FinitePairCover f g :=
  Classical.choice (nonempty_finitePairCover f g hA hB)

/-- Any finite pair-chart cover makes the glued space compact. -/
theorem FinitePairCover.compactSpace (c : FinitePairCover f g) :
    CompactSpace (chartSystem f g).Space := by
  constructor
  rw [← c.covers]
  exact c.finite.isCompact_biUnion fun p _ =>
    isCompact_range ((chartSystem f g).continuous_chart p)

/-- The constructed glued fibre product of compact factors is compact. -/
theorem compactSpace [CompactSpace A.space] [CompactSpace B.space]
    [T2Space C.space] (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) : CompactSpace (chartSystem f g).Space :=
  (finitePairCover f g hA hB).compactSpace f g

end Langlands.Analytic.FibreProduct

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y S : SaturatedAtlasPresentation.{u, u, u} K}
  [T2Space X.presentation.space] [T2Space Y.presentation.space]
  [T2Space S.presentation.space]
  (f : X ⟶ S) (g : Y ⟶ S)

/-- Compactness of the constructed fibre product of saturated presentations. -/
theorem compactSpace_fibreProduct [CompactSpace X.presentation.space]
    [CompactSpace Y.presentation.space] : CompactSpace (fibreProduct f g).presentation.space :=
  FibreProduct.compactSpace (compatibleMap f) (compatibleMap g)
    X.hasAllLocalDomains Y.hasAllLocalDomains

/-- The constructed fibre product, viewed as an analytic space, is compact
and Hausdorff when its factors are compact and its base is Hausdorff. -/
theorem isCompactSpace_localization_fibreProduct [CompactSpace X.presentation.space]
    [CompactSpace Y.presentation.space] :
    IsCompactSpace (localizationFunctor.obj (fibreProduct f g)) := by
  rw [IsCompactSpace, ← Functor.comp_obj,
    localizationFunctor_localizedSpaceFunctor]
  exact ⟨compactSpace_fibreProduct f g,
    FibreProduct.t2Space (compatibleMap f) (compatibleMap g)
      X.hasAllLocalDomains Y.hasAllLocalDomains⟩

end Langlands.Analytic.SaturatedAtlasPresentation
