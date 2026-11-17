import Langlands.Geometry.Analytic.FibreProductLocalAtlas
import Langlands.Geometry.Analytic.AtlasReindexing
import Langlands.Geometry.Analytic.AtlasHomeomorph
import Mathlib.Topology.Instances.Shrink
import Mathlib.Logic.Small.Basic

/-! # Same-universe atlases from a small spectrum cover -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidChartSystem

/-- A small-indexed pointwise cover by small spectra makes the actual full
gluing quotient small. No topology or local-cover premise is required. -/
theorem small_space_of_small_charts (D : AffinoidChartSystem.{u, w} K) [Small.{v} D.Index]
    (hcover : ∀ z : D.Space, ∃ i : D.Index, Small.{v} (BanachSpectrum (D.algebra i)) ∧
      z ∈ range (D.chart i)) : Small.{v} D.Space := by
  let S : Set D.Index := {i | Small.{v} (BanachSpectrum (D.algebra i))}
  let : ∀ i : S, Small.{v} (BanachSpectrum (D.algebra i.val)) := fun i => i.property
  apply small_of_surjective (f := fun p : Σ i : S, BanachSpectrum (D.algebra i.val) =>
    D.chart p.1.val p.2)
  intro z
  obtain ⟨i, hi, s, hs⟩ := hcover z
  exact ⟨⟨⟨i, hi⟩, s⟩, hs⟩

end AffinoidChartSystem

namespace FibreProduct

open AffinoidAtlasPresentation

variable {A B C : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-- A small quotient has a small set of distinct good chart domains. -/
instance small_localAtlasIndex [Small.{v} (chartSystem f g).Space] :
    Small.{v} (LocalAtlasIndex f g) := by
  change Small.{v} {T : Set (chartSystem f g).Space // T ∈ goodChartFamily f g}
  infer_instance

/-- Shrink the already constructed atlas in both its space and index
universes. All original algebras and entire bounded restrictions are kept. -/
def smallAtlas [Small.{v} (chartSystem f g).Space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) :
    IndexedAffinoidAtlas.{u, v, v} K (Shrink.{v} (chartSystem f g).Space) :=
  ((localAtlas f g hA hB hC).transport (Shrink.homeomorph (chartSystem f g).Space)).reindex
    (equivShrink (LocalAtlasIndex f g)).symm

/-- The actual same-universe analytic atlas presentation. The smallness
premise is explicit and may be supplied by a small spectrum cover. -/
def smallPresentation [Small.{v} (chartSystem f g).Space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) : AffinoidAtlasPresentation.{u, v, v} K where
  space := TopCat.of (Shrink.{v} (chartSystem f g).Space)
  atlas := smallAtlas f g hA hB hC

/-- The canonical homeomorphism retains every original quotient point. -/
def smallSpaceHomeomorph [Small.{v} (chartSystem f g).Space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) :
    (chartSystem f g).Space ≃ₜ (smallPresentation f g hA hB hC).space :=
  Shrink.homeomorph (chartSystem f g).Space

end FibreProduct

end Langlands.Analytic
