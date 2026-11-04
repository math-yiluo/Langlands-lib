import Langlands.Geometry.Analytic.SaturatedAffinoidAtlas
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange

/-! # Actual domain closure of the constructed enlarged atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

namespace LocalDomain

variable {a}

/-- Extend any full domain in a local domain algebra to its actual original
chart, retaining its algebra and composing the original bounded maps. -/
def extend (U : LocalDomain a) (V : Domain K U.algebra) : LocalDomain a :=
  ⟨U.index, U.domain.extend V⟩

@[simp]
theorem extend_algebra (U : LocalDomain a) (V : Domain K U.algebra) :
    (U.extend V).algebra = V.algebra := rfl

theorem extend_locus (U : LocalDomain a) (V : Domain K U.algebra) :
    (U.extend V).locus = U.ambientMap '' V.locus := by
  change a.chart U.index '' (U.domain.extend V).locus = _
  rw [Domain.extend_locus, Set.image_image]
  rfl

theorem extend_ambientMap (U : LocalDomain a) (V : Domain K U.algebra)
    (x : BanachSpectrum V.algebra) :
    (U.extend V).ambientMap x = U.ambientMap (V.spectrumMap x) := rfl

/-- Actual full inverse-image quotients are local domains in the original
ambient atlas after extension through the original source representation. -/
def pullback {B : PresentedAffinoidAlgebra K} (U : LocalDomain a)
    (φ : BoundedAlgHom K B U.algebra) (V : Domain K B) : LocalDomain a :=
  U.extend (Domain.pullback φ V)

theorem pullback_locus {B : PresentedAffinoidAlgebra K} (U : LocalDomain a)
    (φ : BoundedAlgHom K B U.algebra) (V : Domain K B) :
    (U.pullback φ V).locus =
      U.ambientMap '' ((BanachSpectrum.comap φ.toBoundedRingHom) ⁻¹' V.locus) :=
  U.extend_locus (Domain.pullback φ V)

end LocalDomain

/-- Every full domain in a chart of the enlargement is an actual local domain
over an original chart, with exactly the same representing algebra. -/
def saturatedDomainToLocal (S : a.saturatedAtlas.Index)
    (V : Domain K (a.saturatedAtlas.algebra S)) : LocalDomain a :=
  (a.saturatedRepresentative S).extend V

@[simp]
theorem saturatedDomainToLocal_algebra (S : a.saturatedAtlas.Index)
    (V : Domain K (a.saturatedAtlas.algebra S)) :
    (a.saturatedDomainToLocal S V).algebra = V.algebra := rfl

theorem saturatedDomainToLocal_locus (S : a.saturatedAtlas.Index)
    (V : Domain K (a.saturatedAtlas.algebra S)) :
    (a.saturatedDomainToLocal S V).locus = a.saturatedAtlas.chart S '' V.locus :=
  (a.saturatedRepresentative S).extend_locus V

/-- Taking further local full domains adds no ambient subset to the
constructed enlargement. This is equality of entire families. -/
theorem localDomainFamily_saturatedAtlas :
    a.saturatedAtlas.localDomainFamily = a.localDomainFamily := by
  ext T
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨a.saturatedDomainToLocal U.index U.domain,
      a.saturatedDomainToLocal_locus U.index U.domain⟩
  · intro hT
    let S : a.saturatedAtlas.Index := ⟨T, hT⟩
    refine ⟨⟨S, Domain.whole K (a.saturatedAtlas.algebra S)⟩, ?_⟩
    exact Set.image_univ.trans (a.range_saturatedChart S)

/-- Every local full-domain subset is already an original chart domain. -/
def HasAllLocalDomains : Prop :=
  a.localDomainFamily = Set.range (fun i => Set.range (a.chart i))

theorem saturatedAtlas_hasAllLocalDomains : a.saturatedAtlas.HasAllLocalDomains :=
  a.localDomainFamily_saturatedAtlas.trans a.saturatedAtlas_chartFamily.symm

/-- In an atlas with all local domains, every actual local domain has an
original chart with exactly its ambient subset. -/
theorem HasAllLocalDomains.exists_chart {a : IndexedAffinoidAtlas.{u, v, w} K X}
    (ha : a.HasAllLocalDomains) (U : LocalDomain a) :
    ∃ i, Set.range (a.chart i) = U.locus := by
  have hU : U.locus ∈ a.localDomainFamily := ⟨U, rfl⟩
  rw [ha] at hU
  exact hU

end Langlands.Analytic.IndexedAffinoidAtlas
