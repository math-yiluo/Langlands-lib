import Langlands.Geometry.Analytic.DisjointAffinoidTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparison
import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalCharts

/-! # Actual affinoid atlases on induced rational spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

variable (X : ρ.OpenSubgroupTransport)

/-- The actual rational quotient, expressed as a positive-polyradius
presentation using the coefficient-preserving radius-one comparison. -/
def inducedChartAlgebra : PresentedAffinoidAlgebra K :=
  PresentedAffinoidAlgebra.ofStrict K X.domain.obj.algebra

/-- The comparison on actual quotient spectra is comap by a bounded
algebra equivalence, rather than an assumed chart homeomorphism. -/
def localAffinoidSpectrumHomeomorph :
    X.LocalSpectrum ≃ₜ BanachSpectrum X.inducedChartAlgebra :=
  PresentedAffinoidAlgebra.strictSpectrumHomeomorph K X.domain.obj.algebra

/-- One actual positive-polyradius quotient presentation for every coset. -/
def inducedAffinoidFamily :
    (G ⧸ X.subgroup.toSubgroup) → PresentedAffinoidAlgebra K :=
  fun _ => X.inducedChartAlgebra

/-- Apply the constructed quotient comparison to every topological summand. -/
def inducedAffinoidCopiesHomeomorph :
    DisjointAffinoidAtlas.Space X.inducedAffinoidFamily ≃ₜ X.InducedCosetCopies where
  toFun p := ⟨p.1, X.localAffinoidSpectrumHomeomorph.symm p.2⟩
  invFun p := ⟨p.1, X.localAffinoidSpectrumHomeomorph p.2⟩
  left_inv p := by
    rcases p with ⟨c, x⟩
    exact congrArg
      (fun y => (⟨c, y⟩ : DisjointAffinoidAtlas.Space X.inducedAffinoidFamily))
      (X.localAffinoidSpectrumHomeomorph.apply_symm_apply x)
  right_inv p := by
    rcases p with ⟨c, x⟩
    exact congrArg (fun y => (⟨c, y⟩ : X.InducedCosetCopies))
      (X.localAffinoidSpectrumHomeomorph.symm_apply_apply x)
  continuous_toFun := continuous_sigma fun _ =>
    continuous_sigmaMk.comp X.localAffinoidSpectrumHomeomorph.symm.continuous
  continuous_invFun := continuous_sigma fun _ =>
    continuous_sigmaMk.comp X.localAffinoidSpectrumHomeomorph.continuous

/-- The actual induced balanced quotient is the sum of these actual affinoid
spectra; the forward map uses the chosen coset representatives. -/
def inducedAffinoidHomeomorph :
    DisjointAffinoidAtlas.Space X.inducedAffinoidFamily ≃ₜ X.InducedSpectrum :=
  X.inducedAffinoidCopiesHomeomorph.trans X.inducedCosetHomeomorph

@[simp]
theorem inducedAffinoidHomeomorph_apply (c : G ⧸ X.subgroup.toSubgroup)
    (x : BanachSpectrum X.inducedChartAlgebra) :
    X.inducedAffinoidHomeomorph ⟨c, x⟩ =
      X.inducedChart c.out (X.localAffinoidSpectrumHomeomorph.symm x) := rfl

/-- An atlas on the actual induced rational spectrum, constructed from
quotient presentations, the radius-one comparison, and coset coordinates. -/
def inducedAffinoidAtlas : IndexedAffinoidAtlas.{u, max u v, v} K X.InducedSpectrum :=
  DisjointAffinoidAtlas.transportAtlas X.inducedAffinoidFamily X.inducedAffinoidHomeomorph

@[simp]
theorem inducedAffinoidAtlas_chart (c : X.inducedAffinoidAtlas.Index)
    (x : BanachSpectrum (X.inducedAffinoidAtlas.algebra c)) :
    X.inducedAffinoidAtlas.chart c x =
      X.inducedChart c.val.out (X.localAffinoidSpectrumHomeomorph.symm x) := rfl

/-- The constructed chart has precisely the original translated quotient
spectrum as its image, including the actual subspace topology. -/
theorem range_inducedAffinoidAtlas_chart (c : X.inducedAffinoidAtlas.Index) :
    Set.range (X.inducedAffinoidAtlas.chart c) = Set.range (X.inducedChart c.val.out) := by
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨X.localAffinoidSpectrumHomeomorph.symm x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨X.localAffinoidSpectrumHomeomorph x,
      congrArg (X.inducedChart c.val.out)
        (X.localAffinoidSpectrumHomeomorph.symm_apply_apply x)⟩

theorem range_inducedAffinoidAtlas_chart_eq_fiber (c : X.inducedAffinoidAtlas.Index) :
    Set.range (X.inducedAffinoidAtlas.chart c) = X.inducedComponent ⁻¹' {c.val} := by
  rw [X.range_inducedAffinoidAtlas_chart, X.range_inducedChart_eq_fiber,
    QuotientGroup.out_eq']

/-- Atlas chart indices identify distinct nonempty coset components. -/
theorem inducedAffinoidAtlas_index_eq_of_subset (c d : X.inducedAffinoidAtlas.Index)
    (h : Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart d)) : c = d :=
  DisjointAffinoidAtlas.transportChart_eq_of_subset _ _ c d h

/-- On contained components the actual bounded restriction is identity,
after transporting the chart index along its forced equality. -/
theorem inducedAffinoidAtlas_restriction_eq (c d : X.inducedAffinoidAtlas.Index)
    (h : Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart d)) :
    X.inducedAffinoidAtlas.restriction c d h =
      BoundedAlgHom.id K X.inducedChartAlgebra := by
  have hcd := X.inducedAffinoidAtlas_index_eq_of_subset c d h
  subst d
  rfl

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
