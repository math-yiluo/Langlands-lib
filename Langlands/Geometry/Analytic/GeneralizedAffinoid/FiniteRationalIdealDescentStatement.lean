import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteCoverIdealRefinement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteDomainIdealDescentStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainRelativeRationalRefinement

/-! # Reduction of full-domain ideal effectiveness to finite rational covers -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- An actual finite rational cover of the whole presented affinoid, retaining
the original rational quotient algebras and bounded structural maps. -/
def ofRationalCharts {n : ℕ} (D : Fin n → RationalChart K A)
    (hD : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    FiniteCover (Domain.whole K A) where
  size := n
  obj i := (D i).toDomain
  map i := ⟨(D i).baseMap, rfl⟩
  covers x _ := hD x

/-- Ideal effectiveness restricted to finite rational covers of a whole
affinoid, with actual full-domain intersections as the overlaps. -/
def RationalIdealEffectivenessStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (A : PresentedAffinoidAlgebra K) (n : ℕ) (D : Fin n → RationalChart K A)
    (hD : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus)
    (I : ∀ i : Fin n, Ideal (D i).algebra),
    (∀ i, IsClosed (I i : Set (D i).algebra)) →
      (ofRationalCharts D hD).IdealCompatible I →
        ∀ i, (D i).baseMap.closedIdealMap ((ofRationalCharts D hD).idealContraction I) = I i

/-- The rational theorem implies the unchanged full finite-domain target.
Refinement transports all compatible ideals and the explicit contraction. -/
theorem idealEffectiveness_of_rationalIdealEffectiveness
    (hR : RationalIdealEffectivenessStatement.{u}) : IdealEffectivenessStatement.{u} := by
  intro K _ _ _ A U c I _ hI
  let r := c.relativeRationalRefinement
  let d := r.toFiniteCover
  let ρ := r.toRefinement
  let J := ρ.idealFamily I
  have hJ : d.IdealCompatible J := ρ.idealFamily_compatible I hI
  apply ρ.ideal_effective_of_idealFamily_effective I hI
  have hJrat : (ofRationalCharts r.chart r.covers).IdealCompatible J := by
    intro i j
    exact hJ.on_test i j
      (U.extend ((r.chart i).toDomain.inter (r.chart j).toDomain))
      (U.extendFunctor.map ((r.chart i).toDomain.interLeft (r.chart j).toDomain))
      (U.extendFunctor.map ((r.chart i).toDomain.interRight (r.chart j).toDomain))
  have hclosed : ∀ j, IsClosed (J j : Set (d.obj j).algebra) :=
    fun j => (ρ.map j).restriction.isClosed_closedIdealMap _
  exact hR K U.algebra r.size r.chart r.covers J hclosed hJrat

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover
