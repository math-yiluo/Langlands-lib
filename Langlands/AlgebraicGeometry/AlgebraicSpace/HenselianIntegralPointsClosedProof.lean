import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianChartIntegralPointsClosedProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformFieldPointChartsProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsCompactProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.RelativeIntegralPoints

/-!
# Integral points over a henselian valuation ring: closedness

Conrad's Corollary 5.7, closedness, without Nagata compactification. Let `K` be a
nontrivially normed field whose closed unit ball is a henselian subring `O`, and `X` a separated
algebraic space over `Spec O`. Injectivity of `X(O) → X_K(K)` is the change-of-coefficients
injectivity for separated spaces. If `X` is of finite type, finitely many affine étale charts
`Uᵢ → X` carry all residue-field points of `X` (`UniformFieldPointChartsStatement`), so by
Hensel every `O`-point of `X` lifts to an `O`-point of some `Uᵢ`
(`HenselianIntegralPointsCompact.exists_point_of_residue_point`). The image of `X(O)` is the
finite union of the images of the `Uᵢ(O)`, each closed by
`HenselianChartIntegralPointsClosedStatement`.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- **Reduction of Conrad's Corollary 5.7, closedness.** The uniform field-point charts and the
closedness of the image of the integral points of one affine étale chart imply
`HenselianIntegralPointsClosedStatement`. -/
theorem henselianIntegralPointsClosed_of_charts (hF : UniformFieldPointChartsStatement.{u})
    (hC : HenselianChartIntegralPointsClosedStatement.{u}) :
    HenselianIntegralPointsClosedStatement.{u} := by
  intro K _ O hO hH X hXsep ι
  refine ⟨?_, fun hXft => ?_⟩
  · have hinj : Function.Injective (Algebra.ofId O K) := fun x y h => Subtype.ext h
    exact (baseChangeRingPointsEquiv O K K X).symm.injective.comp
      (RelativeIntegralPoints.changeRing_injective hXsep (Algebra.ofId O K) hinj)
  · have hXlft : LocallyOfFiniteTypeOverBase X := by
      obtain ⟨U, a, ha, hs, hU⟩ := hXft.exists_atlas
      exact ⟨U, a, ha, hs, hU.1⟩
    have hXqc : IsQuasiCompact X := by
      obtain ⟨U, a, ha, hs, hU⟩ := hXft.exists_atlas
      have : QuasiCompact U.hom := hU.2
      exact ⟨U, a, ha, hs, QuasiCompact.compactSpace_of_compactSpace U.hom⟩
    obtain ⟨n, U, f, hUf, hlift⟩ := hF O X hXsep hXqc
    let κ := IsLocalRing.ResidueField O
    let N : Fin n → Set (RingPoints K (baseChange (Spec.algebraMap O K) X) K) := fun i =>
      Set.range fun u : RingPoint O (U i) O => (baseChangeRingPointsEquiv O K K X).symm
        (RingPoints.changeRing (Algebra.ofId O K)
          (RingPoints.map (f i) ((schemeRingPointsEquiv O (U i) O).symm u)))
    have hrange : Set.range ι = ⋃ i, N i := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        obtain ⟨i, ū, hū⟩ := hlift κ (RingPoints.changeRing (Algebra.ofId O κ) x)
        obtain ⟨u, hu⟩ :=
          HenselianIntegralPointsCompact.exists_point_of_residue_point X x (f i) (hUf i).2 ū hū
        exact Set.mem_iUnion.2 ⟨i, u, by simp only [hu, ι]⟩
      · intro hy
        obtain ⟨i, u, rfl⟩ := Set.mem_iUnion.1 hy
        exact ⟨_, rfl⟩
    rw [hrange]
    let : TopologicalSpace (RingPoints K (baseChange (Spec.algebraMap O K) X) K) :=
      etaleChartTopology K (baseChange (Spec.algebraMap O K) X)
    exact isClosed_iUnion_of_finite fun i =>
      hC K O hO hH X hXsep hXlft (U i) (f i) (hUf i).1 (hUf i).2

/-- **Conrad's Corollary 5.7, closedness.** For a nontrivially normed field `K` whose closed unit
ball is a henselian subring `O`, and a separated algebraic space `X` over `Spec O`, the map
`X(O) → X_K(K)` is injective, and its image is closed for the étale-chart topology when `X` is
of finite type. -/
theorem henselianIntegralPointsClosed : HenselianIntegralPointsClosedStatement.{u} :=
  henselianIntegralPointsClosed_of_charts uniformFieldPointCharts henselianChartIntegralPointsClosed

end Langlands.AlgebraicGeometry.AlgebraicSpace
