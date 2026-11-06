import Langlands.Automorphic.GroupSchemeQuotientL2FiniteApproximationStatement
import Langlands.Automorphic.GroupSchemeFullAEL2FiniteAverage

/-! # One finite-level approximation on the original quotient and full cusp L2 spaces -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- The same decreasing compact open basis gives actual convergent finite
averages on both original spaces, with their original inclusion and projections. -/
def GroupSchemeFullAEL2FiniteApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let S := fullAEL2CuspidalSubmodule F G hPD hG T i hi I e hc
    let ρA := haarQuotientL2FiniteRightAction F G T i hi I e hc
    let ρB := fullAEL2CuspidalFiniteRightAction F G hPD hG T i hi I e hc
    ∃ (K : ℕ → OpenSubgroup (FiniteAdelicGroupPoints F G))
      (hK : ∀ n, IsCompact (K n : Set (FiniteAdelicGroupPoints F G))),
      (𝓝 (1 : FiniteAdelicGroupPoints F G)).HasAntitoneBasis
        (fun n => (K n : Set (FiniteAdelicGroupPoints F G))) ∧
      let A := fun n =>
        letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
        haarQuotientL2FiniteAverage F G T i hi I e hc (K n)
      let B := fun n =>
        letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
        fullAEL2CuspidalFiniteAverage F G hPD hG T i hi I e hc (K n)
      (∀ n (φ : Lp ℂ 2 μQ),
        A n φ ∈ Langlands.fixedVectors ρA (K n).toSubgroup) ∧
      (∀ φ : Lp ℂ 2 μQ, Tendsto (fun n => A n φ) atTop (𝓝 φ)) ∧
      Dense {φ : Lp ℂ 2 μQ | Langlands.IsSmoothVector ρA φ} ∧
      (∀ n (ψ : S),
        B n ψ ∈ Langlands.fixedVectors ρB (K n).toSubgroup) ∧
      (∀ ψ : S, Tendsto (fun n => B n ψ) atTop (𝓝 ψ)) ∧
      Dense {ψ : S | Langlands.IsSmoothVector ρB ψ} ∧
      (∀ n (ψ : S), (B n ψ).val = A n ψ.val) ∧
      (∀ n (φ : Lp ℂ 2 μQ),
        fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc (A n φ) =
          B n (fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc φ)) ∧
      (∀ n (φ : Lp ℂ 2 μQ),
        fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc (A n φ) =
          A n (fullAEL2CuspidalAmbientProjection F G hPD hG T i hi I e hc φ))

end Langlands.Automorphic.GroupSchemeFunctions
