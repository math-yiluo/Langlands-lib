import Langlands.Automorphic.GroupSchemeQuotientL2FiniteAverage

/-! # Finite-level approximation in the original quotient L2 space -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints
open Langlands.Global.PositiveRealTorus Langlands.GroupScheme Langlands.Analysis

/-- A decreasing compact open basis gives actual Haar averages converging on
every original quotient L2 vector, and the original finite smooth vectors are dense. -/
def GroupSchemeQuotientL2FiniteApproximationStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
    [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant],
    let μQ := positiveRationalQuotientHaarMeasure F G T i
    let ρf := haarQuotientL2FiniteRightAction F G T i hi I e hc
    ∃ (K : ℕ → OpenSubgroup (FiniteAdelicGroupPoints F G))
      (hK : ∀ n, IsCompact (K n : Set (FiniteAdelicGroupPoints F G))),
      (𝓝 (1 : FiniteAdelicGroupPoints F G)).HasAntitoneBasis
        (fun n => (K n : Set (FiniteAdelicGroupPoints F G))) ∧
      let A := fun n =>
        letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
        haarQuotientL2FiniteAverage F G T i hi I e hc (K n)
      (∀ n (φ : Lp ℂ 2 μQ),
        A n φ ∈ Langlands.fixedVectors ρf (K n).toSubgroup) ∧
      (∀ φ : Lp ℂ 2 μQ, Tendsto (fun n => A n φ) atTop (𝓝 φ)) ∧
      Dense {φ : Lp ℂ 2 μQ | Langlands.IsSmoothVector ρf φ}

end Langlands.Automorphic.GroupSchemeFunctions
