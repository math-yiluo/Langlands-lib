import Langlands.Automorphic.GroupSchemeRestrictionFullAEL2FiniteAverage

/-! # Finite-level approximation on `L²([G])` and its almost-everywhere cuspidal subspace -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

/-- One decreasing basis of compact open subgroups of the finite adelic points gives Haar
averages converging strongly to the identity on `L²([G])` and on its almost-everywhere cuspidal
subspace, compatibly with the inclusion and the orthogonal projections, and the smooth vectors
of both finite right actions are dense. -/
def QuotientFullAEL2FiniteApproximationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (hPD : ParabolicDynamicStatement.{0}) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
    (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (h : subgroup F G S j = imageSubgroup F T G i)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
    (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j)),
    let Sq := quotientFullAEL2CuspidalSubmodule F G hPD hG h hi hc hT
    let ρA := rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv'
    let ρB := quotientFullAEL2CuspidalFiniteRightAction F G hPD hG h hi hc hT hInv'
    ∃ (K : ℕ → OpenSubgroup (FiniteAdelicGroupPoints F G))
      (hK : ∀ n, IsCompact (K n : Set (FiniteAdelicGroupPoints F G))),
      (𝓝 (1 : FiniteAdelicGroupPoints F G)).HasAntitoneBasis
        (fun n => (K n : Set (FiniteAdelicGroupPoints F G))) ∧
      let A := fun n =>
        letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
        rationalQuotientL2FiniteAverage F G h hi hc hT hInv' (K n)
      let B := fun n =>
        letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
        quotientFullAEL2CuspidalFiniteAverage F G hPD hG h hi hc hT hInv' (K n)
      (∀ n (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)),
        A n φ ∈ Langlands.fixedVectors ρA (K n).toSubgroup) ∧
      (∀ φ : Lp ℂ 2 (quotientHaarMeasure F G S j), Tendsto (fun n => A n φ) atTop (𝓝 φ)) ∧
      Dense {φ : Lp ℂ 2 (quotientHaarMeasure F G S j) | Langlands.IsSmoothVector ρA φ} ∧
      (∀ n (ψ : Sq), B n ψ ∈ Langlands.fixedVectors ρB (K n).toSubgroup) ∧
      (∀ ψ : Sq, Tendsto (fun n => B n ψ) atTop (𝓝 ψ)) ∧
      Dense {ψ : Sq | Langlands.IsSmoothVector ρB ψ} ∧
      (∀ n (ψ : Sq), (B n ψ).val = A n ψ.val) ∧
      (∀ n (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)),
        quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT (A n φ) =
          B n (quotientFullAEL2CuspidalOrthogonalProjection F G hPD hG h hi hc hT φ)) ∧
      (∀ n (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)),
        quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT (A n φ) =
          A n (quotientFullAEL2CuspidalAmbientProjection F G hPD hG h hi hc hT φ))

end Langlands.Global.RestrictionSplitCentre
