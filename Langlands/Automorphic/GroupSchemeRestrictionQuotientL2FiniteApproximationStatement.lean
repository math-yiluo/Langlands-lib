import Langlands.Automorphic.GroupSchemeRestrictionQuotientL2FiniteAverage

/-! # Finite-level approximation in `L²([G])` -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Filter
open scoped CategoryTheory.MonObj Topology

namespace Langlands.Global.RestrictionSplitCentre

open Langlands.GroupScheme PositiveRealTorus Langlands.Automorphic.GroupSchemeFunctions

/-- A decreasing basis of compact open subgroups of the finite adelic points gives Haar averages
on `L²([G])` converging strongly to the identity, and the smooth vectors of the finite right
action are dense. -/
def QuotientL2FiniteApproximationStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of ℚ)))
    (j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (h : subgroup F G S j = imageSubgroup F T G i)
    (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex]
    (hc : IsCentral i) (hT : IsSplitTorus T.toGrp)
    [(Measure.haar : Measure (AdelicGroupPoints.normOneSubgroup F G)).IsMulRightInvariant]
    (hInv' : QuotientRightInvariant F G (quotientHaarMeasure F G S j)),
    let ρf := rationalQuotientL2FiniteRightAction F G (quotientHaarMeasure F G S j) hInv'
    ∃ (K : ℕ → OpenSubgroup (FiniteAdelicGroupPoints F G))
      (hK : ∀ n, IsCompact (K n : Set (FiniteAdelicGroupPoints F G))),
      (𝓝 (1 : FiniteAdelicGroupPoints F G)).HasAntitoneBasis
        (fun n => (K n : Set (FiniteAdelicGroupPoints F G))) ∧
      let A := fun n =>
        letI : CompactSpace (K n) := isCompact_iff_compactSpace.mp (hK n)
        rationalQuotientL2FiniteAverage F G h hi hc hT hInv' (K n)
      (∀ n (φ : Lp ℂ 2 (quotientHaarMeasure F G S j)),
        A n φ ∈ Langlands.fixedVectors ρf (K n).toSubgroup) ∧
      (∀ φ : Lp ℂ 2 (quotientHaarMeasure F G S j), Tendsto (fun n => A n φ) atTop (𝓝 φ)) ∧
      Dense {φ : Lp ℂ 2 (quotientHaarMeasure F G S j) | Langlands.IsSmoothVector ρf φ}

end Langlands.Global.RestrictionSplitCentre
