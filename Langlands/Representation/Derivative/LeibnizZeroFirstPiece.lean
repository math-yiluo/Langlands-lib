import Langlands.Representation.Derivative.LeibnizPieceCompat

/-!
# The zero-first Leibniz grade

For a binary product `A × B` with `A` on `GL_(m+1)` and `B` on `GL_(n+1)`, the
Leibniz grade at the index `(0, d)` is naturally the binary product of `A` with the
order-`d` mirabolic derivative of the restriction of `B`, after the total rank cast.
-/

noncomputable section
open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The total output rank of the zero-first grade, `(m+1) + (n+1-d) = ((m+1)+(n+1)) - d`. -/
theorem leibnizZeroFirst_rank {m n d : ℕ} (hd : d ≤ n + 1) :
    (m + 1) + (n + 1 - d) = ((m + 1) + (n + 1)) - d := by
  omega

/-- Restricting the second factor to the mirabolic subgroup and taking its positive
order-`d` mirabolic derivative, then the binary product with the unchanged first
factor, the total rank cast in `SmoothRep` and forgetting smoothness, is naturally
the Leibniz grade at the zero-first index `(0, d)`. -/
def leibnizZeroFirstSmoothPieceIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ n + 1) :
    letI := T.topology
    (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
        (generalLinearRestriction.{uF, uV} T n) ⋙
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
        (mirabolicDerivativeOfOrder T ψ n d hd) ⋙
      T.binaryNormalizedProductFunctor (m + 1) (n + 1 - d) ⋙
      generalLinearRankCast T (leibnizZeroFirst_rank (m := m) hd.2) ⋙
      SmoothRep.toRep ≅
    leibnizPiece T ψ (m + 1) (n + 1) d (leibnizZeroFirstIndex m (n + 1) d hd.2) := by
  letI := T.topology
  exact Functor.isoWhiskerRight
    (NatIso.prod (Iso.refl (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))))
      (generalLinearRestrictionDerivativeIso.{uF, uV} T ψ n d hd))
    (T.binaryNormalizedProductFunctor (m + 1) (n + 1 - d) ⋙
      generalLinearRankCast T (leibnizZeroFirst_rank (m := m) hd.2) ⋙
      SmoothRep.toRep)

/-- The same comparison with the total rank cast applied in `Rep` after forgetting. -/
def leibnizZeroFirstPieceIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ n + 1) :
    letI := T.topology
    (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
        (generalLinearRestriction.{uF, uV} T n) ⋙
      (𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
        (mirabolicDerivativeOfOrder T ψ n d hd) ⋙
      T.binaryNormalizedProductFunctor (m + 1) (n + 1 - d) ⋙
      SmoothRep.toRep ⋙
      generalLinearRepRankCast.{uF, max uF uV} (F := F) (leibnizZeroFirst_rank (m := m) hd.2) ≅
    leibnizPiece T ψ (m + 1) (n + 1) d (leibnizZeroFirstIndex m (n + 1) d hd.2) := by
  letI := T.topology
  refine (eqToIso ?_) ≪≫ leibnizZeroFirstSmoothPieceIso T ψ m n d hd
  simp only [← generalLinearRankCast_toRep]

end Langlands.Derivative
