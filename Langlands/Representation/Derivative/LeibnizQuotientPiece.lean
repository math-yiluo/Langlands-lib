import Langlands.Representation.Derivative.LeibnizZeroFirstPiece
import Langlands.Representation.Derivative.MirabolicProductRestrictionStatement

/-!
# The differentiated restriction quotient as a Leibniz grade

The last term `A × (B|P)` of the mirabolic restriction sequence of a binary product,
followed by the order-`d` mirabolic derivative, the total rank cast and forgetting
smoothness, is compared with the zero-first Leibniz grade when `d ≤ n + 1`, given a
natural isomorphism of the shape of the left mixed-product derivative formula. For
`d > n + 1` its carriers vanish, given the matching vanishing of the left mixed
product's derivative.
-/

noncomputable section
open CategoryTheory

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

open MirabolicProductRestriction

/-- Given a natural isomorphism `E` of the shape of the left mixed-product derivative
formula for ranks `m + 1`, `n` and order `d`, the differentiated restriction quotient
is naturally the Leibniz grade at the zero-first index `(0, d)`. -/
def leibnizRestrictionQuotientPieceIso (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ n + 1)
    (E : letI := T.topology
      T.leftMixedProductFunctor.{uF, uV} (m + 1) n ⋙
          mirabolicDerivativeOfOrder T ψ ((m + 1) + n) d ⟨hd.1, by omega⟩ ⋙
            generalLinearRankCast T
              (show (m + 1) + n + 1 - d = (m + 1) + (n + 1 - d) by omega) ≅
        (𝟭 _).prod (mirabolicDerivativeOfOrder T ψ n d hd) ⋙
          T.binaryNormalizedProductFunctor (m + 1) (n + 1 - d)) :
    letI := T.topology
    restrictionQuotient.{uF, uV} T m n ⋙
        mirabolicDerivativeOfOrder T ψ (m + n + 1) d ⟨hd.1, by omega⟩ ⋙
          generalLinearRankCast T
            (show (m + n + 1) + 1 - d = ((m + 1) + (n + 1)) - d by omega) ⋙
            SmoothRep.toRep ≅
      leibnizPiece T ψ (m + 1) (n + 1) d (leibnizZeroFirstIndex m (n + 1) d hd.2) := by
  letI := T.topology
  have h1 : (m + 1) + n = m + n + 1 := by omega
  have e1 := mirabolicRankCastDerivativeIso.{uF, max uF uV} T ψ h1 d
    ⟨hd.1, by omega⟩ ⟨hd.1, by omega⟩
  have hcast :
      generalLinearRankCast.{uF, max uF uV} T (congrArg (fun r => r + 1 - d) h1) ⋙
          generalLinearRankCast T
            (show (m + n + 1) + 1 - d = ((m + 1) + (n + 1)) - d by omega) =
        generalLinearRankCast T
            (show (m + 1) + n + 1 - d = (m + 1) + (n + 1 - d) by omega) ⋙
          generalLinearRankCast T (leibnizZeroFirst_rank (m := m) hd.2) := by
    rw [generalLinearRankCast_trans, generalLinearRankCast_trans]
  refine Functor.isoWhiskerLeft
      ((𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
          (generalLinearRestriction.{uF, uV} T n) ⋙
        T.leftMixedProductFunctor.{uF, uV} (m + 1) n)
      (Functor.isoWhiskerRight e1
        (generalLinearRankCast T
            (show (m + n + 1) + 1 - d = ((m + 1) + (n + 1)) - d by omega) ⋙
          SmoothRep.toRep)) ≪≫ ?_
  refine Functor.isoWhiskerLeft
      ((𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
          (generalLinearRestriction.{uF, uV} T n) ⋙
        T.leftMixedProductFunctor.{uF, uV} (m + 1) n ⋙
          mirabolicDerivativeOfOrder T ψ ((m + 1) + n) d ⟨hd.1, by omega⟩)
      (Functor.isoWhiskerRight (eqToIso hcast) SmoothRep.toRep) ≪≫ ?_
  refine Functor.isoWhiskerLeft
      ((𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))).prod
          (generalLinearRestriction.{uF, uV} T n))
      (Functor.isoWhiskerRight E
        (generalLinearRankCast T (leibnizZeroFirst_rank (m := m) hd.2) ⋙
          SmoothRep.toRep)) ≪≫ ?_
  exact leibnizZeroFirstSmoothPieceIso T ψ m n d hd

/-- Every carrier of the differentiated restriction quotient is zero, given that the
order-`d` derivative of every left mixed product with ranks `m + 1`, `n` has zero
carrier. This is used above the second rank, `n + 1 < d`, where BZ77 4.14(a) gives
that vanishing. -/
theorem leibnizRestrictionQuotient_subsingleton (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (m n d : ℕ) (hd : 0 < d ∧ d ≤ (m + 1) + (n + 1))
    (V : letI := T.topology
      ∀ (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier))
        (B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic n F.Carrier)),
        Subsingleton ((mirabolicDerivativeOfOrder T ψ ((m + 1) + n) d
          ⟨hd.1, by omega⟩).obj ((T.leftMixedProductFunctor (m + 1) n).obj (A, B))))
    (X : letI := T.topology
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear (m + 1) F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)) :
    letI := T.topology
    Subsingleton ((restrictionQuotient.{uF, uV} T m n ⋙
        mirabolicDerivativeOfOrder T ψ (m + n + 1) d ⟨hd.1, by omega⟩ ⋙
          generalLinearRankCast T
            (show (m + n + 1) + 1 - d = ((m + 1) + (n + 1)) - d by omega) ⋙
            SmoothRep.toRep).obj X) := by
  let _ := T.topology
  have hMD : ∀ {a b : ℕ} (h : a = b) (ha : 0 < d ∧ d ≤ a + 1) (hb : 0 < d ∧ d ≤ b + 1)
      (Y : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear.mirabolic a F.Carrier)),
      Subsingleton ((mirabolicDerivativeOfOrder T ψ a d ha).obj Y) →
        Subsingleton ((mirabolicDerivativeOfOrder T ψ b d hb).obj
          ((mirabolicRankCast T h).obj Y)) := by
    intro a b h ha hb Y hY
    subst h
    exact hY
  have hGL : ∀ {a b : ℕ} (h : a = b)
      (Y : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier)),
      Subsingleton Y → Subsingleton ((generalLinearRankCast T h).obj Y) := by
    intro a b h Y hY
    subst h
    exact hY
  exact hGL _ _ (hMD (show (m + 1) + n = m + n + 1 by omega) _ _ _ (V X.1 _))

end Langlands.Derivative
