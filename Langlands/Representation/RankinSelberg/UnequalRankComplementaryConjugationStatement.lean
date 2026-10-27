import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.UnequalRankSmearingUnipotent

/-!
# Complementary lower-row conjugation and translated-dual equivariance

The algebra behind the paired complementary-block transfer of JPSS 1983, §2.8,
for the large rank `r = n + ((j + 1) + k + 1)`, so the large group is
`GL_(r+1)`. With `a = blockWeylAt n r` (the unsigned block Weyl element
`diag(I_(n+1), w_(r-n))`), the complementary upper column
`U(z) = unequalRankSmearingUnipotent n k j z` (column `n + k + 2`, transported to
`GL_(r+1)` by `GeneralLinear.reindex` and `finCongr`) and the lower row
`L(x) = rectangularUnipotent (j + 1) k (Fin.snoc 0 x)` (row `n + j + 1`), the
inverse transpose of `a⁻¹ * U(z) * a` is `L(-z)`. Consequently the translated
first dual model equivalence intertwines right translation by `L(-z)` with right
translation by `U(z)`. This module only states these facts.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

/-- Derived algebraic interface for JPS 1979, Theorem 4.5, and JPSS 1983, §2.8.
Write `r = n + ((j + 1) + k + 1)`, `a = blockWeylAt n r`,
`U(z) = reindex (finCongr _) (unequalRankSmearingUnipotent n k j z)` and
`L(x) = rectangularUnipotent (j + 1) k (Fin.snoc 0 x)`.

1. Over every field and for all `n j k` and `z`,
   `inverseTranspose (r + 1) F (a⁻¹ * U(z) * a) = L(-z)`.
2. Over every field whose topology makes it a topological ring, for every
   unitary additive character `ψ`, complex
   representation `π` of `GL_(r+1)`, functional `ℓ : glFunctionals ψ r π`,
   coefficient `f` in the actual model, and `z`, with
   `D = translatedFirstDualModelEquiv ψ π ℓ a`,
   `D (L(-z) • f) = U(z) • D f`, the actions being the model representations
   of `π` and of `inverseTransposePullback π` with `firstDualFunctional ψ π ℓ`. -/
def UnequalRankComplementaryConjugationStatement : Prop :=
  (∀ (F : Type uF) [Field F] (n j k : ℕ) (z : Fin (n + 1) → F),
    inverseTranspose (n + ((j + 1) + k + 1) + 1) F
        ((blockWeylAt n (n + ((j + 1) + k + 1)) (by omega))⁻¹ *
          GeneralLinear.reindex
            (finCongr (show n + ((k + 1) + j + 1) + 1 = n + ((j + 1) + k + 1) + 1 by omega))
            (unequalRankSmearingUnipotent n k j z) *
          blockWeylAt n (n + ((j + 1) + k + 1)) (by omega)) =
      rectangularUnipotent (j + 1) k (Fin.snoc 0 (-z))) ∧
  (∀ (F : Type uF) [Field F] [TopologicalSpace F] [IsTopologicalRing F] (n j k : ℕ)
    (ψ : UnitaryAdditiveCharacter F) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear (n + ((j + 1) + k + 1) + 1) F) V)
    (ℓ : glFunctionals ψ (n + ((j + 1) + k + 1)) π)
    (f : (coefficientModel π ℓ).toSubmodule) (z : Fin (n + 1) → F),
    translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n (n + ((j + 1) + k + 1)) (by omega))
        (modelRepresentation π ℓ (rectangularUnipotent (j + 1) k (Fin.snoc 0 (-z))) f) =
      modelRepresentation (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)
        (GeneralLinear.reindex
          (finCongr (show n + ((k + 1) + j + 1) + 1 = n + ((j + 1) + k + 1) + 1 by omega))
          (unequalRankSmearingUnipotent n k j z))
        (translatedFirstDualModelEquiv ψ π ℓ
          (blockWeylAt n (n + ((j + 1) + k + 1)) (by omega)) f))

end Langlands.RankinSelberg
