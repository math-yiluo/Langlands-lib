import Langlands.Representation.Classification.TadicBlockReductionStatement
import Langlands.Representation.Classification.SupercuspidalSupport

/-! # Complementary products from support on one integral cuspidal line -/

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The unlinked-socle product theorem implies complementary-product
irreducibility for any positive-rank representation whose actual
supercuspidal support lies on one integral twist line. -/
def IntegralLineComplementaryIrreducibilityReduction : Prop :=
  UnlinkedSocleProductIrreducibility.{uF, uV} F T →
    letI := T.topology
    ∀ (n : ℕ) (hn : 0 < n)
      (S : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
      (s : Multiset (T.CuspidalDatum.{max uF uV, uF})),
      T.IsSupercuspidalSupport S s →
        ∀ ρ : T.CuspidalDatum.{max uF uV, uF},
          (∀ τ ∈ s, ∃ m : ℤ, τ = ρ.twist (m : ℝ)) →
            ∀ α ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2), α ≠ 0 →
              Representation.IsIrreducible
                (T.twistedProductInduced (BlockShape.uniform 2 n hn)
                  (fun _ => S) (fun i => if (i : ℕ) = 0 then α else -α)).representation

end Langlands.Classification
