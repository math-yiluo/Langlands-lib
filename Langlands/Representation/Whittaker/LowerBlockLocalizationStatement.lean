import Langlands.Group.GL.LowerBlockLocalizationCoordinates
import Langlands.Representation.RankinSelberg.AnalyticStatement
import Langlands.Representation.RankinSelberg.LocalFactor

/-!
# JPSS arbitrarily small lower-block Whittaker localization

Statement of JPSS section 9.2, printed pages 454–455, in the actual
Whittaker coefficient image. The positive final block has size `c = c₀ + 1`.
-/

namespace Langlands.Whittaker

open Topology HarmonicAnalysis RankinSelberg GeneralLinear

universe uF uV

/-- For each actual Whittaker coefficient and each pair of neighborhoods, there
is another coefficient of the same representation whose restriction to the
actual lower-block chart is the original diagonal restriction times the two
compact open subgroup indicators. This definition states the lemma only. -/
def LowerBlockWhittakerLocalizationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (a d c₀ : ℕ),
      0 < a → 0 < d →
      let c := c₀ + 1
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (Langlands.GeneralLinear ((a + d) + c) F.Carrier) V),
        IsOfWhittakerType (a + d + c₀) (standardCharacter ψ (a + d + c₀)) π →
        ∀ W ∈ whittakerSet ψ (a + d + c₀) π,
          ∀ (Ux : Set (Matrix (Fin d) (Fin a) F.Carrier))
            (Uh : Set (lowerTriangularSubgroup d F.Carrier)),
            Ux ∈ 𝓝 (0 : Matrix (Fin d) (Fin a) F.Carrier) →
            Uh ∈ 𝓝 (1 : lowerTriangularSubgroup d F.Carrier) →
            ∃ Ω₁ : AddSubgroup (Matrix (Fin d) (Fin a) F.Carrier),
              ∃ Ω₂ : Subgroup (lowerTriangularSubgroup d F.Carrier),
                IsCompact (Ω₁ : Set (Matrix (Fin d) (Fin a) F.Carrier)) ∧
                IsOpen (Ω₁ : Set (Matrix (Fin d) (Fin a) F.Carrier)) ∧
                (Ω₁ : Set (Matrix (Fin d) (Fin a) F.Carrier)) ⊆ Ux ∧
                IsCompact (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ∧
                IsOpen (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ∧
                (Ω₂ : Set (lowerTriangularSubgroup d F.Carrier)) ⊆ Uh ∧
                ∃ W₀ ∈ whittakerSet ψ (a + d + c₀) π,
                  ∀ (g : Langlands.GeneralLinear a F.Carrier)
                    (x : Matrix (Fin d) (Fin a) F.Carrier)
                    (h : lowerTriangularSubgroup d F.Carrier),
                    (x ∈ Ω₁ ∧ h ∈ Ω₂ →
                      W₀.val (lowerBlockLocalization c g x h) =
                        W.val (lowerBlockLocalization c g 0 1)) ∧
                    (¬ (x ∈ Ω₁ ∧ h ∈ Ω₂) →
                      W₀.val (lowerBlockLocalization c g x h) = 0)

end Langlands.Whittaker
