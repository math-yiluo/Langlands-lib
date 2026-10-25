import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Whittaker.GeneralLinear
import Langlands.Representation.Whittaker.InducedStatement

/-!
# Nonzero Whittaker functionals under normalized block induction

A proposition target derived from Rodier heredity, as recorded in JPSS (1983),
Section 2.3. The paired Markdown explains the normalization, character and
finite-type comparisons. This module does not prove or assume the target.
-/

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Generic positive-rank block factors yield a nonzero standard Whittaker
functional on their actual normalized upper block induction. No irreducibility
of the induced representation is asserted. -/
def NormalizedInheritanceStatement : Prop :=
  letI := T.topology
  ∀ (n : ℕ) (B : BlockShape (n + 1))
    (σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (ψ : UnitaryAdditiveCharacter F.Carrier),
    (∀ i, ∃ (m : ℕ) (h : B.size i = m + 1),
      IsGeneric ψ m (h ▸ σ i).representation) →
    HasFunctional (N := upperUnipotent (n + 1) F.Carrier)
      (θ := standardCharacter ψ n)
      ((T.normalizedProductInductionFunctor B).obj σ).representation

end Langlands.Whittaker
