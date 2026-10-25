import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Unequal-rank bilinear uniqueness for Whittaker-type coefficient models

The covariance is JPSS (2.11.2) and (2.11.4). The full Whittaker-type
uniqueness target is an internal extension needed for the scope of Theorem
2.7; the printed Proposition on p.399 assumes irreducible generic data.
This module states the extension and does not prove it.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

section FixedData

variable {F : Type uF} [Field F] [TopologicalSpace F] {n r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Membership in JPSS `U_(n+2,r+1)`, expressed inside the actual upper
unipotent group by requiring the leading `(n+2)`-square block to be identity.
For `n < r` these are precisely the matrices in (2.11.3) with `t = n+2`. -/
def IsUnequalRankCovarianceUnipotent (n : ℕ) (u : upperUnipotent (r + 1) F) : Prop :=
  ∀ i j : Fin (r + 1), i.val < n + 2 → j.val < n + 2 →
    u.val i j = if i = j then 1 else 0

/-- The two actual integral covariance laws (2.11.2) and (2.11.4).
The smaller general linear group acts through `diag(g,I_(r-n))`;
the unipotent condition uses exactly `U_(n+2,r+1)`. -/
def IsUnequalRankBilinearCovariant (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ)
    (s : ℂ)
    (B : (coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
      (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] ℂ) : Prop :=
  let ι := fun g : Langlands.GeneralLinear (n + 1) F =>
    GeneralLinear.reindex
      (finCongr (show n + (r - n) + 1 = r + 1 by omega))
      (appendIdentity n (r - n) g)
  (∀ (g : Langlands.GeneralLinear (n + 1) F)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule),
      B (modelRepresentation π ℓ (ι g) f) (modelRepresentation σ ℓ' g f') =
        determinantWeight abv g (((r - n : ℕ) : ℂ) / 2 - s) * B f f') ∧
  (∀ (u : upperUnipotent (r + 1) F),
    IsUnequalRankCovarianceUnipotent n u →
    ∀ (f : (coefficientModel π ℓ).toSubmodule)
      (f' : (coefficientModel σ ℓ').toSubmodule),
      B (modelRepresentation π ℓ u.val f) f' =
        (standardCharacter ψ r u : ℂ) * B f f')

end FixedData

/-- Full Whittaker-type unequal-rank bilinear uniqueness outside a finite
set of spectral values. This internal extension of the irreducible generic
Proposition in JPSS Section 2.11 remains a proof obligation. -/
def UnequalRankBilinearUniquenessStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) : Prop :=
  letI := T.topology
  ∀ hnr : n < r,
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsOfWhittakerType r (standardCharacter ψ r) π →
      IsOfWhittakerType n (inverseStandardCharacter ψ n) σ →
      ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
        let M := (coefficientModel π ℓ).toSubmodule
        let M' := (coefficientModel σ ℓ').toSubmodule
        ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
          ∀ B B' : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ,
            IsUnequalRankBilinearCovariant hnr ψ (normalizedAbsoluteValue T)
              π σ ℓ ℓ' s B →
            IsUnequalRankBilinearCovariant hnr ψ (normalizedAbsoluteValue T)
              π σ ℓ ℓ' s B' →
            B ≠ 0 → ∃ c : ℂ, B' = c • B

end Langlands.RankinSelberg
