import Langlands.Representation.RankinSelberg.EqualRankSwapTransport
import Langlands.Representation.RankinSelberg.WhittakerRankCast
import Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof

/-! # Actual coefficient recasting for the intermediate tail comparison -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear Whittaker HarmonicAnalysis

universe uF uV

section Characters

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F) {n : ℕ}

/-- An inverse coefficient has standard covariance for the scaled character.
Its underlying function is retained exactly. -/
def inverseAsScaledStandard (W : InverseWhittakerFunctions ψ n) :
    WhittakerFunctions (ψ.scale (-1)) n :=
  ⟨W.val, by
    simpa only [WhittakerFunctions, InverseWhittakerFunctions,
      standardCharacter_scale_neg_one] using W.property⟩

/-- Standard covariance for the scaled character is inverse covariance for the
original character, with the same underlying function. -/
def scaledStandardAsInverse (W : WhittakerFunctions (ψ.scale (-1)) n) :
    InverseWhittakerFunctions ψ n :=
  ⟨W.val, by
    simpa only [WhittakerFunctions, InverseWhittakerFunctions,
      standardCharacter_scale_neg_one] using W.property⟩

/-- Inverse covariance for the scaled character is standard covariance for the
original character, with the same underlying function. -/
def scaledInverseAsStandard (W : InverseWhittakerFunctions (ψ.scale (-1)) n) :
    WhittakerFunctions ψ n :=
  ⟨W.val, by
    simpa only [WhittakerFunctions, InverseWhittakerFunctions,
      inverseStandardCharacter_scale_neg_one] using W.property⟩

/-- Standard covariance is inverse covariance for the scaled character,
with the same underlying function. -/
def standardAsScaledInverse (W : WhittakerFunctions ψ n) :
    InverseWhittakerFunctions (ψ.scale (-1)) n :=
  ⟨W.val, by
    simpa only [WhittakerFunctions, InverseWhittakerFunctions,
      inverseStandardCharacter_scale_neg_one] using W.property⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Recasting preserves actual coefficient-image membership; the functional is
transported along equality of the two matrix characters. -/
theorem inverseAsScaledStandard_mem {W : InverseWhittakerFunctions ψ n}
    (hW : W ∈ inverseWhittakerSet ψ n π) :
    inverseAsScaledStandard ψ W ∈ whittakerSet (ψ.scale (-1)) n π := by
  obtain ⟨ℓ, v, rfl⟩ := hW
  let ℓ' : glFunctionals (ψ.scale (-1)) n π :=
    functionalsCongr (standardCharacter_scale_neg_one ψ n).symm ℓ
  exact ⟨ℓ', v, Subtype.ext rfl⟩

/-- A scaled-standard actual coefficient supplies the actual inverse coefficient
of the same representation needed on the full test side. -/
theorem scaledStandardAsInverse_mem
    {W : WhittakerFunctions (ψ.scale (-1)) n}
    (hW : W ∈ whittakerSet (ψ.scale (-1)) n π) :
    scaledStandardAsInverse ψ W ∈ inverseWhittakerSet ψ n π := by
  obtain ⟨ℓ, v, rfl⟩ := hW
  let ℓ' : glInverseFunctionals ψ n π :=
    functionalsCongr (standardCharacter_scale_neg_one ψ n) ℓ
  exact ⟨ℓ', v, Subtype.ext rfl⟩

/-- A scaled-inverse actual tail coefficient supplies an actual standard
coefficient of the same tail representation. -/
theorem scaledInverseAsStandard_mem
    {W : InverseWhittakerFunctions (ψ.scale (-1)) n}
    (hW : W ∈ inverseWhittakerSet (ψ.scale (-1)) n π) :
    scaledInverseAsStandard ψ W ∈ whittakerSet ψ n π := by
  obtain ⟨ℓ, v, rfl⟩ := hW
  let ℓ' : glFunctionals ψ n π :=
    functionalsCongr (inverseStandardCharacter_scale_neg_one ψ n) ℓ
  exact ⟨ℓ', v, Subtype.ext rfl⟩

/-- The same standard coefficient is an actual inverse coefficient at the
scaled character, using the transported functional and the same vector. -/
theorem standardAsScaledInverse_mem {W : WhittakerFunctions ψ n}
    (hW : W ∈ whittakerSet ψ n π) :
    standardAsScaledInverse ψ W ∈ inverseWhittakerSet (ψ.scale (-1)) n π := by
  obtain ⟨ℓ, v, rfl⟩ := hW
  let ℓ' : glInverseFunctionals (ψ.scale (-1)) n π :=
    functionalsCongr (inverseStandardCharacter_scale_neg_one ψ n).symm ℓ
  exact ⟨ℓ', v, Subtype.ext rfl⟩

end Characters

section RankTransport

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable (ψ : UnitaryAdditiveCharacter F) {m n : ℕ}

/-- Equality transport for inverse coefficients likewise retains the actual
function after the corresponding numerical matrix reindexing. -/
def inverseWhittakerRankCast (h : m = n) (W : InverseWhittakerFunctions ψ m) :
    InverseWhittakerFunctions ψ n :=
  h ▸ W

theorem inverseWhittakerRankCast_apply (h : m = n)
    (W : InverseWhittakerFunctions ψ m)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (inverseWhittakerRankCast ψ h W).val g =
      W.val (reindex (finCongr (congrArg (· + 1) h.symm)) g) := by
  subst n
  have hg : reindex (finCongr (rfl : m + 1 = m + 1)) g = g := by
    apply Units.ext
    rfl
  simp only [inverseWhittakerRankCast, hg]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Smoothness is unchanged by an equality transport of the matrix rank. -/
theorem representationRankCast_isSmooth (h : m = n)
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    (hπ : IsSmooth π) : IsSmooth (h ▸ π) := by
  subst n
  exact hπ

/-- Equality transport changes only the representation's asserted rank.
The coefficient still belongs to its actual coefficient image. -/
theorem whittakerRankCast_mem (h : m = n)
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    {W : WhittakerFunctions ψ m} (hW : W ∈ whittakerSet ψ m π) :
    whittakerRankCast ψ h W ∈ whittakerSet ψ n (h ▸ π) := by
  subst n
  exact hW

/-- Rank transport preserves membership in the inverse coefficient image of
the equally transported representation. -/
theorem inverseWhittakerRankCast_mem (h : m = n)
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F) V)
    {W : InverseWhittakerFunctions ψ m} (hW : W ∈ inverseWhittakerSet ψ m π) :
    inverseWhittakerRankCast ψ h W ∈ inverseWhittakerSet ψ n (h ▸ π) := by
  subst n
  exact hW

end RankTransport

section TailIntegrand

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (n k : ℕ)

/-- The reversed-character zero-row tail integrand is the exact product
appearing in the lower-block calculation, with the two actual coefficient
functions retained. This is a function identity, not a measure comparison. -/
theorem reversedTail_unequalRankFunction
    (Wtest : InverseWhittakerFunctions ψ (n + (0 + k + 1)))
    (Wtail : WhittakerFunctions ψ n) (s : ℂ)
    (x : Matrix (Fin 0) (Fin (n + 1)) F)
    (g : Langlands.GeneralLinear (n + 1) F) :
    unequalRankFunction (ψ.scale (-1)) abv 0 k
      (inverseAsScaledStandard ψ Wtest) (standardAsScaledInverse ψ Wtail) s x g =
      Wtail.val g * Wtest.val (appendIdentity n (0 + k + 1) g) *
        determinantWeight abv g (s - ((0 + k + 1 : ℕ) : ℂ) / 2) := by
  simp only [unequalRankFunction, unequalRankMatrix_zero_rows,
    inverseAsScaledStandard, standardAsScaledInverse, mul_comm (Wtail.val g)]

end TailIntegrand

section Cutoff

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The published cutoff theorem also applies to every actual inverse
coefficient after the same-function character recasting. -/
theorem inverse_zeroRow_cutoff (n k : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.valuativeExtension
    letI := T.moduleTopology
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ
        (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V),
      IsSmooth π →
      ∀ W ∈ inverseWhittakerSet ψ (n + (0 + k + 1)) π,
        ∃ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier),
          (∀ y, Φ y = 0 ∨ Φ y = 1) ∧
          ∀ g : Langlands.GeneralLinear (n + 1) F.Carrier,
            W.val (appendIdentity n (0 + k + 1) g) * Φ (lastRow g) =
              W.val (appendIdentity n (0 + k + 1) g) := by
  let := T.topology
  let := T.valuativeRel
  let := T.valuativeExtension
  let := T.moduleTopology
  let := T.localField
  intro ψ V _ _ π hπ W hW
  obtain ⟨ℓ, hℓ⟩ := inverseAsScaledStandard_mem ψ π hW
  exact zeroRowLastRowCutoff p F T n k (ψ.scale (-1)) V π hπ ℓ
    ⟨inverseAsScaledStandard ψ W, hℓ⟩

end Cutoff

end Langlands.RankinSelberg.InducedTailIntermediate
