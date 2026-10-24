import Langlands.Representation.RankinSelberg.PadicPairFactors

/-!
# Gamma relations over general nonarchimedean local fields

Canonical Borel specializations of the existing JPSS relation, and its
larger-rank-first extension. No factor is selected and no existence is assumed.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW uV₂ uW₂

section General

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- The published pair gamma relation with Borel measurable structures on the
field, the smaller-rank groups and their quotient. The spectral cardinality,
absolute value and Fourier measure are explicit inputs. -/
def IsGeneralPairGammaFactor (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : letI := borel F; AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (G : RationalFunctions) : Prop :=
  letI := borel F
  letI : BorelSpace F := ⟨rfl⟩
  letI := borel (Langlands.GeneralLinear (n + 1) F)
  letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  letI := borel (upperUnipotent (n + 1) F)
  letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  letI := borel (LeftUnipotentQuotient n F)
  IsPairGammaFactor q ψ abv ν π σ G

/-- The gamma relation for either positive-rank order, with the larger rank
first. Equal ranks retain the given order. This is the gamma analogue of the
convention for L and epsilon factors in JPSS (2.12). -/
def IsGeneralSymmetricGammaFactor (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (ν : letI := borel F; AdditiveHaarMeasure F)
    {r n : ℕ} {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (G : RationalFunctions) : Prop :=
  if n ≤ r then IsGeneralPairGammaFactor q ψ abv ν π σ G
  else IsGeneralPairGammaFactor q ψ abv ν σ π G

variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : letI := borel F; AdditiveHaarMeasure F}
  {r n : ℕ} {V : Type uV} {W : Type uW} {V₂ : Type uV₂} {W₂ : Type uW₂}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup V₂] [Module ℂ V₂] [AddCommGroup W₂] [Module ℂ W₂]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {π₂ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V₂}
  {σ₂ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W₂}
  {G G' : RationalFunctions}

/-- Uniqueness is inherited from the existing pair relation. -/
theorem IsGeneralPairGammaFactor.unique (hq : 1 < q)
    (h : IsGeneralPairGammaFactor q ψ abv ν π σ G)
    (h' : IsGeneralPairGammaFactor q ψ abv ν π σ G') : G = G' := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  exact IsPairGammaFactor.unique hq h h'

/-- Representation equivalences may change both carrier universes. -/
theorem IsGeneralPairGammaFactor.congr_equiv (φ : π.Equiv π₂) (φ' : σ.Equiv σ₂) :
    IsGeneralPairGammaFactor q ψ abv ν π σ G ↔
      IsGeneralPairGammaFactor q ψ abv ν π₂ σ₂ G := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  exact IsPairGammaFactor.congr_equiv φ φ'

theorem isGeneralSymmetricGammaFactor_of_le (h : n ≤ r) :
    IsGeneralSymmetricGammaFactor q ψ abv ν π σ G ↔
      IsGeneralPairGammaFactor q ψ abv ν π σ G := by
  simp only [IsGeneralSymmetricGammaFactor, h, ↓reduceIte]

theorem isGeneralSymmetricGammaFactor_of_lt (h : r < n) :
    IsGeneralSymmetricGammaFactor q ψ abv ν π σ G ↔
      IsGeneralPairGammaFactor q ψ abv ν σ π G := by
  simp only [IsGeneralSymmetricGammaFactor, Nat.not_le.mpr h, ↓reduceIte]

/-- The larger-rank-first relation has at most one rational-function witness. -/
theorem IsGeneralSymmetricGammaFactor.unique (hq : 1 < q)
    (h : IsGeneralSymmetricGammaFactor q ψ abv ν π σ G)
    (h' : IsGeneralSymmetricGammaFactor q ψ abv ν π σ G') : G = G' := by
  unfold IsGeneralSymmetricGammaFactor at h h'
  split_ifs at h h'
  · exact h.unique hq h'
  · exact h.unique hq h'

theorem IsGeneralSymmetricGammaFactor.congr_equiv (φ : π.Equiv π₂)
    (φ' : σ.Equiv σ₂) :
    IsGeneralSymmetricGammaFactor q ψ abv ν π σ G ↔
      IsGeneralSymmetricGammaFactor q ψ abv ν π₂ σ₂ G := by
  unfold IsGeneralSymmetricGammaFactor
  split_ifs
  · exact IsGeneralPairGammaFactor.congr_equiv φ φ'
  · exact IsGeneralPairGammaFactor.congr_equiv φ' φ

end General

section Padic

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uF} p)
  (ψ : letI := K.canonicalTopologicalData.topology; UnitaryAdditiveCharacter K.Carrier)
  (ν : letI := K.canonicalTopologicalData.topology; letI := borel K.Carrier
    AdditiveHaarMeasure K.Carrier)
  {r n : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) K.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) K.Carrier) W)
  (G : RationalFunctions)

/-- At the canonical p-adic data, the general pair relation is the published
p-adic relation, by definitional equality. -/
theorem isGeneralPairGammaFactor_padic :
    (letI := K.canonicalTopologicalData.topology
     letI := K.canonicalTopologicalData.valuativeRel
     letI := K.canonicalTopologicalData.localField
     IsGeneralPairGammaFactor K.canonicalTopologicalData.residueCardinality ψ
       (normalizedAbsoluteValue K.canonicalTopologicalData) ν π σ G) ↔
      IsPadicPairGammaFactor K ψ ν π σ G :=
  Iff.rfl

/-- Both rank branches specialize to the existing p-adic symmetric relation. -/
theorem isGeneralSymmetricGammaFactor_padic :
    (letI := K.canonicalTopologicalData.topology
     letI := K.canonicalTopologicalData.valuativeRel
     letI := K.canonicalTopologicalData.localField
     IsGeneralSymmetricGammaFactor K.canonicalTopologicalData.residueCardinality ψ
       (normalizedAbsoluteValue K.canonicalTopologicalData) ν π σ G) ↔
      IsPadicSymmetricGammaFactor K ψ ν π σ G :=
  Iff.rfl

end Padic

end Langlands.RankinSelberg
