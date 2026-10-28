import Langlands.Representation.RankinSelberg.RankOneExtensionScalarCutoffStatement
import Langlands.Representation.RankinSelberg.UnequalRankSmearingAverage
import Langlands.HarmonicAnalysis.ScalarFourierClosureProof
import Langlands.Group.GL.NormalizedCharacter
import Langlands.HarmonicAnalysis.PadicLatticeGeometryProof
import Langlands.LocalField.Topology

/-!
# Proof of the same-model scalar Fourier cutoff for the early JPSS Lemma (5.5)

The cutoff set is a principal-unit neighborhood of `1`, small enough that the
quasicharacter is trivial on it, that it lies in the given open set, and that
the scalar diagonal matrices it defines fix a vector representing `f₂`.
The proof follows the paired Markdown.
-/

noncomputable section

namespace Langlands.RankinSelberg

open scoped WithZero
open MeasureTheory HarmonicAnalysis Whittaker Topology Langlands.GeneralLinear

universe uF uV

namespace ScalarCutoffProof

section Matrix

variable {R : Type uF} [Field R]

/-- The scalar block `a ↦ [I, 0; 0, a]` in the cell coordinates. -/
def scalarBlockHom (t : ℕ) :
    R →* Matrix (Fin (t + 1) ⊕ Fin 1) (Fin (t + 1) ⊕ Fin 1) R where
  toFun a := Matrix.fromBlocks 1 0 0 (Matrix.of fun (_ _ : Fin 1) => a)
  map_one' := by
    rw [← Matrix.fromBlocks_one]
    congr 1
    ext i j
    simp [Matrix.one_apply, Subsingleton.elim i j]
  map_mul' a b := by
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · simp
    · simp
    · simp
    · ext i j
      simp [Matrix.mul_apply]

/-- The scalar diagonal matrix `D(a)`, carrying `a` at the scalar coordinate. -/
def scalarDiagonal (t k : ℕ) (a : Rˣ) :
    Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) R :=
  GeneralLinear.rankInclusion (k + 1)
    (GeneralLinear.reindex (R := R) (rankOneExtensionCellCoordinates t)
      (Units.map (scalarBlockHom t) a))

theorem scalarDiagonal_one (t k : ℕ) :
    scalarDiagonal (R := R) t k 1 = 1 := by
  simp [scalarDiagonal]

/-- `[m, 0; x, a] = [m, 0; x, 1] [I, 0; 0, a]`. -/
theorem lowerBlock_eq_mul (t : ℕ) (m : Langlands.GeneralLinear (t + 1) R)
    (x : Fin (t + 1) → R) (a : Rˣ) :
    rankOneExtensionLowerBlock t m x a =
      rankOneExtensionLowerBlock t m x 1 *
        GeneralLinear.reindex (R := R) (rankOneExtensionCellCoordinates t)
          (Units.map (scalarBlockHom t) a) := by
  unfold rankOneExtensionLowerBlock
  rw [← map_mul]
  congr 1
  apply Units.ext
  change Matrix.fromBlocks m.val 0 (Matrix.of fun (_ : Fin 1) => x)
      (Matrix.of fun (_ _ : Fin 1) => a.val) =
    Matrix.fromBlocks m.val 0 (Matrix.of fun (_ : Fin 1) => x)
      (Matrix.of fun (_ _ : Fin 1) => (1 : Rˣ).val) *
    Matrix.fromBlocks 1 0 0 (Matrix.of fun (_ _ : Fin 1) => a.val)
  rw [Matrix.fromBlocks_multiply]
  congr 1
  · simp
  · simp
  · simp
  · ext i j
    simp [Matrix.mul_apply]

/-- The embedded block factors as `B(m,x,a) = B(m,x,1) D(a)`. -/
theorem embeddedLowerBlock_eq_mul (t k : ℕ) (m : Langlands.GeneralLinear (t + 1) R)
    (x : Fin (t + 1) → R) (a : Rˣ) :
    rankOneExtensionEmbeddedLowerBlock t k m x a =
      rankOneExtensionEmbeddedLowerBlock t k m x 1 * scalarDiagonal t k a := by
  rw [rankOneExtensionEmbeddedLowerBlock, lowerBlock_eq_mul, map_mul]
  rfl

theorem scalar_ne_firstTrailing (t k : ℕ) :
    (rankOneExtensionScalarIndex t).castAdd (k + 1) ≠
      rankOneExtensionFirstTrailingIndex t k := by
  intro h
  have hv := congrArg Fin.val h
  simp [rankOneExtensionFirstTrailingIndex] at hv

/-- The first trailing row of `B(m,x,a)` is the standard row. -/
theorem embeddedLowerBlock_trailing_row (t k : ℕ) (m : Langlands.GeneralLinear (t + 1) R)
    (x : Fin (t + 1) → R) (a : Rˣ) (j : Fin ((1 + (t + 1)) + (k + 1))) :
    rankOneExtensionEmbeddedLowerBlock t k m x a (rankOneExtensionFirstTrailingIndex t k) j =
      if j = rankOneExtensionFirstTrailingIndex t k then 1 else 0 := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have hne : Fin.castAdd (k + 1) j ≠ rankOneExtensionFirstTrailingIndex t k := by
      intro h
      have hv := congrArg Fin.val h
      simp [rankOneExtensionFirstTrailingIndex] at hv
      omega
    rw [ite_eq_right hne]
    exact GeneralLinear.blockSum_apply_right_left _ _ _ _
  · change GeneralLinear.blockSum (rankOneExtensionLowerBlock t m x a, 1)
      (Fin.natAdd (1 + (t + 1)) 0) (Fin.natAdd (1 + (t + 1)) j) = _
    rw [GeneralLinear.blockSum_apply_right]
    simp [rankOneExtensionFirstTrailingIndex, Matrix.one_apply, eq_comm]

/-- The scalar column of `B(m,x,a)` is `a` times the standard column. -/
theorem embeddedLowerBlock_scalar_column (t k : ℕ) (m : Langlands.GeneralLinear (t + 1) R)
    (x : Fin (t + 1) → R) (a : Rˣ) (i : Fin ((1 + (t + 1)) + (k + 1))) :
    rankOneExtensionEmbeddedLowerBlock t k m x a i
        ((rankOneExtensionScalarIndex t).castAdd (k + 1)) =
      if i = (rankOneExtensionScalarIndex t).castAdd (k + 1) then a.val else 0 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · change GeneralLinear.blockSum (rankOneExtensionLowerBlock t m x a, 1)
      (Fin.castAdd (k + 1) i) (Fin.castAdd (k + 1) (rankOneExtensionScalarIndex t)) = _
    rw [GeneralLinear.blockSum_apply_left]
    obtain ⟨i', rfl⟩ := (rankOneExtensionCellCoordinates t).surjective i
    rcases i' with i' | i'
    · have hne : Fin.castAdd (k + 1) (rankOneExtensionCellCoordinates t (Sum.inl i')) ≠
          Fin.castAdd (k + 1) (rankOneExtensionScalarIndex t) := by
        intro h
        have h' := (Fin.castAdd_injective _ _ h)
        exact Sum.inl_ne_inr ((rankOneExtensionCellCoordinates t).injective h')
      rw [ite_eq_right hne]
      exact rankOneExtensionLowerBlock_apply t m x a (Sum.inl i') (Sum.inr 0)
    · have hi : i' = 0 := Subsingleton.elim _ _
      subst hi
      exact (rankOneExtensionLowerBlock_scalar t m x a).trans (ite_eq_left rfl).symm
  · have hne : Fin.natAdd (1 + (t + 1)) i ≠
        (rankOneExtensionScalarIndex t).castAdd (k + 1) := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    rw [ite_eq_right hne]
    exact GeneralLinear.blockSum_apply_right_left _ _ _ _

/-- `B(m,x,a) S(u) = S(a u) B(m,x,a)`. -/
theorem embeddedLowerBlock_mul_smearing (t k : ℕ) (m : Langlands.GeneralLinear (t + 1) R)
    (x : Fin (t + 1) → R) (a : Rˣ) (u : R) :
    rankOneExtensionEmbeddedLowerBlock t k m x a * rankOneExtensionSmearingUnipotent t k u =
      rankOneExtensionSmearingUnipotent t k (a.val * u) *
        rankOneExtensionEmbeddedLowerBlock t k m x a := by
  apply Units.ext
  ext i j
  have hrow := embeddedLowerBlock_trailing_row t k m x a
  have hcol := embeddedLowerBlock_scalar_column t k m x a
  change ((rankOneExtensionEmbeddedLowerBlock t k m x a).val *
      Matrix.transvection ((rankOneExtensionScalarIndex t).castAdd (k + 1))
        (rankOneExtensionFirstTrailingIndex t k) u) i j =
    (Matrix.transvection ((rankOneExtensionScalarIndex t).castAdd (k + 1))
        (rankOneExtensionFirstTrailingIndex t k) (a.val * u) *
      (rankOneExtensionEmbeddedLowerBlock t k m x a).val) i j
  by_cases hj : j = rankOneExtensionFirstTrailingIndex t k
  · subst hj
    rw [Matrix.mul_transvection_apply_same]
    by_cases hi : i = (rankOneExtensionScalarIndex t).castAdd (k + 1)
    · subst hi
      rw [Matrix.transvection_mul_apply_same]
      erw [hcol, ite_eq_left rfl, hrow, ite_eq_left rfl]
      ring
    · rw [Matrix.transvection_mul_apply_of_ne (ha := hi)]
      erw [hcol, ite_eq_right hi]
      ring
  · rw [Matrix.mul_transvection_apply_of_ne (hb := hj)]
    by_cases hi : i = (rankOneExtensionScalarIndex t).castAdd (k + 1)
    · subst hi
      rw [Matrix.transvection_mul_apply_same]
      erw [hrow, ite_eq_right hj]
      ring
    · rw [Matrix.transvection_mul_apply_of_ne (ha := hi)]

/-- The smearing transvection is upper unipotent. -/
theorem smearing_mem_upperUnipotent (t k : ℕ) (c : R) :
    rankOneExtensionSmearingUnipotent t k c ∈
      upperUnipotent (((1 + (t + 1)) + k) + 1) R := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    change rankOneExtensionSmearingUnipotent t k c i j = 0
    rw [rankOneExtensionSmearingUnipotent_apply]
    have hne : i ≠ j := fun h => (lt_irrefl j) (h ▸ hij)
    rw [ite_eq_right hne, ite_eq_right]
    · simp
    · rintro ⟨rfl, rfl⟩
      have hv : (rankOneExtensionFirstTrailingIndex t k).val <
          ((rankOneExtensionScalarIndex t).castAdd (k + 1)).val := hij
      simp [rankOneExtensionFirstTrailingIndex] at hv
      omega
  · intro i
    change rankOneExtensionSmearingUnipotent t k c i i = 1
    rw [rankOneExtensionSmearingUnipotent_apply, ite_eq_left rfl, ite_eq_right]
    · simp
    · rintro ⟨rfl, h⟩
      exact scalar_ne_firstTrailing t k h

end Matrix

section Character

variable {R : Type uF} [Field R] [TopologicalSpace R]

/-- The standard character takes the value `ψ(c)` on the smearing transvection. -/
theorem standardCharacter_smearing (ψ : UnitaryAdditiveCharacter R) (t k : ℕ) (c : R) :
    (standardCharacter ψ ((1 + (t + 1)) + k)
        ⟨rankOneExtensionSmearingUnipotent t k c, smearing_mem_upperUnipotent t k c⟩ : ℂ) =
      ψ.complex c := by
  rw [standardCharacter_apply]
  congr 1
  rw [Finset.sum_eq_single ⟨t + 1, by omega⟩]
  · change rankOneExtensionSmearingUnipotent t k c _ _ = c
    rw [rankOneExtensionSmearingUnipotent_apply, ite_eq_right, ite_eq_left]
    · simp
    · constructor
      · ext
        simp
      · ext
        simp [rankOneExtensionFirstTrailingIndex]
        omega
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
  · intro b _ hb
    change rankOneExtensionSmearingUnipotent t k c _ _ = 0
    rw [rankOneExtensionSmearingUnipotent_apply, ite_eq_right, ite_eq_right]
    · simp
    · rintro ⟨h, -⟩
      apply hb
      ext
      have hv := congrArg Fin.val h
      simpa using hv
    · intro h
      have hv := congrArg Fin.val h
      simp at hv
  · simp

end Character

section Cutoff

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The cutoff set: elements of valuation one congruent to one modulo `π^n`.
Its units are exactly the principal units of level `n`. -/
def cutoffSet (n : ℕ) : Set F.Carrier :=
  {x | T.discreteValuation x = 1 ∧ (x - 1) / T.uniformizer ^ (n : ℤ) ∈ T.Integers}

theorem mem_cutoffSet_iff (n : ℕ) (u : F.Carrierˣ) :
    (u : F.Carrier) ∈ cutoffSet T n ↔ u ∈ T.principalUnits n :=
  (T.mem_principalUnits_iff_div_mem_integers n u).symm

theorem cutoffSet_isOpen (n : ℕ) :
    letI := T.topology
    IsOpen (cutoffSet T n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier
  have hval : IsOpen {x : F.Carrier | T.discreteValuation x = 1} := by
    convert (Valuation.isOpen_sphere (v := ValuativeRel.valuation F.Carrier)
      one_ne_zero) using 1
    ext x
    simp only [Set.mem_ofPred_eq, Valuation.restrict_eq_one_iff]
    change e (ValuativeRel.valuation F.Carrier x) = 1 ↔
      ValuativeRel.valuation F.Carrier x = 1
    constructor
    · intro h
      exact e.strictMono.injective (h.trans (map_one e).symm)
    · intro h
      rw [h, map_one]
  have hint : IsOpen (T.Integers : Set F.Carrier) := Valuation.isOpen_integer
  have hc : Continuous fun x : F.Carrier => (x - 1) / T.uniformizer ^ (n : ℤ) :=
    (continuous_id.sub (continuous_const (y := (1 : F.Carrier)))).div_const _
  exact hval.inter (hint.preimage hc)

theorem cutoffSet_isCompact_isClosed (n : ℕ) :
    letI := T.topology
    IsCompact (cutoffSet T n) ∧ IsClosed (cutoffSet T n) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hshell : T.valuationShell 0 = {x | T.discreteValuation x = 1} := by
    ext x
    simp [PadicField.TopologicalData.valuationShell]
  have hint : IsClosed (T.Integers : Set F.Carrier) := Valuation.isClosed_integer
  have hclosed : IsClosed (cutoffSet T n) := by
    have hc : Continuous fun x : F.Carrier => (x - 1) / T.uniformizer ^ (n : ℤ) :=
      (continuous_id.sub (continuous_const (y := (1 : F.Carrier)))).div_const _
    have h := (T.valuationShell_compact_closed 0).2.inter (hint.preimage hc)
    rw [hshell] at h
    exact h
  refine ⟨(T.valuationShell_compact_closed 0).1.of_isClosed_subset hclosed ?_, hclosed⟩
  intro x hx
  rw [hshell]
  exact hx.1

theorem one_mem_cutoffSet (n : ℕ) : (1 : F.Carrier) ∈ cutoffSet T n := by
  refine ⟨map_one _, ?_⟩
  rw [sub_self, zero_div]
  exact Subring.zero_mem _

theorem zero_not_mem_cutoffSet (n : ℕ) : (0 : F.Carrier) ∉ cutoffSet T n := by
  intro h
  have h0 := h.1
  rw [map_zero] at h0
  exact zero_ne_one h0

theorem exists_unit_of_mem_cutoffSet (n : ℕ) {y : F.Carrier} (hy : y ∈ cutoffSet T n) :
    ∃ a : F.Carrierˣ, (a : F.Carrier) = y ∧ a ∈ T.principalUnits n := by
  have hy0 : y ≠ 0 := fun h => zero_not_mem_cutoffSet T n (h ▸ hy)
  exact ⟨Units.mk0 y hy0, rfl, (mem_cutoffSet_iff T n _).mp hy⟩

end Cutoff

end ScalarCutoffProof

open ScalarCutoffProof in
/-- The same-model scalar Fourier cutoff for the early JPSS Lemma (5.5). -/
theorem rankOneExtensionScalarCutoff :
    RankOneExtensionScalarCutoffStatement.{uF, uV} := by
  intro p _ F ψ ν t k V _ _ π
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : TotallyDisconnectedSpace F.Carrier :=
    (padicLatticeGeometry F F.canonicalTopologicalData).1
  intro hπ ℓ f₂ χ O hO hO1
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f₂
  obtain ⟨K, hK⟩ := hπ v
  -- Continuity of the scalar diagonal and of the smearing transvection.
  have hφ : Continuous fun a : F.Carrierˣ =>
      Units.map (scalarBlockHom (R := F.Carrier) t) a := by
    rw [Units.continuous_iff]
    constructor
    · exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        (continuous_matrix fun _ _ => Units.continuous_val) :
          Continuous fun a : F.Carrierˣ =>
            Matrix.fromBlocks (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier) 0 0
              (Matrix.of fun (_ _ : Fin 1) => a.val))
    · exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        (continuous_matrix fun _ _ => Units.continuous_coe_inv) :
          Continuous fun a : F.Carrierˣ =>
            Matrix.fromBlocks (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) F.Carrier) 0 0
              (Matrix.of fun (_ _ : Fin 1) => (a⁻¹ : F.Carrierˣ).val))
  have hD : Continuous (scalarDiagonal (R := F.Carrier) t k) :=
    (GeneralLinear.rankInclusionContinuous (k + 1)).continuous.comp
      ((GeneralLinear.reindexContinuous (R := F.Carrier)
        (rankOneExtensionCellCoordinates t)).continuous.comp hφ)
  have hS : Continuous (rankOneExtensionSmearingUnipotent (K := F.Carrier) t k) := by
    have hval : Continuous fun u : F.Carrier =>
        (rankOneExtensionSmearingUnipotent t k u).val := by
      refine continuous_matrix fun i j => ?_
      exact (continuous_const.add (continuous_if_const _ (fun _ => continuous_id)
        (fun _ => continuous_const))).congr
          (fun u => (rankOneExtensionSmearingUnipotent_apply t k u i j).symm)
    rw [Units.continuous_iff]
    exact ⟨hval, hval.comp continuous_neg⟩
  -- The principal-unit level.
  obtain ⟨n₀, hn₀⟩ := F.canonicalTopologicalData.exists_multiplicativeTrivialAt χ
  have hDK : {a : F.Carrierˣ | scalarDiagonal t k a ∈ K} ∈ 𝓝 (1 : F.Carrierˣ) := by
    apply (K.isOpen.preimage hD).mem_nhds
    change scalarDiagonal t k 1 ∈ K
    rw [scalarDiagonal_one]
    exact K.one_mem
  obtain ⟨n₁, hn₁⟩ := F.canonicalTopologicalData.exists_principalUnits_subset hDK
  have hOO : (Units.val ⁻¹' O : Set F.Carrierˣ) ∈ 𝓝 (1 : F.Carrierˣ) :=
    (hO.preimage Units.continuous_val).mem_nhds (by simpa using hO1)
  obtain ⟨n₂, hn₂⟩ := F.canonicalTopologicalData.exists_principalUnits_subset hOO
  have hle₀ := F.canonicalTopologicalData.principalUnits_antitone
    (show n₀ ≤ n₀ + n₁ + n₂ by omega)
  have hle₁ := F.canonicalTopologicalData.principalUnits_antitone
    (show n₁ ≤ n₀ + n₁ + n₂ by omega)
  have hle₂ := F.canonicalTopologicalData.principalUnits_antitone
    (show n₂ ≤ n₀ + n₁ + n₂ by omega)
  let U := cutoffSet F.canonicalTopologicalData (n₀ + n₁ + n₂)
  obtain ⟨hUc, hUcl⟩ := cutoffSet_isCompact_isClosed F.canonicalTopologicalData (n₀ + n₁ + n₂)
  have hUo := cutoffSet_isOpen F.canonicalTopologicalData (n₀ + n₁ + n₂)
  have hUχ : ∀ a : F.Carrierˣ, (a : F.Carrier) ∈ U → χ a = 1 := fun a ha =>
    hn₀ a (hle₀ ((mem_cutoffSet_iff _ _ a).mp ha))
  have hfix : ∀ a : F.Carrierˣ, (a : F.Carrier) ∈ U → π (scalarDiagonal t k a) v = v := by
    intro a ha
    have hKa : scalarDiagonal t k a ∈ K.toSubgroup :=
      hn₁ (hle₁ ((mem_cutoffSet_iff _ _ a).mp ha))
    exact (Representation.mem_invariants _ _).mp hK ⟨_, hKa⟩
  -- The Schwartz–Bruhat pair.
  let Φ : SchwartzBruhat F.Carrier := Hecke.TestFunction.characteristic ⟨hUcl, hUo⟩ hUc
  have hΦ : ∀ b, Φ b = U.indicator (fun _ => (1 : ℂ)) b := fun b => rfl
  let Φneg := Hecke.TestFunction.pullback (Homeomorph.neg F.Carrier) Φ
  obtain ⟨κ, hκ⟩ := (scalarFourierClosure F.Carrier ψ ν.val ν.property).2 Φneg
  have hΦκ : ∀ b, Φ b = fourierIntegral ψ ν.val κ b := by
    intro b
    have hfun : (κ : F.Carrier → ℂ) = fourierTransform ψ ν.val Φneg := funext hκ
    calc Φ b = Φneg (-b) := by simp [Φneg]
      _ = fourierIntegral ψ ν.val (fourierTransform ψ ν.val Φneg) b :=
        ((ν.property Φneg).2 b).symm
      _ = fourierIntegral ψ ν.val κ b := by rw [hfun]
  have hΦin : ∀ a : F.Carrierˣ, (a : F.Carrier) ∈ U → Φ (a : F.Carrier) = ((χ a : ℂˣ) : ℂ)⁻¹ := by
    intro a ha
    rw [hΦ, Set.indicator_of_mem ha, hUχ a ha]
    simp
  have hΦout : ∀ a : F.Carrierˣ, (a : F.Carrier) ∉ U → Φ (a : F.Carrier) = 0 := by
    intro a ha
    rw [hΦ, Set.indicator_of_notMem ha]
  -- The smeared coefficient.
  obtain ⟨f₁, hf₁⟩ := Smearing.exists_coefficient_average ν.val.measure π hπ ℓ
    (rankOneExtensionSmearingUnipotent t k) hS κ (modelMap π ℓ v)
  have hcov : ∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier)
      (x : Fin (t + 1) → F.Carrier) (a : F.Carrierˣ) (u : F.Carrier),
      κ u * (modelMap π ℓ v).val.val
          (rankOneExtensionEmbeddedLowerBlock t k m x a *
            rankOneExtensionSmearingUnipotent t k u) =
        (ψ.complex (u * a) * κ u) *
          (modelMap π ℓ v).val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) := by
    intro m x a u
    have hθ := (modelMap π ℓ v).val.property
      ⟨rankOneExtensionSmearingUnipotent t k (a.val * u),
        smearing_mem_upperUnipotent t k (a.val * u)⟩
      (rankOneExtensionEmbeddedLowerBlock t k m x a)
    rw [embeddedLowerBlock_mul_smearing]
    erw [hθ]
    rw [standardCharacter_smearing, mul_comm (a.val) u]
    ring
  have hsmear : ∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier)
      (x : Fin (t + 1) → F.Carrier) (a : F.Carrierˣ),
      f₁.val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
        Φ (a : F.Carrier) *
          (modelMap π ℓ v).val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) := by
    intro m x a
    rw [(hf₁ _).2, funext (hcov m x a), integral_mul_const, hΦκ]
    rfl
  have hscalar : ∀ (m : Langlands.GeneralLinear (t + 1) F.Carrier)
      (x : Fin (t + 1) → F.Carrier) (a : F.Carrierˣ), (a : F.Carrier) ∈ U →
      (modelMap π ℓ v).val.val (rankOneExtensionEmbeddedLowerBlock t k m x a) =
        (modelMap π ℓ v).val.val (rankOneExtensionEmbeddedLowerBlock t k m x 1) := by
    intro m x a ha
    rw [embeddedLowerBlock_eq_mul]
    change ℓ.val (π (rankOneExtensionEmbeddedLowerBlock t k m x 1 * scalarDiagonal t k a) v) =
      ℓ.val (π (rankOneExtensionEmbeddedLowerBlock t k m x 1) v)
    rw [map_mul, Module.End.mul_apply, hfix a ha]
  refine ⟨U, κ, Φ, f₁, hUc, hUo, ?_, one_mem_cutoffSet _ _, zero_not_mem_cutoffSet _ _,
    ?_, ?_, hΦin, hΦout, hΦκ, hf₁, hsmear, hscalar, ?_, ?_⟩
  · intro y hy
    obtain ⟨a, rfl, ha⟩ := exists_unit_of_mem_cutoffSet _ _ hy
    exact hn₂ (hle₂ ha)
  · intro y hy
    exact (F.canonicalTopologicalData.normalizedAbs_eq_one_iff_discreteValuation y).mpr hy.1
  · rw [hΦ, Set.indicator_of_notMem (zero_not_mem_cutoffSet _ _)]
  · intro m x a ha
    rw [hsmear, hΦin a ha, hscalar m x a ha]
  · intro m x a ha
    rw [hsmear, hΦout a ha, zero_mul]

end Langlands.RankinSelberg
