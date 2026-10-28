import Langlands.Representation.RankinSelberg.RankOneExtensionCompactSectionStatement
import Langlands.Representation.RankinSelberg.RankOneExtensionCellAlgebra
import Langlands.Representation.Induction.CompactLocalSection
import Langlands.Group.GL.BlockIwahoriBasis
import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof

/-!
# Proof of the normalized compact sections for the strict rank-one extension

The section is the published double-coset section `P̄ · 1 · K` of the lower
induction, for a compact open subgroup `K` with block Iwahori factorization for the
lower shape, and value `vol(L)⁻¹ (w ⊗ 1)` at the identity, where `L = {y | u(y) ∈ K}`.
The test function is `vol(L)⁻¹ 1_L`. Since `P̄` meets the upper radical trivially,
the factorization `K = (K ∩ N̄) (K ∩ M) (K ∩ N)` identifies the section on the whole
upper cell and its support.
-/

noncomputable section

open MeasureTheory Topology

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]

/-- The lower block parabolic meets the upper block radical trivially. -/
theorem eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup
    {g : GeneralLinear n R} (hP : g ∈ B.oppositeParabolic R)
    (hU : g ∈ B.unipotentSubgroup R) : g = 1 := by
  rw [B.mem_oppositeParabolic_iff] at hP
  rw [B.mem_unipotentSubgroup_iff, B.mem_parabolic_iff] at hU
  obtain ⟨hU, hD⟩ := hU
  apply Units.ext
  ext r s
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective r
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective s
  change g (B.index i a) (B.index j b) =
    (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index j b)
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hP i j a b h, Matrix.one_apply_ne]
    intro he
    exact (ne_of_lt h) (congrArg Sigma.fst
      (B.indexEquiv.injective (show B.indexEquiv ⟨i, a⟩ = B.indexEquiv ⟨j, b⟩ from he)))
  · rw [hD i a b]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Matrix.one_apply_ne ((B.index i).injective.ne hab)]
  · rw [hU i j a b h, Matrix.one_apply_ne]
    intro he
    exact (ne_of_lt h) (congrArg Sigma.fst
      (B.indexEquiv.injective (show B.indexEquiv ⟨i, a⟩ = B.indexEquiv ⟨j, b⟩ from he))).symm

theorem oppositeUnipotentSubgroup_le_oppositeParabolic :
    B.oppositeUnipotentSubgroup R ≤ B.oppositeParabolic R := by
  rintro _ ⟨h, -, rfl⟩
  exact h.property

theorem leviSubgroup_le_oppositeParabolic :
    B.leviSubgroup R ≤ B.oppositeParabolic R := by
  rintro _ ⟨m, rfl⟩
  exact (B.oppositeLeviInParabolic R m).property

end Langlands.GeneralLinear.BlockShape

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis

universe uF uV uW uX

section Cell

variable {R : Type uF} [Field R] (t : ℕ)

/-- The entries `(i, t + 1)`, `i ≤ t`, of a matrix: the coordinates of the upper cell. -/
def rankOneExtensionCellCoordinate (g : Langlands.GeneralLinear (1 + (t + 1)) R) :
    Fin (t + 1) → R :=
  fun i => g (rankOneExtensionHeadIndex t i) (rankOneExtensionScalarIndex t)

theorem rankOneExtensionLowerShape_index_zero (a : Fin (t + 1)) :
    (rankOneExtensionLowerShape t).index (0 : Fin 2) a =
      rankOneExtensionCellCoordinates t (Sum.inl a) := by
  apply Fin.ext
  change ((rankOneExtensionLowerShape t).indexEquiv ⟨(0 : Fin 2), a⟩).val = _
  rw [BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  simp [rankOneExtensionCellCoordinates]

theorem rankOneExtensionLowerShape_index_one (b : Fin 1) :
    (rankOneExtensionLowerShape t).index (1 : Fin 2) b =
      rankOneExtensionCellCoordinates t (Sum.inr b) := by
  apply Fin.ext
  change ((rankOneExtensionLowerShape t).indexEquiv ⟨(1 : Fin 2), b⟩).val = _
  rw [BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  change (∑ k : Fin 1, (rankOneExtensionLowerShape t).size
    (Fin.castLE (by decide : 1 ≤ 2) k)) + b.val = _
  rw [Fin.sum_univ_one]
  simp [rankOneExtensionCellCoordinates]
  omega

theorem rankOneExtensionCellCoordinate_upperCell (y : Fin (t + 1) → R) :
    rankOneExtensionCellCoordinate t (rankOneExtensionUpperCell t y) = y := by
  funext i
  exact (rankOneExtensionUpperCell_apply t y (Sum.inl i) (Sum.inr 0)).trans (by simp)

theorem rankOneExtensionUpperCell_inv (y : Fin (t + 1) → R) :
    (rankOneExtensionUpperCell t y)⁻¹ = rankOneExtensionUpperCell t (-y) := by
  apply Units.ext
  rfl

theorem rankOneExtensionUpperCell_index_one_zero (y : Fin (t + 1) → R)
    (a : Fin 1) (b : Fin (t + 1)) :
    rankOneExtensionUpperCell t y ((rankOneExtensionLowerShape t).index (1 : Fin 2) a)
      ((rankOneExtensionLowerShape t).index (0 : Fin 2) b) = 0 := by
  rw [rankOneExtensionLowerShape_index_one, rankOneExtensionLowerShape_index_zero,
    rankOneExtensionUpperCell_apply]
  simp

theorem rankOneExtensionUpperCell_index_zero_zero (y : Fin (t + 1) → R)
    (a b : Fin (t + 1)) :
    rankOneExtensionUpperCell t y ((rankOneExtensionLowerShape t).index (0 : Fin 2) a)
      ((rankOneExtensionLowerShape t).index (0 : Fin 2) b) = if a = b then 1 else 0 := by
  rw [rankOneExtensionLowerShape_index_zero, rankOneExtensionLowerShape_index_zero,
    rankOneExtensionUpperCell_apply]
  simp [Matrix.one_apply]

theorem rankOneExtensionUpperCell_index_one_one (y : Fin (t + 1) → R) (a b : Fin 1) :
    rankOneExtensionUpperCell t y ((rankOneExtensionLowerShape t).index (1 : Fin 2) a)
      ((rankOneExtensionLowerShape t).index (1 : Fin 2) b) = if a = b then 1 else 0 := by
  rw [rankOneExtensionLowerShape_index_one, rankOneExtensionLowerShape_index_one,
    rankOneExtensionUpperCell_apply, Subsingleton.elim a b]
  simp

/-- The upper cell lies in the upper radical of the lower shape. -/
theorem rankOneExtensionUpperCell_mem_unipotentSubgroup (y : Fin (t + 1) → R) :
    rankOneExtensionUpperCell t y ∈ (rankOneExtensionLowerShape t).unipotentSubgroup R := by
  rw [BlockShape.mem_unipotentSubgroup_iff, BlockShape.mem_parabolic_iff]
  refine ⟨fun i j a b hji => ?_, fun i a b => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact False.elim ((lt_irrefl _) hji)
    · exact False.elim (by simp at hji)
    · exact rankOneExtensionUpperCell_index_one_zero t y a b
    · exact False.elim ((lt_irrefl _) hji)
  · fin_cases i
    · exact rankOneExtensionUpperCell_index_zero_zero t y a b
    · exact rankOneExtensionUpperCell_index_one_one t y a b

/-- Every element of the upper radical of the lower shape is an upper cell. -/
theorem eq_rankOneExtensionUpperCell_of_mem_unipotentSubgroup
    {g : Langlands.GeneralLinear (1 + (t + 1)) R}
    (hg : g ∈ (rankOneExtensionLowerShape t).unipotentSubgroup R) :
    g = rankOneExtensionUpperCell t (rankOneExtensionCellCoordinate t g) := by
  rw [BlockShape.mem_unipotentSubgroup_iff, BlockShape.mem_parabolic_iff] at hg
  obtain ⟨hP, hD⟩ := hg
  apply Units.ext
  ext r s
  obtain ⟨i, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective r
  obtain ⟨j, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective s
  rw [rankOneExtensionUpperCell_apply]
  rcases i with a | a <;> rcases j with b | b
  · have h : g (rankOneExtensionCellCoordinates t (Sum.inl a))
        (rankOneExtensionCellCoordinates t (Sum.inl b)) = if a = b then 1 else 0 := by
      have h0 := hD (0 : Fin 2) a b
      rwa [rankOneExtensionLowerShape_index_zero, rankOneExtensionLowerShape_index_zero] at h0
    rw [h]
    simp [Matrix.one_apply]
  · have hb : b = 0 := Subsingleton.elim _ _
    subst hb
    simp [rankOneExtensionCellCoordinate, rankOneExtensionHeadIndex,
      rankOneExtensionScalarIndex]
  · have h : g (rankOneExtensionCellCoordinates t (Sum.inr a))
        (rankOneExtensionCellCoordinates t (Sum.inl b)) = 0 := by
      have h0 := hP (1 : Fin 2) (0 : Fin 2) a b (show (0 : Fin 2) < 1 by decide)
      rwa [rankOneExtensionLowerShape_index_one, rankOneExtensionLowerShape_index_zero] at h0
    rw [h]
    simp
  · have h : g (rankOneExtensionCellCoordinates t (Sum.inr a))
        (rankOneExtensionCellCoordinates t (Sum.inr b)) = if a = b then 1 else 0 := by
      have h0 := hD (1 : Fin 2) a b
      rwa [rankOneExtensionLowerShape_index_one, rankOneExtensionLowerShape_index_one] at h0
    rw [h, Subsingleton.elim a b]
    simp

variable [TopologicalSpace R] [IsTopologicalRing R]

omit [IsTopologicalRing R] in
theorem continuous_rankOneExtensionCellCoordinate :
    Continuous (rankOneExtensionCellCoordinate (R := R) t) :=
  continuous_pi fun _ => (GeneralLinear.entry _ _).continuous

theorem continuous_rankOneExtensionUpperCell :
    Continuous (rankOneExtensionUpperCell (K := R) t) := by
  have hval : Continuous fun y : Fin (t + 1) → R =>
      ((rankOneExtensionUpperCell t y : Langlands.GeneralLinear (1 + (t + 1)) R) :
        Matrix (Fin (1 + (t + 1))) (Fin (1 + (t + 1))) R) := by
    apply continuous_pi
    intro r
    apply continuous_pi
    intro s
    obtain ⟨i, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective r
    obtain ⟨j, rfl⟩ := (rankOneExtensionCellCoordinates t).surjective s
    simp only [rankOneExtensionUpperCell_apply]
    rcases i with a | a <;> rcases j with b | b <;> simp <;> fun_prop
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [rankOneExtensionUpperCell_inv]
  exact hval.comp continuous_neg

end Cell

section Smooth

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The inflated and twisted inducing representation of a smooth Levi representation
is smooth on the lower parabolic. -/
theorem isSmooth_oppositeInducing (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (σ : Representation ℂ (B.Levi F.Carrier) X)
    (hσ : letI := T.topology; IsSmooth σ) :
    letI := T.topology
    IsSmooth (twist (T.oppositeParabolicHalfModulus B)
      (σ.comp (B.oppositeLeviProjection F.Carrier))) := by
  let := T.topology
  exact (isSmooth_twist_iff _ _ (T.isOpen_ker_oppositeParabolicHalfModulus B)).2
    (isSmooth_comp _ (T.oppositeBlockLeviProjection B).continuous hσ)

end Smooth

section Construction

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The cell-section construction for an arbitrary smooth representation `ρ` of the
lower parabolic of the lower shape and an arbitrary vector `x₀`. -/
theorem exists_rankOneExtensionCellSection
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (t k : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {X : Type uX} [AddCommGroup X] [Module ℂ X]
    (π : Representation ℂ (Langlands.GeneralLinear ((1 + (t + 1)) + (k + 1)) F.Carrier) V)
    (ρ : Representation ℂ ((rankOneExtensionLowerShape t).oppositeParabolic F.Carrier) X)
    (v : V) (x₀ : X)
    (hπ : letI := F.canonicalTopologicalData.topology; IsSmooth π)
    (hρ : letI := F.canonicalTopologicalData.topology; IsSmooth ρ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.generalLinearTopologicalGroup (1 + (t + 1))
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ O : Set (Fin (t + 1) → F.Carrier), IsOpen O → (0 : Fin (t + 1) → F.Carrier) ∈ O →
      ∃ (φ : SchwartzBruhat (Fin (t + 1) → F.Carrier))
        (s : Induction.SmoothFunctions
          ((rankOneExtensionLowerShape t).oppositeParabolic F.Carrier) ρ),
        Function.support φ ⊆ O ∧
        Integrable φ (rowMeasure ν.val (t + 1)) ∧
        ∫ y, φ y ∂rowMeasure ν.val (t + 1) = 1 ∧
        (∀ y : Fin (t + 1) → F.Carrier,
          Induction.eval _ ρ s (rankOneExtensionUpperCell t y) = φ y • x₀) ∧
        (∀ g : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier,
          Induction.eval _ ρ s g ≠ 0 →
            ∃ q : (rankOneExtensionLowerShape t).oppositeParabolic F.Carrier,
              ∃ y ∈ Function.support φ,
                g = (q : Langlands.GeneralLinear (1 + (t + 1)) F.Carrier) *
                  rankOneExtensionUpperCell t y) ∧
        (∀ y ∈ Function.support φ,
          π (rankInclusion (k + 1) (rankOneExtensionUpperCell t y)) v = v) := by
  intro O hO hO0
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (1 + (t + 1))
  let := borel F.Carrier
  have : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  have := T.secondCountableTopology
  have := T.sigmaCompactSpace
  have : IsTopologicalRing F.Carrier := inferInstance
  let B := rankOneExtensionLowerShape t
  let P := B.oppositeParabolic F.Carrier
  let G := Langlands.GeneralLinear (1 + (t + 1)) F.Carrier
  -- Open stabilizers of `v` and `x₀`.
  obtain ⟨Kπ, hKπ⟩ := hπ v
  obtain ⟨H, hH⟩ := hρ x₀
  obtain ⟨O', hO'open, hO'⟩ := isOpen_induced_iff.mp H.isOpen
  let U : Set G := O' ∩ (rankInclusion (k + 1)) ⁻¹' (Kπ : Set _) ∩
    rankOneExtensionCellCoordinate t ⁻¹' O
  have hU : U ∈ 𝓝 (1 : G) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact (hO'open.inter (Kπ.isOpen.preimage
        (rankInclusionContinuous (R := F.Carrier) (n := 1 + (t + 1)) (k + 1)).continuous)).inter
        (hO.preimage (continuous_rankOneExtensionCellCoordinate t))
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · have h1 : (1 : P) ∈ (Subtype.val ⁻¹' O' : Set P) := by
          rw [hO']
          exact H.one_mem
        exact h1
      · change rankInclusion (k + 1) (1 : G) ∈ Kπ
        rw [map_one]
        exact Kπ.one_mem
      · change rankOneExtensionCellCoordinate t (1 : G) ∈ O
        have h1 : rankOneExtensionCellCoordinate t (1 : G) = 0 := by
          rw [← rankOneExtensionUpperCell_zero (t := t), rankOneExtensionCellCoordinate_upperCell]
        rw [h1]
        exact hO0
  -- A compact open subgroup with block Iwahori factorization inside `U`.
  obtain ⟨K, hKc, hKU, hKfac⟩ := B.exists_compactOpenSubgroup_hasBlockIwahoriFactorization T hU
  have hfac : ∀ g ∈ K, ∃ q ∈ P, ∃ n ∈ K, n ∈ B.unipotentSubgroup F.Carrier ∧ g = q * n := by
    intro g hg
    obtain ⟨⟨l, m, n⟩, hlmn⟩ :=
      (BlockShape.HasBlockIwahoriFactorization.bijective _ _ hKfac).2 ⟨g, hg⟩
    have he : l.val * m.val * n.val = g := congrArg Subtype.val hlmn
    exact ⟨l.val * m.val,
      P.mul_mem (B.oppositeUnipotentSubgroup_le_oppositeParabolic F.Carrier l.property.2)
        (B.leviSubgroup_le_oppositeParabolic F.Carrier m.property.2),
      n.val, n.property.1, n.property.2, he.symm⟩
  -- The normalized test function.
  let L : Set (Fin (t + 1) → F.Carrier) := rankOneExtensionUpperCell t ⁻¹' (K : Set G)
  have hLopen : IsOpen L := K.isOpen.preimage (continuous_rankOneExtensionUpperCell t)
  have hLclosed : IsClosed L := K.isClosed.preimage (continuous_rankOneExtensionUpperCell t)
  have hL0 : (0 : Fin (t + 1) → F.Carrier) ∈ L := by
    change rankOneExtensionUpperCell t 0 ∈ K
    rw [rankOneExtensionUpperCell_zero]
    exact K.one_mem
  have hLsub : L ⊆ rankOneExtensionCellCoordinate t '' (K : Set G) :=
    fun y hy => ⟨rankOneExtensionUpperCell t y, hy, rankOneExtensionCellCoordinate_upperCell t y⟩
  have hLcompact : IsCompact L :=
    (hKc.image (continuous_rankOneExtensionCellCoordinate t)).of_isClosed_subset hLclosed hLsub
  let μ := rowMeasure ν.val (t + 1)
  have hLmeas : MeasurableSet L := hLopen.measurableSet
  have hμpos : 0 < μ L := hLopen.measure_pos μ ⟨0, hL0⟩
  have hμfin : μ L < ⊤ := hLcompact.measure_lt_top
  have hreal : 0 < μ.real L := ENNReal.toReal_pos hμpos.ne' hμfin.ne
  let c : ℂ := ((μ.real L : ℝ) : ℂ)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (by exact_mod_cast hreal.ne')
  let φf : (Fin (t + 1) → F.Carrier) → ℂ := L.indicator (fun _ => c)
  have hφlc : IsLocallyConstant φf :=
    (LocallyConstant.indicator (LocallyConstant.const _ c) ⟨hLclosed, hLopen⟩).isLocallyConstant
  have hφcs : HasCompactSupport φf :=
    HasCompactSupport.intro' hLcompact hLclosed (fun y hy => Set.indicator_of_notMem hy _)
  let φ : SchwartzBruhat (Fin (t + 1) → F.Carrier) := ⟨φf, hφlc, hφcs⟩
  have hφL : ∀ y, y ∈ L → φ y = c := fun y hy => by
    change L.indicator (fun _ => c) y = c
    exact Set.indicator_of_mem hy _
  have hφnL : ∀ y, y ∉ L → φ y = 0 := fun y hy => by
    change L.indicator (fun _ => c) y = 0
    exact Set.indicator_of_notMem hy _
  have hsupp : Function.support φ = L := by
    ext y
    by_cases hy : y ∈ L
    · simp only [Function.mem_support, hφL y hy, hy, iff_true]
      exact hc
    · simp only [Function.mem_support, hφnL y hy, hy, ne_eq, not_true_eq_false]
  -- The double-coset section.
  have hx : c • x₀ ∈ fixedVectors ρ (Induction.conjOpenSubgroup P K 1).toSubgroup := by
    rintro ⟨q, hq⟩
    have hqK : (q : G) ∈ K := by
      simpa using Induction.mem_conjOpenSubgroup.mp hq
    have hqH : q ∈ H := by
      have h1 : q ∈ (Subtype.val ⁻¹' O' : Set P) := (hKU hqK).1.1
      rw [hO'] at h1
      exact h1
    change ρ q (c • x₀) = c • x₀
    rw [map_smul]
    exact congrArg (c • ·) (hH ⟨q, hqH⟩)
  let s := Induction.compactDoubleCosetSection P ρ K hKc 1 (c • x₀) hx
  have key : ∀ g : G, Induction.eval P ρ s.val g ≠ 0 →
      ∃ q ∈ P, ∃ n ∈ K, n ∈ B.unipotentSubgroup F.Carrier ∧ g = q * n := by
    intro g hg
    have hmem : Induction.quotientMap P g ∈
        Induction.quotientSupport P (Induction.eval P ρ s.val) := ⟨g, hg, rfl⟩
    obtain ⟨k', hk', hkk⟩ :=
      Induction.compactDoubleCosetSection_support_subset P ρ K hKc 1 (c • x₀) hx hmem
    have hr : g * (1 * k')⁻¹ ∈ P := QuotientGroup.rightRel_apply.mp (Quotient.exact hkk)
    obtain ⟨q₀, hq₀, n, hnK, hnU, hk'eq⟩ := hfac k' hk'
    refine ⟨g * k'⁻¹ * q₀, P.mul_mem (by simpa using hr) hq₀, n, hnK, hnU, ?_⟩
    subst hk'eq
    group
  have hcell : ∀ y, y ∉ L → Induction.eval P ρ s.val (rankOneExtensionUpperCell t y) = 0 := by
    intro y hy
    by_contra hne
    obtain ⟨q, hq, n, hnK, hnU, he⟩ := key _ hne
    have hqU : q ∈ B.unipotentSubgroup F.Carrier := by
      have : q = rankOneExtensionUpperCell t y * n⁻¹ := by
        rw [he]
        group
      rw [this]
      exact (B.unipotentSubgroup F.Carrier).mul_mem
        (rankOneExtensionUpperCell_mem_unipotentSubgroup t y)
        ((B.unipotentSubgroup F.Carrier).inv_mem hnU)
    have hq1 := B.eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup F.Carrier hq hqU
    apply hy
    change rankOneExtensionUpperCell t y ∈ K
    rw [he, hq1, one_mul]
    exact hnK
  refine ⟨φ, s.val, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- support in `O`
    rw [hsupp]
    intro y hy
    have h := (hKU hy).2
    change rankOneExtensionCellCoordinate t (rankOneExtensionUpperCell t y) ∈ O at h
    rwa [rankOneExtensionCellCoordinate_upperCell] at h
  · -- integrability
    exact (integrableOn_const hμfin.ne).integrable_indicator hLmeas
  · -- integral one
    change ∫ y, L.indicator (fun _ => c) y ∂μ = 1
    rw [integral_indicator_const _ hLmeas, Complex.real_smul]
    exact mul_inv_cancel₀ (by exact_mod_cast hreal.ne')
  · -- restriction to the upper cell
    intro y
    by_cases hy : y ∈ L
    · have h := Induction.compactDoubleCosetSection_apply P ρ K hKc 1 (c • x₀) hx 1
        ⟨rankOneExtensionUpperCell t y, hy⟩
      simp only [OneMemClass.coe_one, one_mul, map_one] at h
      rw [hφL y hy]
      exact h
    · rw [hφnL y hy, zero_smul]
      exact hcell y hy
  · -- support in `P̄ · u(supp φ)`
    intro g hg
    obtain ⟨q, hq, n, hnK, hnU, he⟩ := key g hg
    have hn := eq_rankOneExtensionUpperCell_of_mem_unipotentSubgroup t hnU
    refine ⟨⟨q, hq⟩, rankOneExtensionCellCoordinate t n, ?_, ?_⟩
    · rw [hsupp]
      change rankOneExtensionUpperCell t (rankOneExtensionCellCoordinate t n) ∈ K
      rw [← hn]
      exact hnK
    · rw [he, ← hn]
  · -- `v` is fixed on the support
    intro y hy
    rw [hsupp] at hy
    exact hKπ ⟨_, (hKU hy).1.2⟩

end Construction

section Final

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {W : Type uW} [AddCommGroup W] [Module ℂ W] (t : ℕ)
  (χ : letI := F.canonicalTopologicalData.topology; Quasicharacter F.Carrier)
  (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)

/-- The two block factors `(σ, χ)` of the lower induction are smooth. -/
theorem rankOneExtensionLowerFamily_isSmooth
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ) :
    letI := F.canonicalTopologicalData.topology
    ∀ i, IsSmooth (rankOneExtensionLowerFamily F t (rankOneExtensionCharacter.{uF, uW} F χ) σ i) := by
  let := F.canonicalTopologicalData.topology
  intro i
  fin_cases i
  · exact hσ
  · exact rankOneExtensionCharacter_isSmooth F ψ χ

/-- The inducing representation of the lower induction of `(σ, χ)` is smooth. -/
theorem rankOneExtensionLowerInducing_isSmooth
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (hσ : letI := F.canonicalTopologicalData.topology; IsSmooth σ) :
    letI := F.canonicalTopologicalData.topology
    letI : ∀ i : Fin (rankOneExtensionLowerShape t).length,
        AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
      Shahidi.pairCarrier.instAddCommGroup i.rev
    letI : ∀ i : Fin (rankOneExtensionLowerShape t).length,
        Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
      Shahidi.pairCarrier.instModule ℂ i.rev
    IsSmooth (twist (V := PiTensorProduct ℂ (rankOneExtensionLowerCarrier (W := W)))
      (F.canonicalTopologicalData.oppositeParabolicHalfModulus (rankOneExtensionLowerShape t))
      (((rankOneExtensionLowerShape t).blockTensor
        (V := rankOneExtensionLowerCarrier (W := W))
        (rankOneExtensionLowerFamily F t (rankOneExtensionCharacter.{uF, uW} F χ) σ)).comp
        ((rankOneExtensionLowerShape t).oppositeLeviProjection F.Carrier))) := by
  let := F.canonicalTopologicalData.topology
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      AddCommGroup (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instAddCommGroup i.rev
  let : ∀ i : Fin (rankOneExtensionLowerShape t).length,
      Module ℂ (rankOneExtensionLowerCarrier (W := W) i) := fun i =>
    Shahidi.pairCarrier.instModule ℂ i.rev
  exact isSmooth_oppositeInducing F.canonicalTopologicalData (rankOneExtensionLowerShape t) _
    (FiniteTensor.isSmooth_external _ (rankOneExtensionLowerFamily_isSmooth F t χ σ ψ hσ))

end Final

/-- JPSS (1983), Lemma (5.5), formulas (5)–(7): normalized compact sections of the actual
lower induction of `(σ, χ)`. -/
theorem rankOneExtensionCompactSection :
    RankOneExtensionCompactSectionStatement.{uF, uV, uW} := by
  intro p _ F ψ ν t k V _ _ W _ _ π σ χ v w hπ hσ O hO hO0
  obtain ⟨φ, s, h1, h2, h3, h4, h5, h6⟩ :=
    exists_rankOneExtensionCellSection F ψ ν t k π _ v
      (rankOneExtensionLowerPureTensor w (ULift.up 1)) hπ
      (rankOneExtensionLowerInducing_isSmooth F t χ σ ψ hσ) O hO hO0
  refine ⟨φ, (rankOneExtensionLowerModel F t χ σ).asModuleEquiv.symm s,
    h1, h2, h3, ?_, ?_, h6⟩
  · exact h4
  · exact h5

end Langlands.RankinSelberg
