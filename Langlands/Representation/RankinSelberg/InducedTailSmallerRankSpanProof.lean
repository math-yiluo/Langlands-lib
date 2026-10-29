import Langlands.Representation.RankinSelberg.InducedTailSpanStatement
import Langlands.Representation.Whittaker.TwoBlockExtensionProof
import Langlands.Representation.RankinSelberg.TwistInvariance
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.Hecke.TestFunction
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

noncomputable section

namespace Langlands.RankinSelberg.InducedTailSmallerRank

open GeneralLinear Whittaker HarmonicAnalysis MeasureTheory
open scoped Topology

universe uF uV₁ uV₂ uW

variable {F : Type uF} [Field F]

@[simp] theorem reindex_finCongr_apply {m n : ℕ} (h : m = n)
    (g : Langlands.GeneralLinear m F) (i j : Fin n) :
    GeneralLinear.reindex (finCongr h) g i j =
      g ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ := rfl

@[simp] theorem reindex_finCongr_self {n : ℕ} (h : n = n)
    (g : Langlands.GeneralLinear n F) :
    GeneralLinear.reindex (finCongr h) g = g := by
  apply Units.ext
  ext i j
  rfl

theorem det_reindex_finCongr {m n : ℕ} (h : m = n)
    (g : Langlands.GeneralLinear m F) :
    Matrix.det (GeneralLinear.reindex (finCongr h) g).val = Matrix.det g.val := by
  subst n
  rw [reindex_finCongr_self]

theorem reindex_appendIdentity_congr {r n d d' : ℕ} (hd : d = d')
    (hr : n + d + 1 = r + 1) (hr' : n + d' + 1 = r + 1)
    (g : Langlands.GeneralLinear (n + 1) F) :
    GeneralLinear.reindex (finCongr hr) (appendIdentity n d g) =
      GeneralLinear.reindex (finCongr hr') (appendIdentity n d' g) := by
  subst d'
  rfl

theorem appendIdentity_append (n d e : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    GeneralLinear.reindex (finCongr (by omega : n + d + e + 1 = n + (d + e) + 1))
      (appendIdentity (n + d) e (appendIdentity n d g)) =
        appendIdentity n (d + e) g := by
  apply Units.ext
  ext i j
  change appendIdentity (n + d) e (appendIdentity n d g)
    ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ = _
  simp only [appendIdentity_entry]
  split_ifs <;> simp_all <;> omega

theorem lastRow_appendIdentity (n d : ℕ) (hd : 0 < d)
    (g : Langlands.GeneralLinear (n + 1) F) :
    lastRow (appendIdentity n d g) =
      fun j => if j = Fin.last (n + d) then 1 else 0 := by
  funext j
  rw [lastRow, appendIdentity_entry]
  have hlast : ¬ (Fin.last (n + d)).val < n + 1 := by simp; omega
  simp only [dite_eq_right hlast]
  simp [eq_comm]

theorem exists_schwartzBruhat_one {X : Type uF} [TopologicalSpace X]
    [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] (x : X) :
    ∃ Φ : SchwartzBruhat X, Φ x = 1 := by
  obtain ⟨K, hKc, hK⟩ := exists_compact_mem_nhds x
  obtain ⟨U, hU, hxU, hUK⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp hK
  have hUc : IsCompact U := hKc.of_isClosed_subset hU.isClosed hUK
  exact ⟨Hecke.TestFunction.characteristic hU hUc, by simp [hxU]⟩

theorem appendIdentity_comp_fixed (n b r d₁ d₂ : ℕ)
    (hb : n + d₁ = b) (hr : b + d₂ = r)
    (g : Langlands.GeneralLinear (n + 1) F) :
    GeneralLinear.reindex (finCongr (by omega : b + d₂ + 1 = r + 1))
      (appendIdentity b d₂
        (GeneralLinear.reindex (finCongr (by omega : n + d₁ + 1 = b + 1))
          (appendIdentity n d₁ g))) =
    GeneralLinear.reindex (finCongr (by omega : n + (d₁ + d₂) + 1 = r + 1))
      (appendIdentity n (d₁ + d₂) g) := by
  apply Units.ext
  ext i j
  simp only [reindex_finCongr_apply, appendIdentity_entry]
  split_ifs <;> simp_all <;> omega

theorem lastRow_appendIdentity_fixed (n b d : ℕ)
    (hb : n + d = b) (hd : 0 < d)
    (g : Langlands.GeneralLinear (n + 1) F) :
    lastRow (GeneralLinear.reindex (finCongr (by omega : n + d + 1 = b + 1))
      (appendIdentity n d g)) =
        fun j => if j = Fin.last b then 1 else 0 := by
  subst b
  exact lastRow_appendIdentity n d hd g

variable [TopologicalSpace F]

omit [TopologicalSpace F] in
theorem halfModulus_weight (abv : AbsoluteValue F ℝ)
    {n : ℕ} (k d : ℕ) (g : Langlands.GeneralLinear (n + 1) F) (s : ℂ) :
    (Real.rpow (abv (Matrix.det g.val)) ((d : ℝ) / 2) : ℂ) *
      determinantWeight abv g (s - ((k + d + 1 : ℕ) : ℂ) / 2) =
        determinantWeight abv g (s - ((k + 1 : ℕ) : ℂ) / 2) := by
  have hdet : Matrix.det g.val ≠ 0 := g.det_ne_zero
  have ha : 0 < abv (Matrix.det g.val) := (abv.pos_iff).mpr hdet
  have hp := Complex.ofReal_cpow ha.le ((d : ℝ) / 2)
  change (Real.rpow (abv (Matrix.det g.val)) ((d : ℝ) / 2) : ℂ) = _ at hp
  rw [hp]
  unfold determinantWeight
  rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
  congr 1
  push_cast
  ring

theorem integrand_eq (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (k d : ℕ)
    (W₂ : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W : WhittakerFunctions ψ (n + (0 + (k + d) + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (hres : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (appendIdentity n (0 + (k + d) + 1) g) =
        W₂.val (appendIdentity n (0 + k + 1) g) *
          (Real.rpow (abv (Matrix.det g.val)) ((d : ℝ) / 2) : ℂ))
    (s : ℂ) (x : Matrix (Fin 0) (Fin (n + 1)) F)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv 0 (k + d) W W' s x q =
      unequalRankIntegrand ψ abv 0 k W₂ W' s x q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk, unequalRankMatrix_zero_rows, hres]
    calc
      _ = W₂.val (appendIdentity n (0 + k + 1) g) * W'.val g *
          ((Real.rpow (abv (Matrix.det g.val)) ((d : ℝ) / 2) : ℂ) *
            determinantWeight abv g (s - ((0 + (k + d) + 1 : ℕ) : ℂ) / 2)) := by
              ring
      _ = _ := by
        rw [show (0 + (k + d) + 1 : ℕ) = k + d + 1 from by omega,
          halfModulus_weight]
        simp only [Nat.zero_add]

theorem converges (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (k d : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin 0) (Fin (n + 1)) F))
    (W₂ : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W : WhittakerFunctions ψ (n + (0 + (k + d) + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (hres : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (appendIdentity n (0 + (k + d) + 1) g) =
        W₂.val (appendIdentity n (0 + k + 1) g) *
          (Real.rpow (abv (Matrix.det g.val)) ((d : ℝ) / 2) : ℂ))
    (s : ℂ) :
    UnequalRankConverges ψ abv 0 (k + d) μ ν W W' s ↔
      UnequalRankConverges ψ abv 0 k μ ν W₂ W' s := by
  unfold UnequalRankConverges
  simp_rw [integrand_eq ψ abv k d W₂ W W' hres]

theorem integral_eq (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {n : ℕ} (k d : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin 0) (Fin (n + 1)) F))
    (W₂ : WhittakerFunctions ψ (n + (0 + k + 1)))
    (W : WhittakerFunctions ψ (n + (0 + (k + d) + 1)))
    (W' : InverseWhittakerFunctions ψ n)
    (hres : ∀ g : Langlands.GeneralLinear (n + 1) F,
      W.val (appendIdentity n (0 + (k + d) + 1) g) =
        W₂.val (appendIdentity n (0 + k + 1) g) *
          (Real.rpow (abv (Matrix.det g.val)) ((d : ℝ) / 2) : ℂ))
    (s : ℂ) :
    unequalRankIntegral ψ abv 0 (k + d) μ ν W W' s =
      unequalRankIntegral ψ abv 0 k μ ν W₂ W' s := by
  unfold unequalRankIntegral
  simp_rw [integrand_eq ψ abv k d W₂ W W' hres]

/-- Transfer the actual rational-value sets, retaining both literal gap indices
until after their rank transports have been eliminated. -/
theorem values_subset (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) {r b n k l d : ℕ}
    (hb : b = n + (0 + k + 1)) (hr : r = n + (0 + l + 1)) (hl : l = k + d)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [MeasurableSpace (Matrix (Fin 0) (Fin (n + 1)) F)]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {V₂ : Type*} [AddCommGroup V₂] [Module ℂ V₂]
    {V' : Type*} [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (π₂ : Representation ℂ (Langlands.GeneralLinear (b + 1) F) V₂)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V')
    (μ : Measure (LeftUnipotentQuotient n F))
    (ν : Measure (Matrix (Fin 0) (Fin (n + 1)) F))
    (hext : ∀ W₂ ∈ whittakerSet ψ b π₂,
      ∃ W ∈ whittakerSet ψ r π,
        ∀ g : Langlands.GeneralLinear (n + 1) F,
          W.val (GeneralLinear.reindex (finCongr (by omega))
            (appendIdentity n (0 + l + 1) g)) =
          W₂.val (GeneralLinear.reindex (finCongr (by omega))
            (appendIdentity n (0 + k + 1) g)) *
            (Real.rpow (abv (Matrix.det g.val)) ((d : ℝ) / 2) : ℂ)) :
    unequalRankZetaValuesAt 0 k hb q ψ abv μ ν π₂ σ ⊆
      unequalRankZetaValuesAt 0 l hr q ψ abv μ ν π σ := by
  subst b
  subst r
  subst l
  simp_rw [reindex_finCongr_self] at hext
  change unequalRankZetaValues q ψ abv 0 k μ ν π₂ σ ⊆
    unequalRankZetaValues q ψ abv 0 (k + d) μ ν π σ
  rintro R ⟨W₂, hW₂, W', hW', hc, hR⟩
  obtain ⟨W, hW, hres⟩ := hext W₂ hW₂
  refine ⟨W, hW, W', hW', ?_, ?_⟩
  · obtain ⟨a, ha⟩ := hc
    exact ⟨a, fun s hs => (converges ψ abv k d μ ν W₂ W W' hres s).2 (ha s hs)⟩
  · apply RationalContinuationLinear.continuation_of_eq_on_right hR
    exact ⟨0, fun s _ => integral_eq ψ abv k d μ ν W₂ W W' hres s⟩

end Langlands.RankinSelberg.InducedTailSmallerRank

namespace Langlands.RankinSelberg

open GeneralLinear Whittaker HarmonicAnalysis MeasureTheory QuotientIntegration

universe uF uV₁ uV₂ uW

set_option maxHeartbeats 400000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- Assemble the smaller-test-rank span inclusion from the two-block
Whittaker extension formula. -/
theorem inducedTailSmallerRankSpan_of_extension
    (hext : TwoBlockWhittakerExtensionStatement.{uF, uV₁, uV₂}) :
    InducedTailSmallerRankSpanStatement.{uF, uV₁, uV₂, uW} := by
  intro p hp F ψ ν a b t V₁ _ _ V₂ _ _ W _ _ π₁ π₂ σ hπ₁ hπ₂ hσ π₁' π₂' ξ h
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  dsimp only
  intro _ μtail μfull htail hfull
  have hm : μfull = μtail :=
    (unipotentQuotientHaar_unique F.Carrier t μfull hfull).trans
      (unipotentQuotientHaar_unique F.Carrier t μtail htail).symm
  subst μfull
  obtain ⟨Φ, hΦ⟩ := InducedTailSmallerRank.exists_schwartzBruhat_one
    (fun j : Fin (b + 1) => if j = Fin.last b then (1 : F.Carrier) else 0)
  apply zetaSpan_mono
  apply InducedTailSmallerRank.values_subset
    F.canonicalTopologicalData.residueCardinality ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (r := a + 1 + b) (b := b) (n := t)
    (k := b - t - 1) (l := a + 1 + b - t - 1) (d := a + 1)
    (by omega) (by omega) (by omega) ξ π₂ σ μtail
    (rectangularMeasure ν.val 0 (t + 1))
  intro W₂ hW₂
  obtain ⟨Wfull, hWfull, hWg⟩ :=
    hext p F ψ a b π₁ π₂ hπ₁ hπ₂ W₂ hW₂ Φ
  refine ⟨Wfull, hWfull, ?_⟩
  intro g
  have hg := hWg (GeneralLinear.reindex
    (finCongr (by omega : t + (0 + (b - t - 1) + 1) + 1 = b + 1))
    (appendIdentity t (0 + (b - t - 1) + 1) g))
  rw [InducedTailSmallerRank.appendIdentity_comp_fixed
      t b (a + 1 + b) (0 + (b - t - 1) + 1) (a + 1) (by omega) (by omega),
    InducedTailSmallerRank.reindex_appendIdentity_congr
      (show (0 + (b - t - 1) + 1) + (a + 1) =
        0 + (a + 1 + b - t - 1) + 1 by omega) _ (by omega),
    InducedTailSmallerRank.lastRow_appendIdentity_fixed
      t b (0 + (b - t - 1) + 1) (by omega) (by omega),
    hΦ, mul_one, InducedTailSmallerRank.det_reindex_finCongr, det_appendIdentity] at hg
  simpa only [normalizedAbsoluteValue_apply] using hg

/-- The tail's actual zero-row Laurent span is contained in that of the
canonical normalized upper induction when the test rank is smaller. -/
theorem inducedTailSmallerRankSpan :
    InducedTailSmallerRankSpanStatement.{uF, uV₁, uV₂, uW} :=
  inducedTailSmallerRankSpan_of_extension twoBlockWhittakerExtension

end Langlands.RankinSelberg
