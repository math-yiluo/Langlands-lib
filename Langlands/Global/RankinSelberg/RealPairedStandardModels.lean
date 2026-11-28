import Langlands.Global.RankinSelberg.RealExactWhittakerUniqueness
import Langlands.Global.RankinSelberg.RealOrdinaryTestExtraction
import Langlands.Global.RankinSelberg.RealPairedModelGrowth
import Langlands.Global.RankinSelberg.RealStandardBlockSublist

/-! # Genuine paired smooth tests of real standard modules -/

noncomputable section

open MeasureTheory Langlands.Archimedean Langlands.LocalFactor.Archimedean
open scoped ContDiff Manifold Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option quotPrecheck false

namespace Langlands.Global.RankinSelbergGlobal.RealPairedStandardModels

open ArchimedeanLocal CompletedProjectiveRepresentation RealStandardCompactBanach
open RealPairedRankRaising RealPaddedExponential
open RealPaddedWhittakerProduct (oppositeScale realPaddedWhittakerProduct)
open RealPairedSmoothRowAbsorption (slot unitProjection_slot_self unitProjection_slot_of_ne)
open RealExactBlockStandardEvaluation (realExactBlockStandardEvaluation)
open RealExactWhittakerUniqueness (realWhittakerModel_eq_range)
open RealOrdinaryTestExtraction (smoothOfCompact)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealLocalJacquet (dualBlock)

attribute [local instance] archimedeanRealGLMeasurable archimedeanRealGLBorel
  archimedeanRealNMeasurable archimedeanRealNBorel archimedeanRealQMeasurable archimedeanRealQBorel

private local instance (n : ℕ) (ds : List RealBlock) : NormedAddCommGroup (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) : NormedSpace ℂ (Carrier n ds) :=
  (closureSubmodule (n := n) ds).normedSpace

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℝ
local notation "N" => fun r => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Mat" => fun r : ℕ => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Row" => fun r : ℕ => Fin (r + 1) → ℝ

/-- The two inducing lists in their specified order. -/
abbrev pairLists (ds es : List RealBlock) : Fin 2 → List RealBlock := Fin.cases ds (fun _ => es)

/-- The individual Banach carriers used to form the completed projective product. -/
abbrev slotCarrier (n : Fin 2 → ℕ) (ds : Fin 2 → List RealBlock) (i : Fin 2) :=
  Carrier (n i + 1) (ds i)

/-- The two genuine standard Banach actions. -/
abbrev slotRepresentation (n : Fin 2 → ℕ) (ds : Fin 2 → List RealBlock) (i : Fin 2) :
    G (n i) →* (slotCarrier n ds i →L[ℂ] slotCarrier n ds i) :=
  RealStandardCompactBanach.representation (n := n i + 1) (ds i)

/-- The genuine smooth vectors in the individual standard carriers. -/
abbrev SlotSmooth (n : Fin 2 → ℕ) (ds : Fin 2 → List RealBlock) (i : Fin 2) :=
  DerivativeSmoothVectors 𝓘(ℝ, Mat (n i)) (slotRepresentation n ds i)

/-- The genuine product-group smooth vectors of the two standard carriers. -/
abbrev PairSmooth (n : Fin 2 → ℕ) (ds : Fin 2 → List RealBlock) :=
  DerivativeSmoothVectors 𝓘(ℝ, (∀ i : Fin 2, Mat (n i)))
    (productAction (fun i => Mat (n i)) (slotRepresentation n ds))

variable (n : Fin 2 → ℕ) (ds : Fin 2 → List RealBlock)

local notation "A" => fun i => Mat (n i)
local notation "Alg" => (∀ i : Fin 2, A i)
local notation "I" => 𝓘(ℝ, Alg)
local notation "ρ₀" => slotRepresentation n ds
local notation "D" => PairSmooth n ds
local notation "D₀" => SlotSmooth n ds
local notation "P" => productAction A ρ₀
local notation "act" => DerivativeSmoothVectors.representation I P
local notation "CF" => fun i => Automorphic.realStandardKFinite (n i + 1) (ds i)
local notation "src" => fun i => smoothOfCompact (ds i)
local notation "pad" => fun m (hm : ∀ i, m ≤ n i) =>
  padProductGL (fun i => n i + 1) (fun i => Nat.succ_le_succ (hm i))

private local instance : ChartedSpace Alg Algˣ :=
  (Units.isOpenEmbedding_val (R := Alg)).singletonChartedSpace

/-- A compact-finite pair read in the genuine product-group smooth space. -/
abbrev pairedCompactVector (f : ∀ i, CF i) : D :=
  pureSmooth A ρ₀ (fun i => src i (f i))

/-- The scalar pair form agrees with the individual forms on pure vectors and carries their
opposite unipotent characters in the respective slots. It is invariant under simultaneous
leading padding of a common unipotent. -/
def IsPairedStandardForm (a : ℝˣ) (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ) : Prop :=
  (∀ v : ∀ i, D₀ i, T (pureSmooth A ρ₀ v) = ∏ i, L i (v i)) ∧
  (∀ (i : Fin 2) (u : N (n i)) (v : D), T (act (slot n i u.val) v) =
    realWhittakerCharacter (oppositeScale a i) u.val * T v) ∧
  ∀ (m : ℕ) (hm : ∀ i, m ≤ n i) (u : N m) (v : D), T (act (pad m hm u.val) v) = T v

/-- Every rank-correct real standard pair has genuine smooth evaluations realizing the
whole compact-finite coefficient models and a paired form with the opposite scales. -/
def RealPairedStandardModelsStatement : Prop :=
  (∀ i, realRank (ds i) = n i + 1) → ∀ a : ℝˣ,
    ∃ (B : ∀ i, CF i →ₗ[ℂ] (G (n i) → ℂ)) (L : ∀ i, D₀ i →L[ℂ] ℂ) (T : D →L[ℂ] ℂ),
      (∀ i, IsRealWhittakerIntertwiner (n i) (ds i) (oppositeScale a i) (B i) ∧
        IsWhittakerStandardEvaluation (ds i) (oppositeScale a i) (B i) (L i) ∧ (L i) ≠ 0 ∧
        realWhittakerModel (n i) (ds i) (oppositeScale a i) = (B i).range) ∧
      IsPairedStandardForm n ds a L T

private theorem character_one (r : ℕ) (a : ℝˣ) : realWhittakerCharacter a (1 : G r) = 1 :=
  congrArg Units.val ((Langlands.Whittaker.standardCharacter (realScaledCharacter a) r).map_one)

set_option maxHeartbeats 850000 in
theorem realPairedStandardModels : RealPairedStandardModelsStatement n ds := by
  intro hd a
  choose B hB hBn using fun i => realExactBlockWhittakerNonzero (n i) (ds i) (hd i) (oppositeScale a i)
  choose L hL using fun i => realExactBlockStandardEvaluation (n i) (ds i) (hd i)
    (oppositeScale a i) (B i) (hB i)
  have hR (i : Fin 2) : IsContinuousRepresentation (ρ₀ i) := isContinuousRepresentation (ds i)
  obtain ⟨T, hT, hCov, hInv⟩ := realPaddedWhittakerProduct n (slotCarrier n ds) ρ₀ hR a L (fun i => (hL i).2)
  refine ⟨B, L, T, fun i => ⟨hB i, hL i, ?_, ?_⟩, hT, ?_, hInv⟩
  · intro he
    apply hBn i
    apply LinearMap.ext
    intro f
    funext g
    rw [← (hL i).1 f g, he]
    rfl
  · exact realWhittakerModel_eq_range (ds i) (hd i) (oppositeScale a i) (B i) (hB i) (hBn i)
  · intro i u v
    have hU (j : Fin 2) : unitProjection A j (slot n i u.val) ∈ N (n j) := by
      by_cases hj : j = i
      · subst j
        rw [unitProjection_slot_self]
        exact u.property
      · rw [unitProjection_slot_of_ne n hj]
        exact (N (n j)).one_mem
    rw [hCov _ hU, Finset.prod_eq_single i]
    · rw [unitProjection_slot_self]
    · intro j _ hj
      rw [unitProjection_slot_of_ne n hj, character_one]
    · simp

/-- The pure compact-finite pairs are dense after taking their linear span in the full
product-group smooth topology. -/
theorem dense_span_pairedCompactVector :
    Dense (Submodule.span ℂ (Set.range (pairedCompactVector n ds)) : Set D) := by
  exact smoothProjectiveProductSources A ρ₀ (fun i => isContinuousRepresentation (ds i)) CF src
    (fun i => denseRange_compactFiniteEquiv (ds i))

/-- At every group element each compact-finite source has the specified scalar coefficient. -/
theorem slotCoefficient_of_compact (a : ℝˣ) (B : ∀ i, CF i →ₗ[ℂ] (G (n i) → ℂ))
    (L : ∀ i, D₀ i →L[ℂ] ℂ)
    (hL : ∀ i, IsWhittakerStandardEvaluation (ds i) (oppositeScale a i) (B i) (L i))
    (f : ∀ i, CF i) (i : Fin 2) : slotCoefficient n ρ₀ L (fun j => src j (f j)) i = B i (f i) :=
  funext ((hL i).1 (f i))

section Growth

variable (r t : ℕ) (xs ys : List RealBlock)

local notation "ranks" => pairRanks r t
local notation "blocks" => pairLists xs ys
local notation "Dpair" => PairSmooth ranks blocks
local notation "CFin" => fun i => Automorphic.realStandardKFinite (ranks i + 1) (blocks i)
local notation "Emb" => fun i => smoothOfCompact (blocks i)
local notation "Epair" => slotCarrier ranks blocks
local notation "Rpair" => slotRepresentation ranks blocks
local notation "Lpair" => fun i => SlotSmooth ranks blocks i →L[ℂ] ℂ
local notation "dSign" => fun xs : List RealBlock => (RealJacquet.determinant xs (-1) : ℂ)

private theorem compact_mem_models (a : ℝˣ) (B : ∀ i, CFin i →ₗ[ℂ] (G (ranks i) → ℂ))
    (L : ∀ i, Lpair i)
    (hB : ∀ i, IsRealWhittakerIntertwiner (ranks i) (blocks i) (oppositeScale a i) (B i))
    (hL : ∀ i, IsWhittakerStandardEvaluation (blocks i) (oppositeScale a i) (B i) (L i))
    (f : ∀ i, CFin i) (i : Fin 2) :
    slotCoefficient ranks Rpair L (fun j => Emb j (f j)) i ∈
      realWhittakerModel (ranks i) (blocks i) (oppositeScale a i) := by
  rw [slotCoefficient_of_compact ranks blocks a B L hL f i]
  exact (RealOrdinaryTestExtraction.coefficient (B i) (hB i) (f i)).property

set_option maxHeartbeats 950000 in
/-- The paired normalized growth theorem on the genuine smooth space of two unequal
rank real standard models, assuming entire ordinary continuation on their exact tests. -/
theorem realPairedStandardUnequalGrowth (hO : RealOrdinaryNormalizedContinuationStatement)
    (h : t < r) (hx : realRank xs = r + 1) (hy : realRank ys = t + 1) (a : ℝˣ)
    (μ : RealQuotientMeasureData t) (hm : ∀ i, t ≤ ranks i)
    (B : ∀ i, CFin i →ₗ[ℂ] (G (ranks i) → ℂ)) (L : ∀ i, Lpair i) (T : Dpair →L[ℂ] ℂ)
    (hB : ∀ i, IsRealWhittakerIntertwiner (ranks i) (blocks i) (oppositeScale a i) (B i))
    (hL : ∀ i, IsWhittakerStandardEvaluation (blocks i) (oppositeScale a i) (B i) (L i))
    (hT : IsPairedStandardForm ranks blocks a L T) :
    ∀ v : Dpair, HasRealPairNormalizedGrowth xs ys (xs.map dualBlock) (ys.map dualBlock) (-a)
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((dSign xs) ^ (t + 1) * dSign ys) (ordinaryPaddedPairIntegral ranks Epair Rpair t hm μ T (v, none))
      (fun s => ∫ p, unequalPairedDualKernel r t Epair Rpair h T v s p ∂(realUnequalDualMeasure (r := r) a μ)) := by
  apply realPairedUnequalModelGrowth r t Epair Rpair hO (fun i => isContinuousRepresentation (blocks i))
    h hm a μ L T hT.1 hT.2.1 (hT.2.2 t hm) xs ys hx hy CFin Emb
    (fun i => denseRange_compactFiniteEquiv (blocks i))
  intro f
  have hzero := compact_mem_models r t xs ys a B L hB hL f 0
  have hone := compact_mem_models r t xs ys a B L hB hL f 1
  rw [show oppositeScale a 0 = a from rfl] at hzero
  rw [show oppositeScale a 1 = -a from rfl] at hone
  exact ⟨hzero, hone⟩

variable (m : ℕ)

local notation "rr" => pairRanks m m
local notation "EE" => slotCarrier rr blocks
local notation "RR" => slotRepresentation rr blocks
local notation "DD" => PairSmooth rr blocks
local notation "FF" => fun i => Automorphic.realStandardKFinite (rr i + 1) (blocks i)

set_option maxHeartbeats 950000 in
/-- The corresponding normalized pair in equal ranks, with the given Schwartz row and
its exact Fourier transform in the reflected integral. -/
theorem realPairedStandardEqualGrowth (hO : RealOrdinaryNormalizedContinuationStatement)
    (hx : realRank xs = m + 1) (hy : realRank ys = m + 1) (a : ℝˣ) (μ : RealQuotientMeasureData m)
    (hm : ∀ i, m ≤ rr i) (B : ∀ i, FF i →ₗ[ℂ] (G (rr i) → ℂ))
    (L : ∀ i, SlotSmooth rr blocks i →L[ℂ] ℂ) (T : DD →L[ℂ] ℂ)
    (hB : ∀ i, IsRealWhittakerIntertwiner (rr i) (blocks i) (oppositeScale a i) (B i))
    (hL : ∀ i, IsWhittakerStandardEvaluation (blocks i) (oppositeScale a i) (B i) (L i))
    (hT : IsPairedStandardForm rr blocks a L T) (Φ : 𝓢(Row m, ℂ)) :
    ∀ v : DD, HasRealPairNormalizedGrowth xs ys (xs.map dualBlock) (ys.map dualBlock) (-a)
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero)) ((dSign xs) ^ m)
      (ordinaryPaddedPairIntegral rr EE RR m hm μ T (v, some Φ))
      (fun s => ∫ q, equalPairedDualKernel m EE RR (-a) T v Φ s q ∂μ.measure) := by
  apply realPairedEqualModelGrowth m EE RR hO (fun i => isContinuousRepresentation (blocks i))
    hm a μ L T hT.1 hT.2.1 (hT.2.2 m hm) xs ys hx hy FF (fun i => smoothOfCompact (blocks i))
    (fun i => denseRange_compactFiniteEquiv (blocks i)) _ Φ
  intro f
  have hzero := compact_mem_models m m xs ys a B L hB hL f 0
  have hone := compact_mem_models m m xs ys a B L hB hL f 1
  rw [show oppositeScale a 0 = a from rfl] at hzero
  rw [show oppositeScale a 1 = -a from rfl] at hone
  exact ⟨hzero, hone⟩

end Growth

end Langlands.Global.RankinSelbergGlobal.RealPairedStandardModels
