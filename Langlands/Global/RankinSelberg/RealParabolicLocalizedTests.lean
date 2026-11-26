import Langlands.Analysis.CompactWeightedTestPullback
import Langlands.Analysis.LocalSmoothCutoff
import Langlands.Global.RankinSelberg.RealParabolicStandardSection
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Continuous compact test realizations of real parabolic sections -/

noncomputable section

open Filter Matrix Set TopologicalSpace
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.Analysis Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean
open Langlands.Shahidi (blockWeyl swapRank)

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "M" => fun n => Matrix (Fin n) (Fin n) ℝ
local notation "X" => fun m n => Matrix (Fin m) (Fin n) ℝ

variable {m n : ℕ}

private def submatrixCLM {d r s : ℕ} (i : Fin r → Fin d) (j : Fin s → Fin d) :
    M d →L[ℝ] X r s :=
  (show M d →ₗ[ℝ] X r s from {
    toFun := fun A => A.submatrix i j
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }).toContinuousLinearMap

private def shuffledMatrix : M (n + m) →L[ℝ] M (m + n) :=
  ((LinearMap.mulLeft ℝ (blockWeyl m n ℝ).val).toContinuousLinearMap).comp
    (submatrixCLM (finCongr (Nat.add_comm m n)) (finCongr (Nat.add_comm m n)))

private theorem shuffledMatrix_val (u : G (n + m)) : shuffledMatrix u.val =
    (blockWeyl m n ℝ * swapRank m n ℝ u).val := rfl

private def pivot : M (n + m) →L[ℝ] M m :=
  (submatrixCLM (fun i : Fin m => i.castAdd n) (fun j : Fin m => j.castAdd n)).comp shuffledMatrix

private def upperRight : M (n + m) →L[ℝ] X m n :=
  (submatrixCLM (fun i : Fin m => i.castAdd n) (fun j : Fin n => j.natAdd m)).comp shuffledMatrix

private def pivotDomain (m n : ℕ) : Set (M (n + m)) :=
  {u | IsUnit (pivot (m := m) (n := n) u)}

private theorem isOpen_pivotDomain : IsOpen (pivotDomain m n) :=
  isOpen_setOf_isUnit_matrix.preimage (pivot (m := m) (n := n)).continuous

private theorem mem_pivotDomain_iff (u : G (n + m)) :
    u.val ∈ pivotDomain m n ↔ blockWeyl m n ℝ * swapRank m n ℝ u ∈ parabolicCell m n :=
  (Matrix.isUnit_iff_isUnit_det _).trans isUnit_iff_ne_zero

private def rectangleCoordinate (u : M (n + m)) : X m n := Ring.inverse (pivot u) * upperRight u

private theorem contDiffOn_rectangleCoordinate : ContDiffOn ℝ ∞ (rectangleCoordinate (m := m) (n := n))
    (pivotDomain m n) := by
  intro u hu
  have hu' : IsUnit (pivot (m := m) (n := n) u) := hu
  have hInv : ContDiffAt ℝ ∞ Ring.inverse (pivot u) := by
    rw [← hu'.unit_spec]
    exact contDiffAt_ringInverse ℝ hu'.unit
  have hP := hInv.comp u (pivot (m := m) (n := n)).contDiff.contDiffAt
  have hB : ContDiffAt ℝ ∞ (upperRight (m := m) (n := n)) u := upperRight.contDiff.contDiffAt
  let assemble : (Fin m → Fin n → ℝ) →L[ℝ] X m n :=
    (Matrix.ofLinearEquiv ℝ).toLinearMap.toContinuousLinearMap
  have h : ContDiffAt ℝ ∞ (fun A : M (n + m) => fun i j => rectangleCoordinate A i j) u := by
    apply contDiffAt_pi.mpr
    intro i
    apply contDiffAt_pi.mpr
    intro j
    simp only [rectangleCoordinate, Matrix.mul_apply]
    exact ContDiffAt.sum fun k _ =>
      ((Matrix.entryLinearMap ℝ ℝ i k).toContinuousLinearMap.contDiff.contDiffAt.comp u hP).mul
        ((Matrix.entryLinearMap ℝ ℝ k j).toContinuousLinearMap.contDiff.contDiffAt.comp u hB)
  exact (assemble.contDiff.contDiffAt.comp u h).contDiffWithinAt

private theorem rectangleCoordinate_of_split (u : G (n + m)) (a : G m) (b : G n)
    (C : X n m) (Y : X m n)
    (h : split (blockWeyl m n ℝ * swapRank m n ℝ u).val =
      Matrix.fromBlocks a.val (a.val * Y) C (C * Y + b.val)) : rectangleCoordinate u.val = Y := by
  have hA : pivot u.val = a.val := by
    change (split (shuffledMatrix u.val)).toBlocks₁₁ = _
    rw [shuffledMatrix_val, h, Matrix.toBlocks_fromBlocks₁₁]
  have hB : upperRight u.val = a.val * Y := by
    change (split (shuffledMatrix u.val)).toBlocks₁₂ = _
    rw [shuffledMatrix_val, h, Matrix.toBlocks_fromBlocks₁₂]
  rw [rectangleCoordinate, hA, hB, Ring.inverse_unit, ← Matrix.mul_assoc]
  rw [show a⁻¹.val * a.val = 1 from a.inv_val, Matrix.one_mul]

private theorem exists_transverseBump (L : Compacts (X m n)) :
    ∃ b : X m n → ℂ, ContDiff ℝ ∞ b ∧ HasCompactSupport b ∧ ∀ Y ∈ L, b Y = 1 := by
  obtain ⟨A, hA⟩ := L.isCompact.exists_bound_of_continuousOn
    (continuous_id : Continuous (id : X m n → X m n)).continuousOn
  let r := max A 0 + 1
  let b : ContDiffBump (0 : X m n) := ⟨r, r + 1, by dsimp [r]; positivity, by linarith⟩
  refine ⟨fun Y => (b Y : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, ?_⟩
  intro Y hY
  have hy : Y ∈ Metric.closedBall (0 : X m n) b.rIn := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hA Y hY).trans ((le_max_left A 0).trans (le_add_of_nonneg_right zero_le_one))
  simp [b.one_of_mem_closedBall hy]

private theorem standardSection_factor {f : G m → ℂ} {g : G n → ℂ}
    (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (L : Compacts (X m n))
    (bump : X m n → ℂ) (hb : ContDiff ℝ ∞ bump) (hbC : HasCompactSupport bump)
    (hb₁ : ∀ Y ∈ L, bump Y = 1) (φ : 𝓓_{L}(X m n, ℂ)) (u : G (n + m)) :
    standardSection f g bump u * φ (rectangleCoordinate u.val) = standardSection f g φ u := by
  let v := blockWeyl m n ℝ * swapRank m n ℝ u
  by_cases hv : v ∈ parabolicCell m n
  · obtain ⟨a, b, C, Y, hY⟩ := exists_cellCoordinates v hv
    unfold standardSection
    rw [(realParabolicCompactSection m n _ _ f g bump hf hg hb hbC).2.2 v _ _ _ _ hY,
      (realParabolicCompactSection m n _ _ f g φ hf hg φ.contDiff φ.hasCompactSupport).2.2 v _ _ _ _ hY,
      rectangleCoordinate_of_split u _ _ _ _ hY]
    by_cases hL : Y ∈ L
    · rw [hb₁ Y hL, mul_one]
    · simp [φ.zero_on_compl hL]
  · simp [standardSection, compactSection, ← show v = blockWeyl m n ℝ * swapRank m n ℝ u from rfl, hv]

private theorem localizedTest_exists {d₁ d₂ : List RealBlock} (hm : realRank d₁ = m)
    (hn : realRank d₂ = n) {f : G m → ℂ} {g : G n → ℂ}
    (hf : f ∈ realStandardModule m d₁) (hg : g ∈ realStandardModule n d₂)
    (K : Compacts (M (n + m))) (hK : ∀ x ∈ (K : Set (M (n + m))), IsUnit x)
    (L : Compacts (X m n)) (η : M (n + m) → ℂ) (hη : ContDiff ℝ ∞ η) (hηK : tsupport η ⊆ K) :
    ∃ P : 𝓓_{L}(X m n, ℂ) →L[ℂ] 𝓓_{K}(M (n + m), ℂ),
      ∀ (φ : 𝓓_{L}(X m n, ℂ)) (u : G (n + m)), P φ u.val = η u.val * standardSection f g φ u := by
  obtain ⟨bump, hb, hbC, hb₁⟩ := exists_transverseBump L
  let W := unitsExtension (standardSection f g bump)
  have hW : ContDiffOn ℝ ∞ W {x | IsUnit x} := contDiffOn_unitsExtension
    (realParabolicStandardSection m n d₁ d₂ hm hn f g hf hg bump hb hbC).1.1
  have hWcell (u : G (n + m)) (hu : u.val ∈ tsupport W) : u.val ∈ pivotDomain m n := by
    by_contra hnot
    let S := tsupport (compactSection (-(n : ℂ) / 2) ((m : ℂ) / 2) f g bump)
    have hS : S ⊆ parabolicCell m n :=
      (realParabolicCompactSection m n _ _ f g bump hf.1.1 hg.1.1 hb hbC).2.1
    let τ (v : G (n + m)) := blockWeyl m n ℝ * swapRank m n ℝ v
    have hτ : Continuous τ := continuous_const.mul
      (GeneralLinear.reindexContinuous (R := ℝ) (finCongr (Nat.add_comm n m))).continuous
    let U := Units.val '' (τ ⁻¹' Sᶜ)
    have hU : IsOpen U := Units.isOpenEmbedding_val.isOpenMap _ (isClosed_closure.isOpen_compl.preimage hτ)
    have hsub : Function.support W ⊆ Uᶜ := by
      rintro x hx ⟨v, hv, rfl⟩
      apply hx
      rw [show W v.val = standardSection f g bump v from unitsExtension_val _ v]
      change compactSection (-(n : ℂ) / 2) ((m : ℂ) / 2) f g bump (τ v) = 0
      exact image_eq_zero_of_notMem_tsupport (show τ v ∉ S from hv)
    exact (closure_minimal hsub hU.isClosed_compl hu)
      ⟨u, fun h => hnot ((mem_pivotDomain_iff u).mpr (hS h)), rfl⟩
  let w := η * W
  have hw : ContDiff ℝ ∞ w := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ (K : Set (M (n + m)))
    · exact hη.contDiffAt.mul (hW.contDiffAt (isOpen_setOf_isUnit_matrix.mem_nhds (hK x hx)))
    · apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [K.isCompact.isClosed.isOpen_compl.mem_nhds hx] with y hy
      change η y * W y = 0
      rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hηK h)), zero_mul]
  have hwK : tsupport w ⊆ K := tsupport_mul_subset_left.trans hηK
  have hcut : (K : Set (M (n + m))) ∩ tsupport W ⊆ pivotDomain m n := by
    rintro x ⟨hxK, hxW⟩
    obtain ⟨u, rfl⟩ := hK x hxK
    exact hWcell u hxW
  obtain ⟨α, _, hα, _, hP⟩ := exists_contDiff_cutoff_smul isOpen_pivotDomain
    (K.isCompact.inter_right isClosed_closure) hcut contDiffOn_rectangleCoordinate
  let p (x : M (n + m)) := α x • rectangleCoordinate x
  refine ⟨compactWeightedTestPullback K L p w hP hw hwK, fun φ u => ?_⟩
  rw [compactWeightedTestPullback_apply]
  have hWv : W u.val = standardSection f g bump u := unitsExtension_val _ _
  have heq := standardSection_factor hf.1.1 hg.1.1 L bump hb hbC hb₁ φ u
  rw [← heq, ← hWv]
  change η u.val * W u.val * φ (p u.val) = η u.val * (W u.val * φ (rectangleCoordinate u.val))
  by_cases hxK : u.val ∈ (K : Set (M (n + m)))
  · by_cases hxW : u.val ∈ tsupport W
    · have hp : p u.val = rectangleCoordinate u.val := by
        change α u.val • rectangleCoordinate u.val = _
        rw [hα ⟨hxK, hxW⟩, Pi.one_apply, one_smul]
      rw [hp, mul_assoc]
    · rw [image_eq_zero_of_notMem_tsupport hxW, mul_zero, zero_mul, zero_mul, mul_zero]
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hxK (hηK h)), zero_mul, zero_mul, zero_mul]

/-- Multiplying a compact parabolic standard section by a fixed ambient cutoff yields a
continuous linear map from tests of fixed transverse support to tests of fixed ambient support. -/
def RealParabolicLocalizedTestsStatement : Prop :=
  ∀ (m n : ℕ) (d₁ d₂ : List RealBlock), realRank d₁ = m → realRank d₂ = n →
    ∀ (f : G m → ℂ) (g : G n → ℂ), f ∈ realStandardModule m d₁ → g ∈ realStandardModule n d₂ →
    ∀ (K : Compacts (M (n + m))), (∀ x ∈ (K : Set (M (n + m))), IsUnit x) →
    ∀ (L : Compacts (X m n)) (η : M (n + m) → ℂ), ContDiff ℝ ∞ η → tsupport η ⊆ K →
      ∃ P : 𝓓_{L}(X m n, ℂ) →L[ℂ] 𝓓_{K}(M (n + m), ℂ),
        ∀ (φ : 𝓓_{L}(X m n, ℂ)) (u : G (n + m)), P φ u.val = η u.val * standardSection f g φ u

theorem realParabolicLocalizedTests : RealParabolicLocalizedTestsStatement := by
  intro m n d₁ d₂ hm hn f g hf hg K hK L η hη hηK
  exact localizedTest_exists hm hn hf hg K hK L η hη hηK

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection
