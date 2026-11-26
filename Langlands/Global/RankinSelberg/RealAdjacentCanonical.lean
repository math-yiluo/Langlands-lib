import Langlands.Global.RankinSelberg.RealAdjacentCanonicalChamber
import Langlands.Global.RankinSelberg.RealUnequalCanonicalReflection
import Langlands.Global.RankinSelberg.RealLocalEqualGrowthStep

/-! # The real normalized adjacent-rank equation at every inducing parameter

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal
open Langlands.Archimedean
open Langlands.Archimedean.GramFormula Langlands.Archimedean.PartialJacquet
open RealGodement (canonicalJacquetMap realSpectralChamber isOpen_realSpectralChamber
  hasRealPairNormalizedGrowth_scale_congr realGodementCanonicalModel)
open RealUnequalFamily (HasRealUnequalCanonicalPairGrowth realUnequalCanonicalGrowthReflection)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

/-! ### The determinant sign of a character list -/

/-- The value at `-1` of a real character datum depends only on its parity. -/
theorem charData_character_neg_one (e : Fin 2) (t t' : ℂ) :
    (RealJacquetFrobenius.charData e t).character (-1) =
      (RealJacquetFrobenius.charData e t').character (-1) := by
  apply Units.ext
  rw [RealJacquetFrobenius.charData_character_apply,
    RealJacquetFrobenius.charData_character_apply]
  simp [RealJacquetFrobenius.charFun]

/-- The determinant sign of a character list depends only on the parities. -/
theorem determinant_characterList_neg_one {n : ℕ} (p : Fin n → Fin 2) (z z' : Fin n → ℂ) :
    determinant (RealGodementProfiles.characterList p z) (-1) =
      determinant (RealGodementProfiles.characterList p z') (-1) := by
  unfold determinant RealGodementProfiles.characterList
  simp only [List.map_ofFn]
  congr 2
  funext i
  exact charData_character_neg_one (p i) (z i) (z' i)

/-! ### Removing the chamber condition -/

theorem cons_mem_realSpectralChamber {n : ℕ} (q : Fin (n + 1) → ℂ)
    (hq : q ∈ realSpectralChamber n) (x : ℂ) (hx : (q 0).re < x.re) :
    (Fin.cons x q : Fin (n + 2) → ℂ) ∈ realSpectralChamber (n + 1) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ] using hx
  · simpa only [Fin.castSucc_succ, Fin.cons_succ] using hq j

/-- A property of inducing exponents that continues along holomorphic families from a small
disk about zero to parameter one, and holds in the strict chamber once the leading real part
exceeds a bound depending on the remaining exponents, holds everywhere. -/
theorem realChamberRemoval {n : ℕ} (A : (Fin (n + 2) → ℂ) → Prop)
    (reflection : ∀ p : ℂ → Fin (n + 2) → ℂ, Differentiable ℂ p →
      (∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ ball 0 δ, A (p z)) → A (p 1))
    (hStrong : ∀ q : Fin (n + 1) → ℂ, ∃ M : ℝ, ∀ Z : Fin (n + 2) → ℂ, Fin.tail Z = q →
      Z ∈ realSpectralChamber (n + 1) → M ≤ (Z 0).re → A Z) :
    ∀ Z, A Z := by
  have hHead (q : Fin (n + 1) → ℂ) (hq : q ∈ realSpectralChamber n) (x : ℂ) :
      A (Fin.cons x q) := by
    obtain ⟨M, hM⟩ := hStrong q
    let x₀ : ℂ := ((max (q 0).re M + 1 : ℝ) : ℂ)
    let u (z : ℂ) : ℂ := x₀ + z * (x - x₀)
    let p (z : ℂ) : Fin (n + 2) → ℂ := Fin.cons (u z) q
    have hu : Differentiable ℂ u := (differentiable_id.mul_const (x - x₀)).const_add x₀
    have hp : Differentiable ℂ p := by
      apply differentiable_pi.mpr
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa only [p, Fin.cons_zero] using hu
      · simpa only [p, Fin.cons_succ] using differentiable_const (q j)
    have hp₁ : p 1 = Fin.cons x q := by simp [p, u, add_comm x₀]
    let S : Set ℂ := {z : ℂ | (q 0).re < (u z).re} ∩ {z : ℂ | M < (u z).re}
    have hS : IsOpen S :=
      (isOpen_lt continuous_const (Complex.continuous_re.comp hu.continuous)).inter
        (isOpen_lt continuous_const (Complex.continuous_re.comp hu.continuous))
    have hz₀ : (0 : ℂ) ∈ S := by
      refine ⟨?_, ?_⟩
      · change (q 0).re < (u 0).re
        simp only [u, zero_mul, add_zero, x₀, Complex.ofReal_re]
        linarith [le_max_left (q 0).re M]
      · change M < (u 0).re
        simp only [u, zero_mul, add_zero, x₀, Complex.ofReal_re]
        linarith [le_max_right (q 0).re M]
    obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS 0 hz₀
    rw [← hp₁]
    refine reflection p hp ⟨δ, hδ, fun z hz => ?_⟩
    have hzS := hδS hz
    apply hM (p z) (by simp only [p, Fin.tail_cons])
      (cons_mem_realSpectralChamber q hq (u z) hzS.1)
    simpa only [p, Fin.cons_zero] using le_of_lt hzS.2
  intro Z
  let p₀ : Fin (n + 2) → ℂ := fun i => -((i : ℕ) : ℂ)
  have hp₀ : Fin.tail p₀ ∈ realSpectralChamber n := by
    intro i
    simp only [Fin.tail, p₀, Complex.neg_re, Fin.val_succ, Fin.val_castSucc, Nat.cast_succ,
      Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith
  let pLine (z : ℂ) : Fin (n + 2) → ℂ := p₀ + z • (Z - p₀)
  have hLine : Differentiable ℂ pLine := (differentiable_id.smul_const (Z - p₀)).const_add p₀
  have hLine₁ : pLine 1 = Z := by simp [pLine, add_comm p₀]
  have hTail : Continuous (Fin.tail : (Fin (n + 2) → ℂ) → Fin (n + 1) → ℂ) :=
    continuous_pi fun i => continuous_apply i.succ
  have hS : IsOpen ((Fin.tail ∘ pLine) ⁻¹' realSpectralChamber n) :=
    (isOpen_realSpectralChamber n).preimage (hTail.comp hLine.continuous)
  have h₀ : (0 : ℂ) ∈ (Fin.tail ∘ pLine) ⁻¹' realSpectralChamber n := by
    simpa only [mem_preimage, Function.comp_apply, pLine, zero_smul, add_zero] using hp₀
  obtain ⟨δ, hδ, hδS⟩ := Metric.isOpen_iff.mp hS 0 h₀
  rw [← hLine₁]
  refine reflection pLine hLine ⟨δ, hδ, fun z hz => ?_⟩
  have h := hHead (Fin.tail (pLine z)) (hδS hz) (pLine z 0)
  rwa [Fin.cons_self_tail] at h

/-! ### The adjacent-rank equation for canonical values -/

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "gap" => Nat.lt_succ_self r

/-- For every inducing parameter, every larger canonical value satisfies the normalized
adjacent-rank equation with strip growth against every value of a smaller uniform Whittaker map,
given compact projection and the equal-rank growth at the smaller rank. -/
theorem realAdjacentCanonicalGrowth (hProjO : RealOrthogonalCompactProjectionPremise r)
    (hEqual : RealLocalEqualCharacterGrowthAtRank r) (D : RealQuotientMeasureData r) (a : ℝˣ)
    (P : Fin (r + 2) → Fin 2) (fs : List RealCharacterData) (hfs : fs.length = r + 1)
    (B : Automorphic.realStandardKFinite (r + 1) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner r (fs.map RealBlock.character) (-a) B)
    (v : Automorphic.realStandardKFinite (r + 1) (fs.map RealBlock.character))
    (Z : Fin (r + 2) → ℂ) :
    HasRealUnequalCanonicalPairGrowth gap a a (-a) D P Z (fs.map RealBlock.character)
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((determinant (RealGodementProfiles.characterList P 0) (-1) : ℂ) ^ (r + 1) *
        (determinant (fs.map RealBlock.character) (-1) : ℂ)) (B v) := by
  have hV : B v ∈ realUniformWhittakerModel r (fs.map RealBlock.character) (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  have hVreg := realUniformWhittakerRegularity r _ (-a) (B v) hV
  have hsign : ((determinant (RealGodementProfiles.characterList P 0) (-1) : ℂ) ^ (r + 1) *
      (determinant (fs.map RealBlock.character) (-1) : ℂ)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) (Units.ne_zero _)
  revert Z
  refine realChamberRemoval (fun Z => HasRealUnequalCanonicalPairGrowth gap a a (-a) D P Z
    (fs.map RealBlock.character) (NNReal.sqrt ‖(a : ℝ)‖₊)
    (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
    ((determinant (RealGodementProfiles.characterList P 0) (-1) : ℂ) ^ (r + 1) *
      (determinant (fs.map RealBlock.character) (-1) : ℂ)) (B v)) ?_ ?_
  · exact realUnequalCanonicalGrowthReflection gap a a (-a) D P _ _ _ _ hsign (B v)
      hVreg.1 hVreg.2
  · intro q
    let ex (i : Fin (r + 1)) : ℝ := ((r + 1 : ℕ) : ℝ) + normExponent (realPositionExponent
      (RealGodementProfiles.characterList (Fin.tail P) q)) (r + 1) i -
        (((r + 1 : ℕ) : ℝ) + 1) / 2
    obtain ⟨M, hM⟩ := (Set.finite_range ex).bddAbove
    refine ⟨M, fun Z hZq hZ hMZ => ?_⟩
    intro f
    have hc : ∀ i : Fin (r + 1), ((r + 1 : ℕ) : ℝ) + normExponent (realPositionExponent
        (RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z))) (r + 1) i ≤
        (RealJacquetFrobenius.charData (P 0) (Z 0)).exponent.re +
          (((r + 1 : ℕ) : ℝ) + 1) / 2 := by
      intro i
      have hi := (hM (Set.mem_range_self i)).trans hMZ
      rw [hZq]
      change _ ≤ (Z 0).re + _
      simp only [ex] at hi
      linarith
    obtain ⟨-, -, h⟩ := realAdjacentCanonicalChamberGrowth hProjO hEqual D (-a) P Z hZ hc fs hfs
      B hB v f
    rw [neg_neg, determinant_characterList_neg_one P Z 0] at h
    have hscale : NNReal.sqrt ‖((-a : ℝˣ) : ℝ)‖₊ = NNReal.sqrt ‖(a : ℝ)‖₊ := by
      rw [Units.val_neg, nnnorm_neg]
    exact hasRealPairNormalizedGrowth_scale_congr hscale h

/-! ### Adjacent-rank growth from equal-rank growth -/

variable (r) in
/-- At a fixed rank, the adjacent-rank character growth follows from the equal-rank character
growth at the smaller rank, given that every uniform Whittaker model of a character list is
contained in the range of the canonical Jacquet map, and compact projection along the
orthogonal group at the smaller rank. -/
def RealAdjacentFromEqualGrowthStatement : Prop :=
  RealGodement.RealUniformCanonicalRangePremise → RealOrthogonalCompactProjectionPremise r →
    RealLocalEqualCharacterGrowthAtRank r → RealLocalAdjacentCharacterGrowthAtRank r

theorem realAdjacentFromEqualGrowth : RealAdjacentFromEqualGrowthStatement r := by
  intro hRange hProjO hEqual ds es hds hes hrd hre a D W W' hW hW'
  obtain ⟨cs, rfl⟩ := hds
  obtain ⟨fs₀, rfl⟩ := hes
  have hcs : cs.length = r + 2 := by rw [← realRank_map_character]; exact hrd
  have hfs₀ : fs₀.length = r + 1 := by rw [← realRank_map_character]; exact hre
  obtain ⟨P, Zs, hPZ⟩ := RealGodement.exists_characterList_eq cs hcs
  obtain ⟨P', Zs', hPZ'⟩ := RealGodement.exists_characterList_eq fs₀ hfs₀
  rw [← hPZ] at hW ⊢
  rw [← hPZ'] at hW' ⊢
  obtain ⟨F, rfl⟩ := hRange (r + 1) (-a) P Zs (by rwa [neg_neg])
  obtain ⟨F', rfl⟩ := hRange r a P' Zs' hW'
  let fs : List RealCharacterData := List.ofFn fun i => RealJacquetFrobenius.charData (P' i) (Zs' i)
  have hfs : fs.length = r + 1 := List.length_ofFn
  have hB := realGodementCanonicalModel r a P' Zs'
  have h := realAdjacentCanonicalGrowth hProjO hEqual D a P fs hfs
    (canonicalJacquetMap a P' Zs') hB F' Zs F
  rw [← determinant_characterList_neg_one P Zs 0] at h
  exact h

end Langlands.Global.RankinSelbergGlobal.RealJacquet
