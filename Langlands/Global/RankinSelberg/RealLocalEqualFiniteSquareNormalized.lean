import Langlands.Global.RankinSelberg.RealLocalCompactFourierWeight
import Langlands.Global.RankinSelberg.RealLocalNormalizedGrowth
import Langlands.Global.RankinSelberg.RealWhittakerCompactProjection
import Langlands.Global.RankinSelberg.RealLocalAdjacentIntegrals
import Langlands.Global.RankinSelberg.RealUniformWhittakerDual

/-! # Entire products for an orthogonal-finite square test in the real equal-rank unfolding -/

noncomputable section

open MeasureTheory Set
open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open Langlands.CompactRepresentativeWeights
open scoped NNReal SchwartzMap Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open ArchimedeanLocal
open Langlands.Archimedean.RealJacquetFrobenius (charData)
open RealJacquet (HasRealPairNormalizedGrowth)
open RealUniformWhittakerDual (dualCharacterBlocks realUniformWhittakerCharacterDual)

attribute [local instance 100] LieRing.ofAssociativeRing

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent (n + 1) ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedAddCommGroup (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedAddCommGroup

private local instance (n : ℕ) (ds : List RealBlock) :
    NormedSpace ℂ (RealStandardCompactBanach.Carrier n ds) :=
  (RealStandardCompactBanach.closureSubmodule (n := n) ds).normedSpace

variable {t : ℕ}

local notation "m" => (t + 1)
local notation "G" => Langlands.GeneralLinear (t + 1) ℝ
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "O" => Matrix.unitaryGroup (Fin (t + 2)) ℝ
local notation "Y" => Matrix (Fin (t + 2)) (Fin (t + 2)) ℝ
local notation "gap" => Nat.lt_succ_self t
local notation "ιT" => GeneralLinear.inverseTranspose (t + 2) ℝ

/-! ### Characters -/

/-- The inverse of the real character with parity `e` and exponent `z` has parity `e`
and exponent `-z`. -/
theorem charData_inverse (e : Fin 2) (z : ℂ) :
    (charData e z).inverse = charData e (-z) := by
  have h : (charData e z).inverse.character = (charData e (-z)).character := by
    ext x
    exact ((charData e z).inverse.character_eq x).trans ((charData e (-z)).character_eq x).symm
  change RealCharacterData.mk (charData e z).inverse.character e (-z) _ =
    RealCharacterData.mk (charData e (-z)).character e (-z) _
  congr 1

/-! ### Matrix coefficients and weighted matrix integrals -/

/-- The matrix coefficient `g ↦ ℓ(π(g) f)` of a standard vector `f` of the smooth position
principal series attached to the expanded block list. -/
def realStandardMatrixCoefficient (es : List RealBlock)
    (ℓ : principalSeries ℝ (t + 2) (realPositionCharacter (RealPrincipalSeries.expand es)) →ₗ[ℂ] ℂ)
    (f : Automorphic.realStandardKFinite (t + 2) es) (g : H) : ℂ :=
  ℓ (RealPrincipalSeries.translate (t + 1) (RealPrincipalSeries.expand es) g
    (RealPrincipalSeries.expandedSmoothInclusion (t + 1) es f))

/-- The matrix integral `w ↦ ∫ Ψ(g) sgn(det g)^e |det g|^(w + m/2) b(g) dμ(g)`, with
`m = t + 1` the smaller rank. -/
def realWeightedMatrixIntegral (μ : Measure H) (e : Fin 2) (Ψ : Y → ℂ) (b : H → ℂ) (w : ℂ) : ℂ :=
  ∫ g, realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g * b g ∂μ

/-! ### Strip growth -/

private theorem stripGrowth_const (c : ℂ) : HasStripExponentialGrowth (fun _ => c) :=
  fun _ _ => ⟨‖c‖, 0, 0, norm_nonneg _, le_rfl, fun _ _ _ _ => by simp⟩

private theorem stripGrowth_add {f g : ℂ → ℂ}
    (hf : HasStripExponentialGrowth f) (hg : HasStripExponentialGrowth g) :
    HasStripExponentialGrowth (fun s => f s + g s) := by
  intro a b
  obtain ⟨C, K, T, hC, hK, hf⟩ := hf a b
  obtain ⟨D, L, U, hD, _, hg⟩ := hg a b
  refine ⟨C + D, max K L, max T U, add_nonneg hC hD, hK.trans (le_max_left _ _), ?_⟩
  intro s ha hb hs
  rw [add_mul]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (hf s ha hb ((le_max_left _ _).trans hs)).trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hg s ha hb ((le_max_right _ _).trans hs)).trans ?_
    gcongr
    exact le_max_right _ _

private theorem stripGrowth_sum {k : ℕ} (F : Fin k → ℂ → ℂ)
    (hF : ∀ j, HasStripExponentialGrowth (F j)) :
    HasStripExponentialGrowth (fun s => ∑ j, F j s) := by
  suffices ∀ S : Finset (Fin k), HasStripExponentialGrowth (fun s => ∑ j ∈ S, F j s) from
    this Finset.univ
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    exact fun a b => ⟨0, 0, 0, le_rfl, le_rfl, fun s _ _ _ => by simp⟩
  | insert j S hj ih =>
    simpa only [Finset.sum_insert hj] using stripGrowth_add (hF j) ih

private theorem stripGrowth_shift {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (z : ℂ) :
    HasStripExponentialGrowth (fun s => f (s + z)) := by
  simpa only [Complex.ofReal_one, div_one] using hf.div_add z (c := 1) one_pos

private theorem stripGrowth_tilt {f : ℂ → ℂ} (hf : HasStripExponentialGrowth f) (v : ℂ) :
    HasStripExponentialGrowth (fun s => f (s + (v + s))) := by
  convert hf.div_add (v / 2) (c := 1 / 2) (by norm_num) using 1
  funext s
  congr 1
  push_cast
  ring

/-! ### The finite square normalization -/

variable (t) in
/-- For a square Schwartz test `Ψ` with finite left orthogonal orbit, the real unfolded
equal-rank integral (8.1) in the separated exponent `z` and the spectral variable `s`,
multiplied by the two reciprocal `L`-factors, is the trace of one entire function `F` of
`(z, s)` on a dominant chamber. The dual unfolded integral, with the Fourier test, the Weyl
inverse-transpose duals and the inverse character, is the trace of a second entire function
`Fd`. The two satisfy the product of the two normalized functional equations everywhere.
The inputs are the normalized corank-one equation for every coefficient of the larger
model with the fixed smaller coefficient `W`, and the normalized matrix equation for every
bounded matrix coefficient of the larger principal series. The larger coefficient is
`B f` for a uniform Whittaker map `B` with a continuous Whittaker evaluation. -/
def RealLocalEqualFiniteSquareNormalizedStatement : Prop :=
  ∀ (D : RealQuotientMeasureData t) (D' : RealQuotientMeasureData (t + 1)) (a : ℝˣ) (e : Fin 2)
    (cs fs : List RealCharacterData), cs.length = t + 1 → fs.length = t + 2 →
  ∀ (W : G → ℂ), W ∈ realUniformWhittakerModel t (cs.map RealBlock.character) a →
  ∀ (B : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ)),
    IsRealUniformWhittakerIntertwiner (t + 1) (fs.map RealBlock.character) (-a) B →
    (∃ L : DerivativeSmoothVectors (matrixModel ℝ (t + 2))
        (RealStandardCompactBanach.representation (n := t + 2) (fs.map RealBlock.character)) →L[ℂ] ℂ,
      RealStandardCompactBanach.IsWhittakerStandardEvaluation (fs.map RealBlock.character) (-a) B L) →
  ∀ (f : Automorphic.realStandardKFinite (t + 2) (fs.map RealBlock.character)) (Ψ : 𝓢(Y, ℂ)),
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℝ (t + 2) =>
      fun X : Y => Ψ (k.val⁻¹.val * X))) →
  ∀ (xs ys xsd ysd : List RealBlock) (bA : ℝˣ) (cA : ℝ≥0) (hcA : 0 < cA) (signA : ℂ),
    (∀ V ∈ realUniformWhittakerModel (t + 1) (fs.map RealBlock.character) (-a),
      HasRealPairNormalizedGrowth xs ys xsd ysd bA cA hcA signA
        (realUnequalIntegral gap D V W) (realUnequalDualIntegral gap (-a) D V W)) →
  ∀ (us vs usd vsd : List RealBlock) (bM : ℝˣ) (cM : ℝ≥0) (hcM : 0 < cM) (signM : ℂ),
    (∀ ℓ, RealPrincipalSeries.HasCompactDerivativeBound (t + 1)
        (RealPrincipalSeries.expand (fs.map RealBlock.character)) ℓ →
      (∃ β : ℝ, ∀ w : ℂ, β < w.re →
        Integrable (fun g => realWeightedMatrixTest (charData e 0) Ψ (w + (m : ℂ) / 2) g *
          realStandardMatrixCoefficient (fs.map RealBlock.character) ℓ f g) D'.groupHaar ∧
        Integrable (fun g => realWeightedMatrixTest (charData e 0)
          (realRectangularSchwartzFourier (-a) Ψ) (w + (m : ℂ) / 2) g *
          realStandardMatrixCoefficient (fs.map RealBlock.character) ℓ f (ιT g)) D'.groupHaar) ∧
      HasRealPairNormalizedGrowth us vs usd vsd bM cM hcM signM
        (realWeightedMatrixIntegral D'.groupHaar e Ψ
          (realStandardMatrixCoefficient (fs.map RealBlock.character) ℓ f))
        (realWeightedMatrixIntegral D'.groupHaar e (realRectangularSchwartzFourier (-a) Ψ)
          (realStandardMatrixCoefficient (fs.map RealBlock.character) ℓ f ∘ ιT))) →
    ∃ F Fd : ℂ × ℂ → ℂ, Differentiable ℂ F ∧ Differentiable ℂ Fd ∧
      (∀ z : ℂ, HasStripExponentialGrowth (fun s => F (z, s))) ∧
      (∀ v : ℂ, HasStripExponentialGrowth (fun s => F (v + s, s))) ∧
      (∀ z : ℂ, HasStripExponentialGrowth (fun s => Fd (z, s))) ∧
      (∀ v : ℂ, HasStripExponentialGrowth (fun s => Fd (v + s, s))) ∧
      (∃ τ σ : ℝ, ∀ z s : ℂ, τ < z.re → σ < s.re →
        F (z, s) = (realPairLFactor xs ys).denominator s *
          (realPairLFactor us vs).denominator (s + z) *
          ∫ p, equalUnfoldedKernel (charData e z) Ψ W (B f) s p ∂(D.measure.prod D'.groupHaar)) ∧
      (∃ τ σ : ℝ, ∀ z s : ℂ, τ < (-z).re → σ < s.re →
        Fd (z, s) = (realPairLFactor xsd ysd).denominator s *
          (realPairLFactor usd vsd).denominator (s - z) *
          ∫ p, equalUnfoldedKernel (charData e (-z)) (realRectangularSchwartzFourier (-a) Ψ)
            (ArchimedeanLocal.dualFunction (t + 1) W) (ArchimedeanLocal.dualFunction (t + 2) (B f)) s p
              ∂(D.measure.prod D'.groupHaar)) ∧
      ∀ z s : ℂ, Fd (z, 1 - s) = signA * (realPairEpsilon xs ys bA cA hcA s : ℂ) *
        (signM * (realPairEpsilon us vs bM cM hcM (s + z) : ℂ)) * F (z, s)

set_option maxHeartbeats 1600000 in
theorem realLocalEqualFiniteSquareNormalized : RealLocalEqualFiniteSquareNormalizedStatement t := by
  intro D D' a e cs fs hcs hfs W hW B hB hL f Ψ hfin xs ys xsd ysd bA cA hcA signA hAdj
    us vs usd vsd bM cM hcM signM hMat
  obtain ⟨L, hL⟩ := hL
  let ds := cs.map RealBlock.character
  let es := fs.map RealBlock.character
  let ν : Measure O := Measure.haar
  let Ψd : 𝓢(Y, ℂ) := realRectangularSchwartzFourier (-a) Ψ
  obtain ⟨κ, hκfin, hrep, hrepd⟩ := realOrthogonalMatchedWeight (-a) ν (charData e 0) Ψ hfin
  obtain ⟨c, u, ℓ, hℓ, hProj⟩ := RealStandardCompactBanach.exists_compactProjection_coefficients
    es (-a) B L hL ν κ hκfin
  let b (j : Fin c) : H → ℂ := realStandardMatrixCoefficient es (ℓ j) f
  have hExp (x g : H) :
      (∫ k, κ k * B f (x * Unitary.toUnits k * g) ∂ν) = ∑ j, B (u j) x * b j g :=
    hProj f x g
  have hmem (v : Automorphic.realStandardKFinite (t + 2) es) :
      B v ∈ realUniformWhittakerModel (t + 1) es (-a) :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  have hdet (k : O) : |((Unitary.toUnits k : H) : Y).det| = 1 :=
    MaximalParabolicIntegration.abs_det_unitary ⟨Unitary.toUnits k, k.property⟩
  have hM (j : Fin c) := hMat (ℓ j) (hℓ j)
  choose hβ' hMg using hM
  choose β hβ using hβ'
  obtain ⟨β₀, hβ₀⟩ := (Set.finite_range β).bddAbove
  have hβj (w : ℂ) (hw : β₀ < w.re) (j : Fin c) : β j < w.re :=
    (hβ₀ (mem_range_self j)).trans_lt hw
  obtain ⟨τ, σ, hProd⟩ := realLocalEqualShiftedProducts D D' O ν Unitary.toUnits
    continuous_unitary_toUnits hdet κ κ.continuous a e ds es W (B f) hW (hmem f) Ψ hrep c
    (fun j => B (u j)) b (fun j => realWeightedMatrixIntegral D'.groupHaar e Ψ (b j))
    (fun j => hmem (u j)) hExp ⟨β₀, fun w hw j => ⟨(hβ j w (hβj w hw j)).1, rfl⟩⟩
  have hWd := realUniformWhittakerCharacterDual t cs hcs a W hW
  have hVd := realUniformWhittakerCharacterDual (t + 1) fs hfs (-a) (B f) (hmem f)
  have hVjd (j : Fin c) :=
    realUniformWhittakerCharacterDual (t + 1) fs hfs (-a) (B (u j)) (hmem (u j))
  obtain ⟨τd, σd, hProdd⟩ := realLocalEqualShiftedProducts D D' O ν Unitary.toUnits
    continuous_unitary_toUnits hdet κ κ.continuous (-a) e (dualCharacterBlocks cs)
    (dualCharacterBlocks fs) (ArchimedeanLocal.dualFunction (t + 1) W) (ArchimedeanLocal.dualFunction (t + 2) (B f)) hWd hVd Ψd
    hrepd c (fun j => ArchimedeanLocal.dualFunction (t + 2) (B (u j))) (fun j => b j ∘ ιT)
    (fun j => realWeightedMatrixIntegral D'.groupHaar e Ψd (b j ∘ ιT)) hVjd
    (fun x g => dualFunction_compactExpansion ν κ (B f) (fun j => B (u j)) b hExp x g)
    ⟨β₀, fun w hw j => ⟨(hβ j w (hβj w hw j)).2, rfl⟩⟩
  have hA (j : Fin c) := hAdj (B (u j)) (hmem (u j))
  choose N Nd hN hNd hNg hNdg hNR hNE using hA
  choose M Md hMf hMd hMfg hMdg hMR hME using hMg
  choose ρ hρ using hNR
  choose ρM hρM using hMR
  obtain ⟨uA, huA⟩ := (Set.finite_range ρ).bddAbove
  obtain ⟨uM, huM⟩ := (Set.finite_range ρM).bddAbove
  let F (p : ℂ × ℂ) := ∑ j, N j p.2 * M j (p.2 + p.1)
  let Fd (p : ℂ × ℂ) := ∑ j, Nd j p.2 * Md j (p.2 - p.1)
  have hF : Differentiable ℂ F := Differentiable.fun_sum fun j _ =>
    ((hN j).comp differentiable_snd).mul
      ((hMf j).comp (differentiable_snd.add differentiable_fst))
  have hFd : Differentiable ℂ Fd := Differentiable.fun_sum fun j _ =>
    ((hNd j).comp differentiable_snd).mul
      ((hMd j).comp (differentiable_snd.sub differentiable_fst))
  have hRef (z s : ℂ) : Fd (z, 1 - s) = signA * (realPairEpsilon xs ys bA cA hcA s : ℂ) *
      (signM * (realPairEpsilon us vs bM cM hcM (s + z) : ℂ)) * F (z, s) := by
    dsimp only [F, Fd]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (1 - s) - z = 1 - (s + z) by ring, hNE j s, hME j (s + z)]
    ring
  have hFdTilt (v : ℂ) : (fun s => Fd (v + s, s)) = fun s => ∑ j, Nd j s * Md j (-v) := by
    funext s
    dsimp only [Fd]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show s - (v + s) = -v by ring]
  refine ⟨F, Fd, hF, hFd,
    fun z => stripGrowth_sum _ (fun j => (hNg j).mul (stripGrowth_shift (hMfg j) z)),
    fun v => stripGrowth_sum _ (fun j => (hNg j).mul (stripGrowth_tilt (hMfg j) v)),
    fun z => stripGrowth_sum _ (fun j => (hNdg j).mul (stripGrowth_shift (hMdg j) (-z))),
    fun v => ?_, ?_, ?_, hRef⟩
  · rw [hFdTilt v]
    exact stripGrowth_sum _ (fun j => (hNdg j).mul (stripGrowth_const _))
  · refine ⟨max τ 0, max σ (max uA uM), fun z s hz hs => ?_⟩
    have hRaw := hProd z s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)
    have hsj (j : Fin c) : ρ j < s.re :=
      (huA (mem_range_self j)).trans_lt
        ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs))
    have hmk (j : Fin c) : ρM j < (s + z).re := by
      rw [Complex.add_re]
      linarith [huM (mem_range_self j),
        (le_max_right uA uM).trans_lt ((le_max_right σ _).trans_lt hs),
        (le_max_right τ 0).trans_lt hz]
    rw [hRaw, Finset.mul_sum]
    dsimp only [F]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hρ j s (hsj j)).1, (hρM j (s + z) (hmk j)).1]
    ring
  · refine ⟨max τd 0, max σd (max uA uM), fun z s hz hs => ?_⟩
    have hRaw := hProdd (-z) s ((le_max_left _ _).trans_lt hz) ((le_max_left _ _).trans_lt hs)
    have hsj (j : Fin c) : ρ j < s.re :=
      (huA (mem_range_self j)).trans_lt
        ((le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hs))
    have hmk (j : Fin c) : ρM j < (s - z).re := by
      rw [sub_eq_add_neg, Complex.add_re]
      linarith [huM (mem_range_self j),
        (le_max_right uA uM).trans_lt ((le_max_right σd _).trans_lt hs),
        (le_max_right τd 0).trans_lt hz]
    rw [hRaw, Finset.mul_sum]
    dsimp only [Fd]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hρ j s (hsj j)).2, (hρM j (s - z) (hmk j)).2,
      RealJacquet.realUnequalDualIntegral_adjacent, ← sub_eq_add_neg]
    ring

end Langlands.Global.RankinSelbergGlobal.RealGodement
