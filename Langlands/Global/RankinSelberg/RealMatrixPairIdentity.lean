import Langlands.Global.RankinSelberg.RealMatrixTwistedFunctionalEquation
import Langlands.Global.RankinSelberg.RealLocalEqualJacquetExpansion
import Langlands.Global.RankinSelberg.RealPrincipalSeriesFactors

/-! # The determinant-twisted real matrix equation with pair factors -/

noncomputable section

open MeasureTheory Filter Set Topology
open scoped Matrix Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean (RealBlock RealCharacterData realRank realPairLFactor
  realPairEpsilon realPairBlocks realEpsilon realLFactor denominator_realLFactor coe_realEpsilon)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal ArchimedeanDeterminantTheta RealSquareFourier RealPrincipalSeries

local instance realPairMatrixGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realPairMatrixGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩

variable {r : ℕ}
local notation "n" => r + 1
local notation "G" => GeneralLinear n ℝ
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "ιg" => inverseTranspose n ℝ
local notation "absC" => fun b : ℝˣ => ((|(b : ℝ)| : ℝ) : ℂ)

/-- Convergence, holomorphy and meromorphic continuation of two normalized real matrix integrals,
whose continuations satisfy the multiplied-out pair equation `PairMeromorphicIdentity`. -/
def HasRealMatrixPairIdentity (μ : Measure G) (f : G → ℂ) (Φ : Mat → ℂ) (fd : G → ℂ)
    (Φd : Mat → ℂ) (xs ys : List RealBlock) (b : ℝˣ) (sign : ℂ) : Prop :=
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (realMatrixZetaKernel f Φ s) μ ∧
      Integrable (realMatrixZetaKernel fd Φd s) μ) ∧
    DifferentiableOn ℂ (realMatrixZeta μ f Φ) {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (realMatrixZeta μ fd Φd) {s : ℂ | σ < s.re} ∧
    MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
    (∀ s : ℂ, σ < s.re → realMatrixZeta μ f Φ s = M s) ∧
    (∀ s : ℂ, σ < s.re → realMatrixZeta μ fd Φd s = Md s) ∧
    RealJacquet.PairMeromorphicIdentity xs ys b sign M Md

/-! ### Lists of real character blocks -/

/-- Expanding a block list gives a list of character blocks. -/
theorem exists_expand_eq_map_character (es : List RealBlock) :
    ∃ cs : List RealCharacterData, expand es = cs.map RealBlock.character := by
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons x es ih =>
    obtain ⟨cs, hcs⟩ := ih
    cases x with
    | character χ =>
      refine ⟨χ :: cs, ?_⟩
      change RealBlock.character χ :: expand es = _
      rw [hcs]
      rfl
    | induced δ =>
      refine ⟨RealJacquetFrobenius.charData (Langlands.LocalFactor.Archimedean.RealGammaReflection.positionParity δ.weight.natAbs)
          (δ.exponent + (δ.weight.natAbs : ℂ) / 2) ::
        RealJacquetFrobenius.charData 0 (δ.exponent - (δ.weight.natAbs : ℂ) / 2) :: cs, ?_⟩
      change RealBlock.character _ :: RealBlock.character _ :: expand es = _
      rw [hcs]
      rfl

theorem realRank_map_character (cs : List RealCharacterData) :
    realRank (cs.map RealBlock.character) = cs.length :=
  Langlands.Archimedean.realRank_map_character cs

theorem realRank_map_character_comp {α : Type*} (cs : List α) (g : α → RealCharacterData) :
    realRank (cs.map fun χ => RealBlock.character (g χ)) = cs.length := by
  induction cs with
  | nil => rfl
  | cons χ cs ih =>
    rw [List.map_cons, Langlands.LocalFactor.Archimedean.realRank_cons, ih, List.length_cons]
    change 1 + cs.length = cs.length + 1
    omega

/-- Products over the positions of a list of character blocks are products over the list. -/
theorem prod_range_positions (cs : List RealCharacterData) (h : Fin 2 → ℂ → (ℝˣ → ℂ) → ℂ) :
    ∏ p ∈ Finset.range cs.length,
        h (RealBlockPosition.realPositionSign (cs.map RealBlock.character) p)
          (GramFormula.realPositionExponent (cs.map RealBlock.character) p)
          (realPositionCharacter (cs.map RealBlock.character) p) =
      (cs.map fun χ => h χ.parity χ.exponent (fun x => (χ.character x : ℂ))).prod := by
  induction cs with
  | nil => simp
  | cons χ cs ih =>
    rw [List.length_cons, Finset.prod_range_succ', List.map_cons, List.map_cons, List.prod_cons,
      ← ih, mul_comm]
    rfl

theorem prod_fin_positions (cs : List RealCharacterData) (hlen : cs.length = n)
    (h : Fin 2 → ℂ → (ℝˣ → ℂ) → ℂ) :
    ∏ i : Fin n,
        h (RealBlockPosition.realPositionSign (cs.map RealBlock.character) i)
          (GramFormula.realPositionExponent (cs.map RealBlock.character) i)
          (realPositionCharacter (cs.map RealBlock.character) i) =
      (cs.map fun χ => h χ.parity χ.exponent (fun x => (χ.character x : ℂ))).prod := by
  rw [Fin.prod_univ_eq_prod_range (fun p =>
    h (RealBlockPosition.realPositionSign (cs.map RealBlock.character) p)
      (GramFormula.realPositionExponent (cs.map RealBlock.character) p)
      (realPositionCharacter (cs.map RealBlock.character) p)) n, ← hlen]
  exact prod_range_positions cs h

theorem list_prod_map_inv (cs : List RealCharacterData) (A : RealCharacterData → ℂ) :
    (cs.map fun χ => (A χ)⁻¹).prod = ((cs.map A).prod)⁻¹ := by
  induction cs with
  | nil => simp
  | cons χ cs ih => rw [List.map_cons, List.map_cons, List.prod_cons, List.prod_cons, ih, mul_inv]

theorem pairBlocks_character (d : RealCharacterData) (cs : List RealCharacterData) :
    realPairBlocks [RealBlock.character d] (cs.map RealBlock.character) =
      cs.map fun χ => RealBlock.character (d.mul χ) := by
  induction cs with
  | nil => rfl
  | cons χ cs ih =>
    simp only [realPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.map_cons] at ih ⊢
    rw [ih]
    rfl

theorem map_dualBlock_character (cs : List RealCharacterData) :
    (cs.map RealBlock.character).map RealLocalJacquet.dualBlock =
      (cs.map RealCharacterData.inverse).map RealBlock.character :=
  Langlands.Global.RankinSelbergGlobal.RealJacquet.map_dualBlock_character cs

/-! ### The torus factors are the pair factors -/

theorem torusL_eq_pair (cs : List RealCharacterData) (hlen : cs.length = n)
    (d : RealCharacterData) (s : ℂ) :
    torusL (fun i : Fin n =>
        RealBlockPosition.realPositionSign (cs.map RealBlock.character) i + d.parity)
      (fun i : Fin n => GramFormula.realPositionExponent (cs.map RealBlock.character) i +
        d.exponent) s =
      ((realPairLFactor [RealBlock.character d] (cs.map RealBlock.character)).denominator s)⁻¹ := by
  have h1 : torusL (fun i : Fin n =>
        RealBlockPosition.realPositionSign (cs.map RealBlock.character) i + d.parity)
      (fun i : Fin n => GramFormula.realPositionExponent (cs.map RealBlock.character) i +
        d.exponent) s =
      (cs.map fun χ => Complex.Gammaℝ (s + (χ.exponent + d.exponent) +
        ((χ.parity + d.parity).val : ℂ))).prod :=
    prod_fin_positions cs hlen
      (fun p t _ => Complex.Gammaℝ (s + (t + d.exponent) + ((p + d.parity).val : ℂ)))
  rw [h1, realPairLFactor, denominator_realLFactor, pairBlocks_character, List.map_map]
  rw [← inv_inv (List.prod _), ← list_prod_map_inv]
  congr 2
  refine List.map_congr_left fun χ _ => ?_
  change _ = (Complex.Gammaℝ (s + ((d.exponent + χ.exponent) + ((d.parity + χ.parity).val : ℂ))))⁻¹
  rw [add_comm d.parity χ.parity]
  congr 2
  ring

theorem torusL_neg_eq_pair (cs : List RealCharacterData) (hlen : cs.length = n)
    (d : RealCharacterData) (z : ℂ) :
    torusL (fun i : Fin n =>
        RealBlockPosition.realPositionSign (cs.map RealBlock.character) i + d.parity)
      (-fun i : Fin n => GramFormula.realPositionExponent (cs.map RealBlock.character) i +
        d.exponent) z =
      ((realPairLFactor ([RealBlock.character d].map RealLocalJacquet.dualBlock)
        ((cs.map RealBlock.character).map RealLocalJacquet.dualBlock)).denominator z)⁻¹ := by
  have h1 : torusL (fun i : Fin n =>
        RealBlockPosition.realPositionSign (cs.map RealBlock.character) i + d.parity)
      (-fun i : Fin n => GramFormula.realPositionExponent (cs.map RealBlock.character) i +
        d.exponent) z =
      (cs.map fun χ => Complex.Gammaℝ (z + -(χ.exponent + d.exponent) +
        ((χ.parity + d.parity).val : ℂ))).prod :=
    prod_fin_positions cs hlen
      (fun p t _ => Complex.Gammaℝ (z + -(t + d.exponent) + ((p + d.parity).val : ℂ)))
  have hd : [RealBlock.character d].map RealLocalJacquet.dualBlock =
      [RealBlock.character d.inverse] := rfl
  rw [h1, hd, map_dualBlock_character, realPairLFactor, denominator_realLFactor,
    pairBlocks_character, List.map_map, List.map_map]
  rw [← inv_inv (List.prod _), ← list_prod_map_inv]
  congr 2
  refine List.map_congr_left fun χ _ => ?_
  change _ = (Complex.Gammaℝ (z + ((-d.exponent + -χ.exponent) +
    ((d.parity + χ.parity).val : ℂ))))⁻¹
  rw [add_comm d.parity χ.parity]
  congr 2
  ring

theorem sqrt_scale_eq (b : ℝˣ) :
    (((NNReal.sqrt ‖(b : ℝ)‖₊ : NNReal) : ℝ) : ℂ) = ((|(b : ℝ)| : ℝ) : ℂ) ^ (1 / 2 : ℂ) := by
  rw [Real.coe_sqrt, coe_nnnorm, Real.norm_eq_abs, Real.sqrt_eq_rpow,
    Complex.ofReal_cpow (abs_nonneg _)]
  norm_num

theorem torusEpsilon_eq_pair (cs : List RealCharacterData) (hlen : cs.length = n)
    (d : RealCharacterData) (b : ℝˣ) (s : ℂ) :
    torusEpsilon (fun i : Fin n =>
        RealBlockPosition.realPositionSign (cs.map RealBlock.character) i + d.parity) *
      (∏ i : Fin n, realPositionCharacter (cs.map RealBlock.character) i b *
        (d.character b : ℂ)) *
      absC b ^ (((n : ℕ) : ℂ) * (s - 1 / 2)) =
    (realPairEpsilon [RealBlock.character d] (cs.map RealBlock.character) b
      (NNReal.sqrt ‖(b : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)) s : ℂ) := by
  have hb : absC b ≠ 0 := Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr b.ne_zero)
  have h1 : torusEpsilon (fun i : Fin n =>
        RealBlockPosition.realPositionSign (cs.map RealBlock.character) i + d.parity) =
      (cs.map fun χ => Complex.I ^ (χ.parity + d.parity).val).prod :=
    prod_fin_positions cs hlen (fun p _ _ => Complex.I ^ (p + d.parity).val)
  have h2 : (∏ i : Fin n, realPositionCharacter (cs.map RealBlock.character) i b *
        (d.character b : ℂ)) =
      (cs.map fun χ => (χ.character b : ℂ) * (d.character b : ℂ)).prod :=
    prod_fin_positions cs hlen (fun _ _ χ => χ b * (d.character b : ℂ))
  have hrank : realRank (cs.map fun χ => RealBlock.character (d.mul χ)) = n := by
    rw [realRank_map_character_comp, hlen]
  rw [h1, h2, realPairEpsilon, pairBlocks_character, coe_realEpsilon, hrank, List.map_map,
    List.map_map, sqrt_scale_eq]
  have hdet : (cs.map ((fun x : RealBlock => (x.determinant b : ℂ)) ∘
        fun χ => RealBlock.character (d.mul χ))).prod =
      (cs.map fun χ => (χ.character b : ℂ) * (d.character b : ℂ)).prod := by
    congr 1
    refine List.map_congr_left fun χ _ => ?_
    change ((d.character * χ.character) b : ℂ) = _
    rw [ContinuousMonoidHom.mul_apply, Units.val_mul, mul_comm]
  have heps : (cs.map ((fun x : RealBlock => (x.standardEpsilon : ℂ)) ∘
        fun χ => RealBlock.character (d.mul χ))).prod =
      (cs.map fun χ => Complex.I ^ (χ.parity + d.parity).val).prod := by
    congr 1
    refine List.map_congr_left fun χ _ => ?_
    change Complex.I ^ (d.parity + χ.parity).val = _
    rw [add_comm]
  have hb' : ((|(b : ℝ)| : ℝ) : ℂ) ≠ 0 := hb
  have hsplit : ((|(b : ℝ)| : ℝ) : ℂ) ^ (((n : ℕ) : ℂ) * (s - 1 / 2)) =
      ((|(b : ℝ)| : ℝ) : ℂ) ^ (((n : ℕ) : ℂ) * (1 / 2)) *
        ((|(b : ℝ)| : ℝ) : ℂ) ^ (((n : ℕ) : ℂ) * (s - 1)) := by
    rw [← Complex.cpow_add _ _ hb']
    congr 1
    ring
  rw [hdet, heps, ← Complex.cpow_nat_mul]
  beta_reduce
  rw [hsplit]
  ring

/-! ### Passing to the pair identity -/

theorem denominator_codiscrete (F : Langlands.LocalFactor.ReciprocalEntire) :
    ∀ᶠ s in codiscrete ℂ, F.denominator s ≠ 0 :=
  eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr F.denominator_eventually_ne_zero

/-- A pair identity transfers along a codiscrete equality of pair multipliers. -/
theorem pairMeromorphicIdentity_of_multiplier {xs ys xs' ys' : List RealBlock} {b : ℝˣ}
    {sign : ℂ} {M Md : ℂ → ℂ}
    (hm : ∀ᶠ s in codiscrete ℂ,
      pairMultiplier xs' ys' b (NNReal.sqrt ‖(b : ℝ)‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)) s =
        pairMultiplier xs ys b (NNReal.sqrt ‖(b : ℝ)‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)) s)
    (h : RealJacquet.PairMeromorphicIdentity xs' ys' b sign M Md) :
    RealJacquet.PairMeromorphicIdentity xs ys b sign M Md := by
  unfold RealJacquet.PairMeromorphicIdentity at h ⊢
  filter_upwards [h, hm, denominator_codiscrete (realPairLFactor xs' ys'),
    denominator_codiscrete (realPairLFactor xs ys)] with s hs hms hd' hd
  have h1 : Md (1 - s) = sign * pairMultiplier xs ys b (NNReal.sqrt ‖(b : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)) s * M s := by
    rw [← hms]
    calc
      Md (1 - s) = (realPairLFactor xs' ys').denominator s *
          (((realPairLFactor xs' ys').denominator s)⁻¹ * Md (1 - s)) := by
        rw [← mul_assoc, mul_inv_cancel₀ hd', one_mul]
      _ = _ := by
        rw [hs, pairMultiplier]
        ring
  rw [h1, pairMultiplier]
  calc
    _ = sign * (realPairEpsilon xs ys b (NNReal.sqrt ‖(b : ℝ)‖₊)
          (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero)) s : ℂ) *
        ((realPairLFactor (xs.map RealLocalJacquet.dualBlock)
          (ys.map RealLocalJacquet.dualBlock)).denominator (1 - s))⁻¹ * M s *
        (((realPairLFactor xs ys).denominator s)⁻¹ * (realPairLFactor xs ys).denominator s) := by
      ring
    _ = _ := by rw [inv_mul_cancel₀ hd, mul_one]

/-- The pair identity for the character list `expand es` itself: for the determinant twist of a
compact-derivative-bounded coefficient of the position principal series of `expand es`, the
torus factors are the pair factors of `[character d]` and `expand es`. -/
theorem realMatrixPairIdentity_expand (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure Kc)
    [κ.IsHaarMeasure] [SFinite κ] (es : List RealBlock) (hes : realRank es = n)
    (f : principalSeries ℝ n (realPositionCharacter (expand es)))
    (ℓ : principalSeries ℝ n (realPositionCharacter (expand es)) →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r (expand es) ℓ) (d : RealCharacterData) (Φ : 𝓢(Mat, ℂ))
    (b : ℝˣ) :
    let F (g : G) := realDetCharacter d g * ℓ (translate r (expand es) g f)
    HasRealMatrixPairIdentity μ F Φ (F ∘ ιg) (matrixTransform b Φ)
      [RealBlock.character d] (expand es) b 1 := by
  intro F
  obtain ⟨cs, hcs⟩ := exists_expand_eq_map_character es
  have hlen : cs.length = n := by
    rw [← realRank_map_character, ← hcs, realRank_expand, hes]
  obtain ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, hFE⟩ :=
    realMatrixTwistedFunctionalEquation (r := r) μ κ (expand es) f ℓ hℓ d Φ b
  refine ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, ?_⟩
  unfold RealJacquet.PairMeromorphicIdentity
  rw [hcs] at hFE ⊢
  filter_upwards [hFE] with s hs
  rw [← torusL_eq_pair cs hlen d s, ← torusL_neg_eq_pair cs hlen d (1 - s),
    ← torusEpsilon_eq_pair cs hlen d b s, one_mul]
  exact hs

/-- The equation for the determinant twist of a compact-derivative-bounded coefficient of the
position principal series of `expand es`, in the form of the pair identity for the character
`d` and the block list `es`, at the Fourier parameter `b` and scale `sqrt |b|`. -/
def RealMatrixPairIdentityStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (es : List RealBlock), realRank es = n →
    ∀ (f : principalSeries ℝ n (realPositionCharacter (expand es)))
    (ℓ : principalSeries ℝ n (realPositionCharacter (expand es)) →ₗ[ℂ] ℂ),
    HasCompactDerivativeBound r (expand es) ℓ →
    ∀ (d : RealCharacterData) (Φ : 𝓢(Mat, ℂ)) (b : ℝˣ),
    let F (g : G) := realDetCharacter d g * ℓ (translate r (expand es) g f)
    HasRealMatrixPairIdentity μ F Φ (F ∘ ιg) (matrixTransform b Φ)
      [RealBlock.character d] es b 1

theorem realMatrixPairIdentity : RealMatrixPairIdentityStatement (r := r) := by
  intro μ hμ κ hκ hκs es hes f ℓ hℓ d Φ b F
  obtain ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, hpair⟩ :=
    realMatrixPairIdentity_expand μ κ es hes f ℓ hℓ d Φ b
  refine ⟨σ, M, Md, h1, h2, h3, h4, h5, h6, h7, pairMeromorphicIdentity_of_multiplier ?_ hpair⟩
  exact pairMultiplier_expand [RealBlock.character d] es b (NNReal.sqrt ‖(b : ℝ)‖₊)
    (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr b.ne_zero))

end Langlands.GodementJacquet
