import Langlands.Representation.Archimedean.RealCartanFixedCosets
import Langlands.Representation.Archimedean.RealCartanLowTraceHaar
import Langlands.Representation.Archimedean.RealCartanRadialWeight
import Langlands.Representation.Archimedean.RealCartanTransverseLimit

/-! # The actual compact Cartan trace over the original blocks -/

noncomputable section

open Matrix MeasureTheory Set Filter
open scoped Matrix.Norms.Operator Topology Manifold ContDiff

namespace Langlands.Archimedean.RealCartanPlacedTrace

open Langlands.LocalFactor.Archimedean GramFormula PrincipalSeriesExtension
  RealCartanArgumentJacobian RealCartanBlockLayout RealCartanCompactSupport RealCartanFilterSupport
  RealCartanFixedCosets RealCartanFixedFlag RealCartanLowTraceHaar RealCartanRadialWeight
  RealCartanTraceCoordinates RealCartanTraceLocalization RealCartanTransverseLimit
  RealLeviChart RealLeviCompactChart RealPrincipalSeriesDuality RealStandardCompactAverage RealInducedStandardBound
  RealStandardEllipticCartan

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "G" n:max => Langlands.GeneralLinear n ℝ

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_GL
  RealLeviBlockHaar.secondCountableTopology_O
local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩

/-- The positive radii of the source slots. -/
def sourceRadius {r s : ℕ} (x : Coordinates r s) (i : Fin (r + s)) : ℝ :=
  Real.exp (coordinateRadius x (finSumFinEquiv.symm i))

theorem sourceRadius_pos {r s : ℕ} (x : Coordinates r s) (i : Fin (r + s)) : 0 < sourceRadius x i :=
  Real.exp_pos _

/-- The orthogonal factor of the prescribed source Cartan matrix. -/
def sourceOrthogonal {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) : K n :=
  ⟨cartanOrthogonal h x, (mem_orthogonalGroup_iff (Fin n) ℝ).mpr (cartanOrthogonal_orthogonal h x).1⟩

theorem sourceFactorization {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s) :
    (cartanElement h x : M n) = diagonal (sourceRadius x ∘ cartanLabel h) * (sourceOrthogonal h x : M n) := by
  have hD : cartanDiagonal h x = diagonal (sourceRadius x ∘ cartanLabel h) := by
    unfold cartanDiagonal sourceRadius cartanLabel
    congr 1
    funext p
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
  rw [cartanElement_val, hD]
  rfl

theorem sourceOrthogonal_zero {n r s : ℕ} (h : 2 * r + s = n) (x : Coordinates r s)
    (p q : Fin n) (hpq : cartanLabel h p ≠ cartanLabel h q) : (sourceOrthogonal h x : M n) p q = 0 := by
  have he := cartanElement_apply_of_label_ne h x hpq
  rw [sourceFactorization, diagonal_mul] at he
  exact (mul_eq_zero.mp he).resolve_left (sourceRadius_pos x _).ne'

/-- The cone tests keep the signed low projection or vanish below the source elliptic rank. -/
theorem eventually_cone_trace {n r s r' s' : ℕ} (h : 2 * r + s = n) {x : Coordinates r s}
    (hx : x ∈ separatedRegularCoordinates r s) {ds : List RealBlock}
    {d : Fin r' → ComplexCharacterData} {b : Fin s' → RealCharacterData}
    (hn : realRank ds = n) (hp : ds.Perm (ofBlockData d b)) (hrle : r' ≤ r) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      compactTestTrace (compactHaar n) ds (cartanElement h x) (scaledConeTest n ε) =
        (-1 : ℂ) ^ r' * compactLowTrace (compactHaar n) ds (cartanElement h x) (scaledConeTest n ε) ∧
      (r' < r → compactTestTrace (compactHaar n) ds (cartanElement h x) (scaledConeTest n ε) = 0) := by
  have hs := length_slots_ofBlockData hn hp
  obtain ⟨ha, hr, hsize, hzero, hskew, hpair, hgram, hd, hnormal⟩ :=
    realStandardEllipticCartanMatrix h x hx
  obtain ⟨U, hU, hOne, htrace⟩ := realCartanFilterSupport n ds (cartanLabel h)
    (cartanSquaredRadius x) (cartanElement h x) ha
    (fun _ _ _ hij heq hk => hsize hij heq hk) (fun _ _ hij => hzero hij)
    (fun _ _ hij heq => hskew hij heq) (fun _ _ hij heq => hpair hij heq) hgram hd hnormal
    (by rwa [hs, hr])
  filter_upwards [eventually_support_scaledConeTest_subset n hU hOne] with ε hε
  obtain ⟨heq, hvanish⟩ := htrace (compactHaar n) (scaledConeTest n ε) hε
  exact ⟨by simpa only [hs] using heq, fun hlt => hvanish (by rwa [hs, hr])⟩

section Placement

variable {t : ℕ} (b : Fin t → RealBlock)
local notation "Sizes" => blockSizes b
local notation "N" => ∑ i, Sizes i
local notation "H" => LeviFrame Sizes

/-- The compact Haar chart normalization, independent of the Cartan data. -/
def chartCoefficient {t : ℕ} (sizes : Fin t → ℕ) : ℝ :=
  Classical.choose (realCartanTransverseLimit t sizes)

theorem chartCoefficient_pos {t : ℕ} (sizes : Fin t → ℕ) : 0 < chartCoefficient sizes :=
  (Classical.choose_spec (realCartanTransverseLimit t sizes)).1

local instance assignmentFintype {u v : ℕ} (sizes : Fin v → ℕ) (a : Fin (∑ i, sizes i) → Fin u) :
    Fintype (Assignment sizes a) := Fintype.ofFinite _

/-- The matched source radii in the original target block order. -/
def matchingRadius {r s : ℕ} (h : 2 * r + s = ∑ i, blockSizes b i) (x : Coordinates r s)
    (e : Assignment (blockSizes b) (cartanLabel h)) (i : Fin t) : ℝ :=
  sourceRadius x (e.val.symm i)

theorem matchingRadius_pos {r s : ℕ} (h : 2 * r + s = ∑ i, blockSizes b i) (x : Coordinates r s)
    (e : Assignment (blockSizes b) (cartanLabel h)) (i : Fin t) : 0 < matchingRadius b h x e i :=
  sourceRadius_pos x (e.val.symm i)

/-- The orthogonal part in the matched target blocks, in the product compact group. -/
def matchedOrthogonal {r s : ℕ} (h : 2 * r + s = ∑ i, blockSizes b i) (x : Coordinates r s)
    (e : Assignment (blockSizes b) (cartanLabel h)) : LeviFrame (blockSizes b) := Classical.choose
  ((mem_range_blockFrame_iff (blockSizes b) (placedOrthogonal (blockSizes b) e (sourceOrthogonal h x))).mpr
    (blockZero_placedOrthogonal (blockSizes b) e (sourceOrthogonal h x) (sourceOrthogonal_zero h x)))

@[simp]
theorem blockFrame_matchedOrthogonal {r s : ℕ} (h : 2 * r + s = ∑ i, blockSizes b i) (x : Coordinates r s)
    (e : Assignment (blockSizes b) (cartanLabel h)) : blockFrame Sizes (matchedOrthogonal b h x e) =
    placedOrthogonal Sizes e (sourceOrthogonal h x) := Classical.choose_spec
  ((mem_range_blockFrame_iff Sizes (placedOrthogonal Sizes e (sourceOrthogonal h x))).mpr
    (blockZero_placedOrthogonal Sizes e (sourceOrthogonal h x) (sourceOrthogonal_zero h x)))

/-- The normalized transverse product at a fixed flag in the given assignment. -/
def matchedProduct {r s : ℕ} (h : 2 * r + s = ∑ i, blockSizes b i) (x : Coordinates r s)
    (e : Assignment (blockSizes b) (cartanLabel h)) (κ : H) : ℝ :=
  let B := fixedLeftFrame Sizes (matchedOrthogonal b h x e) κ
  normalizedProduct Sizes (matchingRadius b h x e) (matchingRadius_pos b h x e)
    (blockFrame Sizes B) (blockZero_blockFrame Sizes B)

/-- The block weight sum before carrying out the within-block Fourier evaluations. -/
def placementSum {r s : ℕ} (h : 2 * r + s = ∑ i, blockSizes b i) (x : Coordinates r s) : ℂ :=
  ∑ e : Assignment (blockSizes b) (cartanLabel h), centralRadialProduct b (matchingRadius b h x e) *
    ∫ κ, ∏ i, frameDensity b i (fixedLeftFrame Sizes (matchedOrthogonal b h x e) κ i) ∂frameMeasure Sizes

private def radialWeight (g : G N) (y : K N) : ℂ :=
  extension (shiftedExponent N (realPositionExponent (List.ofFn b))) 1 (Unitary.toUnits y * g)

private theorem continuous_radialWeight (g : G N) : Continuous (radialWeight b g) := by
  have h := (contMDiff_extension (shiftedExponent N (realPositionExponent (List.ofFn b)))
    (P := 1) (φ := 1) (by intro k; simp)).continuous
  exact h.comp (continuous_unitary_toUnits.mul continuous_const)

private def traceWeight (g : G N) : C(K N × H, ℂ) :=
  ⟨fun p => radialWeight b g p.1 * ∏ i, frameDensity b i (p.2 i),
    ((continuous_radialWeight b g).comp continuous_fst).mul
      (continuous_finsetProd _ fun i _ => (frameDensity b i).continuous.comp
        ((continuous_apply i).comp continuous_snd))⟩

private theorem lowTrace_eq_weightedIntegral (g : G N) (φ : C(K N, ℂ)) :
    compactLowTrace (compactHaar N) (List.ofFn b) g φ = weightedIntegral Sizes g (traceWeight b g) φ := by
  rw [realCartanLowTraceHaar t b]
  apply integral_congr_ae
  exact ae_of_all _ fun y => by
    dsimp only [weightedIntegral]
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun v => by
      change radialWeight b g y * ((∏ i, frameDensity b i (v i)) * _) = _
      simp only [traceWeight, ContinuousMap.coe_mk, mul_assoc]

private theorem radialWeight_placed {r s : ℕ} (h : 2 * r + s = ∑ i, blockSizes b i)
    (x : Coordinates r s) (e : Assignment (blockSizes b) (cartanLabel h)) (κ : H) :
    radialWeight b (cartanElement h x) (blockFrame Sizes κ * permutationFrame (assignmentPerm Sizes e)) =
      (borelWeight Sizes (matchingRadius b h x e) : ℂ) * centralRadialProduct b (matchingRadius b h x e) := by
  let w := permutationFrame (assignmentPerm Sizes e)
  let R := placedOrthogonal Sizes e (sourceOrthogonal h x)
  let D := placedDiagonal Sizes e (sourceRadius x) (sourceRadius_pos x)
  have hw : Unitary.toUnits w * cartanElement h x = D * Unitary.toUnits (R * w) :=
    toUnits_permutationFrame_mul Sizes e (sourceRadius x) (sourceRadius_pos x) _ _ (sourceFactorization h x)
  have hY : Unitary.toUnits (blockFrame Sizes κ * w) * cartanElement h x =
      D * Unitary.toUnits (blockFrame Sizes κ * R * w) := by
    simp only [map_mul, mul_assoc]
    rw [hw, ← mul_assoc (Unitary.toUnits (blockFrame Sizes κ)), blockFrame_commute_placedDiagonal]
    simp only [mul_assoc, map_mul, D]
  apply extension_eq_borel_mul_radial b (matchingRadius b h x e) (matchingRadius_pos b h x e)
    _ (blockFrame Sizes κ * R * w)
  rw [hY]
  change (D : M N) * ((blockFrame Sizes κ * R * w : K N) : M N) = _
  rw [placedDiagonal_val]
  rfl

/-- The actual low trace limit after extracting a common nonzero normalized denominator. -/
def RealCartanPlacedTraceStatement : Prop :=
  ∀ (t : ℕ) (b : Fin t → RealBlock) (r s : ℕ) (h : 2 * r + s = ∑ i, blockSizes b i)
    (x : Coordinates r s), x ∈ separatedRegularCoordinates r s →
    (slots (List.ofFn b) (∑ i, blockSizes b i)).length = r →
    ∀ q : ℝ, q ≠ 0 →
      (∀ (e : Assignment (blockSizes b) (cartanLabel h)) κ, matchedProduct b h x e κ = q) →
      Tendsto (fun ε => compactLowTrace (compactHaar (∑ i, blockSizes b i)) (List.ofFn b)
        (cartanElement h x) (scaledConeTest (∑ i, blockSizes b i) ε))
        (𝓝[>] (0 : ℝ)) (𝓝 ((chartCoefficient (blockSizes b) : ℂ) *
          ((coneMass (∑ i, blockSizes b i) : ℂ) * (q : ℂ)⁻¹) * placementSum b h x))

set_option maxHeartbeats 1000000 in
theorem realCartanPlacedTrace : RealCartanPlacedTraceStatement := by
  intro t b r s h x hx hr q hq heq
  let sz := blockSizes b
  let n := ∑ i, sz i
  let g := cartanElement h x
  let a := cartanLabel h
  let Γ := Assignment sz a
  let w (e : Γ) := permutationFrame (assignmentPerm sz e)
  let R (e : Γ) := matchedOrthogonal b h x e
  let d (e : Γ) := matchingRadius b h x e
  let D (e : Γ) := placedDiagonal sz e (sourceRadius x) (sourceRadius_pos x)
  let W := traceWeight b g
  obtain ⟨ha, hCount, haSize, hzero, hskew, hpair, hgram, hd, hnormal⟩ :=
    realStandardEllipticCartanMatrix h x hx
  have hsize (i : Fin t) : sz i = 1 ∨ sz i = 2 := by
    have hp := blockSizes_pos b i
    have hle := blockSizes_le_two b i
    change 0 < sz i at hp
    change sz i ≤ 2 at hle
    omega
  have hCounts : Nat.card (PairBlock a) = Nat.card (PairBlock (cls sz)) := by
    rw [hCount, card_pairBlock_eq_slots b, hr]
  have hd' (e : Γ) (i : Fin n) : 0 < (d e ∘ cls sz) i := matchingRadius_pos b h x e _
  have hD (e : Γ) : (D e : M n) = diagonal (d e ∘ cls sz) := placedDiagonal_val ..
  have hw (e : Γ) : Unitary.toUnits (w e) * g = D e * Unitary.toUnits (blockFrame sz (R e) * w e) := by
    dsimp only [R]
    rw [blockFrame_matchedOrthogonal]
    exact toUnits_permutationFrame_mul sz e _ _ _ _ (sourceFactorization h x)
  have hk (e : Γ) (κ : LeviFrame sz) : Unitary.toUnits (blockFrame sz κ) * D e =
      D e * Unitary.toUnits (blockFrame sz κ) := blockFrame_commute_placedDiagonal ..
  have hdisj : Pairwise (fun e j : Γ => Disjoint (range fun κ => blockFrame sz κ * w e)
      (range fun κ => blockFrame sz κ * w j)) := fun _ _ hne => disjoint_fixedCoset_of_ne sz ha hne
  have hfix (y : K n) (v : LeviFrame sz) (hv : compactArgument g y (blockFrame sz v) = 1) :
      ∃ e : Γ, y ∈ range (fun κ => blockFrame sz κ * w e) :=
    (realCartanFixedCosets (r + s) t sz a (cartanSquaredRadius x) g y (blockFrame sz v)
      ha (cls_surjective b) (card_cls_fiber_le_two b) hCounts (blockZero_blockFrame sz v)
      (fun _ _ _ hij heq hk => haSize hij heq hk) (fun _ _ hij => hzero hij)
      (fun _ _ hij heq => hskew hij heq) (fun _ _ hij heq => hpair hij heq) hgram hd hnormal hv).exists
  have hcenter (e : Γ) (κ v : LeviFrame sz) : compactArgument g (blockFrame sz κ * w e) (blockFrame sz v) = 1 ↔
      v = fixedLeftFrame sz (R e) κ := by
    have hplaced : compactArgument g (blockFrame sz κ * w e) (blockFrame sz v) = 1 ↔
        blockFrame sz v = blockFrame sz κ * (placedOrthogonal sz e (sourceOrthogonal h x))⁻¹ *
          (blockFrame sz κ)⁻¹ :=
      compactArgument_eq_one_placed sz e _ (sourceRadius_pos x) _ _ _ (sourceFactorization h x) κ
    rw [hplaced]
    have hb : blockFrame sz (fixedLeftFrame sz (R e) κ) =
        blockFrame sz κ * (placedOrthogonal sz e (sourceOrthogonal h x))⁻¹ * (blockFrame sz κ)⁻¹ := by
      simp only [fixedLeftFrame, map_mul, map_inv]
      rw [show blockFrame sz (R e) = _ from blockFrame_matchedOrthogonal b h x e]
    rw [← hb, (blockFrame_injective sz).eq_iff]
  let J (e : Γ) (κ : LeviFrame sz) := argumentLowerEnd sz (d e ∘ cls sz)
    (blockFrame sz (fixedLeftFrame sz (R e) κ)) (blockFrame sz κ * w e)
  have hnorm (e : Γ) (κ : LeviFrame sz) : |(J e κ).det| = borelWeight sz (d e) * q := by
    dsimp only [J]
    rw [abs_det_argument_eq_normalized sz (d e) (matchingRadius_pos b h x e) _ _
      (blockZero_blockFrame sz _)]
    exact congrArg (borelWeight sz (d e) * ·) (heq e κ)
  have hj (e : Γ) (κ : LeviFrame sz) : (J e κ).det ≠ 0 := by
    have hh := (hnorm e κ).symm ▸ mul_ne_zero (borelWeight_pos sz (d e)
      (matchingRadius_pos b h x e)).ne' hq
    exact abs_ne_zero.mp hh
  have hlim := (Classical.choose_spec (realCartanTransverseLimit t sz)).2 Γ g w R
    (fun e => d e ∘ cls sz) D hsize hd' hD hw hk hdisj hfix hcenter hj W
  have hlow (ε : ℝ) : weightedIntegral sz g W (scaledConeTest n ε) =
      compactLowTrace (compactHaar n) (List.ofFn b) g (scaledConeTest n ε) :=
    (lowTrace_eq_weightedIntegral b g _).symm
  change Tendsto (fun ε : ℝ => weightedIntegral sz g W (scaledConeTest n ε))
    (𝓝[>] (0 : ℝ)) (𝓝 ((chartCoefficient sz : ℂ) * (coneMass n : ℂ) *
      ∑ e : Γ, ∫ κ, ((|(J e κ).det|⁻¹ : ℝ) : ℂ) *
        W (blockFrame sz κ * w e, fixedLeftFrame sz (R e) κ) ∂frameMeasure sz)) at hlim
  simp_rw [hlow] at hlim
  let I (e : Γ) := centralRadialProduct b (d e) * ∫ κ, ∏ i,
    frameDensity b i (fixedLeftFrame sz (R e) κ i) ∂frameMeasure sz
  have hI (e : Γ) : (∫ κ, ((|(J e κ).det|⁻¹ : ℝ) : ℂ) *
      W (blockFrame sz κ * w e, fixedLeftFrame sz (R e) κ) ∂frameMeasure sz) = (q : ℂ)⁻¹ * I e := by
    unfold I
    rw [← mul_assoc, ← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun κ => by
      change ((|(J e κ).det|⁻¹ : ℝ) : ℂ) * (radialWeight b g (blockFrame sz κ * w e) *
        ∏ i, frameDensity b i (fixedLeftFrame sz (R e) κ i)) = _
      rw [hnorm, radialWeight_placed b h x e κ, Complex.ofReal_inv, Complex.ofReal_mul]
      have hp : (borelWeight sz (d e) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
        (borelWeight_pos sz (d e) (matchingRadius_pos b h x e)).ne'
      field_simp [hp, Complex.ofReal_ne_zero.mpr hq]
      dsimp only [d, sz]
      ring
  change Tendsto _ _ (𝓝 ((chartCoefficient sz : ℂ) *
    ((coneMass n : ℂ) * (q : ℂ)⁻¹) * ∑ e : Γ, I e))
  have he : (chartCoefficient sz : ℂ) * (coneMass n : ℂ) *
      (∑ e : Γ, ∫ κ, ((|(J e κ).det|⁻¹ : ℝ) : ℂ) *
        W (blockFrame sz κ * w e, fixedLeftFrame sz (R e) κ) ∂frameMeasure sz) =
        (chartCoefficient sz : ℂ) * ((coneMass n : ℂ) * (q : ℂ)⁻¹) * ∑ e : Γ, I e := by
    simp_rw [hI, ← Finset.mul_sum]
    ring
  rw [← he]
  exact hlim

end Placement

end Langlands.Archimedean.RealCartanPlacedTrace
