import Langlands.Global.RankinSelberg.CompactPairingSpanning
import Langlands.Global.RankinSelberg.RealGodementFiniteGeneration
import Langlands.Global.RankinSelberg.RealGodementGaussianPairing
import Langlands.Global.RankinSelberg.RealGodementSchwartzSection
import Langlands.Representation.Archimedean.RealPrincipalSeriesDualityProof

/-! # Spanning the real K-finite principal series by polynomial Gaussian Godement sections -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial gaussianPolynomialLinear
  exists_rightTranslate_gaussianPolynomial rightTranslate_mem_range)
open PartialJacquet (normExponent)
open GramFormula (realPositionExponent)
open FiniteTranslationSpan (rightSpan)
open ComplexJacquet (compactPairingSpanning)
open RealPrincipalSeriesDuality (haarK)
open Langlands.Whittaker (rightTranslation)

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

attribute [local instance] RealPrincipalSeriesDuality.measurableSpaceK
  RealPrincipalSeriesDuality.borelSpaceK

variable {m : ℕ}

local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "K" => unitaryCompact ℝ (m + 1)
local notation "Poly" => MvPolynomial (Coordinates m (m + 1)) ℂ

/-- Right translation of a real Godement section by an upper group element pulls the test
back along right multiplication of rectangular matrices. -/
theorem sectionValue_mul_right (μ : Measure G) (c : RealCharacterData) (f : G → ℂ)
    (Φ : X → ℂ) (g q : H) :
    sectionValue μ c f Φ (g * q) = determinantWeight c ((m : ℂ) / 2) q *
      sectionValue μ c f (fun x => Φ (x * q.val)) g := by
  let s := (m : ℂ) / 2
  let v := ((m : ℂ) + 1) / 2
  change determinantWeight c s (g * q) *
      (∫ h, f h⁻¹ * determinantWeight c v h * Φ (rowPoint h.val (g * q)) ∂μ) =
    determinantWeight c s q * (determinantWeight c s g *
      (∫ h, f h⁻¹ * determinantWeight c v h * Φ (rowPoint h.val g * q.val) ∂μ))
  rw [map_mul, mul_left_comm (determinantWeight c s q), mul_assoc]
  congr 2
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  dsimp only
  congr 2
  change h.val * (lastRows g.val * q.val) = (h.val * lastRows g.val) * q.val
  exact (Matrix.mul_assoc _ _ _).symm

private theorem integrable_sectionIntegrand (μ : Measure G) [μ.IsHaarMeasure]
    (c : RealCharacterData) (ds : List RealBlock) {f : G → ℂ}
    (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2)
    (Φ : 𝓢(X, ℂ)) (g : H) :
    Integrable (fun h : G => f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h *
      Φ (rowPoint h.val g)) μ := by
  obtain ⟨b, hb, hB⟩ := realGodementSchwartzMajorant m μ c ds f hf hc Φ {g} isCompact_singleton
  have hC : Continuous (fun h : G => f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h *
      Φ (rowPoint h.val g)) :=
    ((hf.1.continuous.comp continuous_inv).mul (contMDiff_determinantWeight c _).continuous).mul
      (Φ.continuous.comp (Units.continuous_val.matrix_mul continuous_const))
  refine hb.mono' hC.aestronglyMeasurable (ae_of_all _ fun h => ?_)
  simpa only [norm_mul] using hB g rfl h

/-- The real Godement section as a linear map on Schwartz tests in the convergence half-plane. -/
private def sectionLinear (μ : Measure G) [μ.IsHaarMeasure] (c : RealCharacterData)
    (ds : List RealBlock) {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) :
    𝓢(X, ℂ) →ₗ[ℂ] (H → ℂ) where
  toFun Φ := sectionValue μ c f Φ
  map_add' Φ Ψ := by
    funext g
    have hΦ := integrable_sectionIntegrand μ c ds hf hc Φ g
    have hΨ := integrable_sectionIntegrand μ c ds hf hc Ψ g
    simp only [sectionValue_eq_integral, Pi.add_apply, add_apply, mul_add]
    rw [integral_add hΦ hΨ, mul_add]
  map_smul' a Φ := by
    funext g
    simp only [sectionValue_eq_integral, Pi.smul_apply, smul_apply, smul_eq_mul,
      RingHom.id_apply]
    have h : (fun h : G => f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h *
        (a * Φ (rowPoint h.val g))) =
        fun h => a * (f h⁻¹ * determinantWeight c (((m : ℂ) + 1) / 2) h *
          Φ (rowPoint h.val g)) := by
      funext h
      ring
    rw [h, integral_const_mul]
    ring

/-- In the convergence half-plane, the section of every polynomial Gaussian test with a
principal-series lower input is a K-finite vector of the upper position principal series. -/
theorem gaussianSection_mem_kFinite (μ : Measure G) [μ.IsHaarMeasure] (c : RealCharacterData)
    (ds : List RealBlock) {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) (P : Poly) :
    sectionValue μ c f (gaussianPolynomial P) ∈ kFiniteFunctions
      (principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds))) K := by
  refine Submodule.mem_inf.mpr ⟨realGodementSchwartzSection m μ c ds f hf hc _, ?_⟩
  refine (mem_kFiniteVectors_iff _ _ _).mpr ?_
  let V := MvPolynomial.restrictTotalDegree (Coordinates m (m + 1)) ℂ P.totalDegree
  let T := (sectionLinear μ c ds hf hc).comp ((gaussianPolynomialLinear m (m + 1)).comp V.subtype)
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range T) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨q, hq, hA⟩ := rightTranslate_mem_range P k
  refine ⟨determinantWeight c ((m : ℂ) / 2) k.val • ⟨q, hq⟩, ?_⟩
  rw [map_smul]
  funext g
  change determinantWeight c ((m : ℂ) / 2) k.val * sectionValue μ c f (gaussianPolynomial q) g =
    sectionValue μ c f (gaussianPolynomial P) (g * k.val)
  rw [sectionValue_mul_right]
  congr 2
  funext x
  exact (hA x).symm

private def restrictK : (H → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun F k := F k.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem eq_of_restrictK {c : RealCharacterData} {ds : List RealBlock} {F U : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (hU : U ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (heq : restrictK U = restrictK F) : U = F := by
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  have hK : U k = F k := congrFun heq (⟨k, hk⟩ : K)
  rw [hU.2 a u k, hF.2 a u k, hK]

private theorem finiteDimensional_rightSpan_restrictK {V : Submodule ℂ (H → ℂ)} {v : H → ℂ}
    (hv : v ∈ kFiniteFunctions V K) : FiniteDimensional ℂ (rightSpan (restrictK v)) := by
  let W := Submodule.span ℂ (Set.range fun k : K => rightTranslation ℂ H k.val v)
  let : FiniteDimensional ℂ W := (mem_kFiniteVectors_iff _ _ _).mp (Submodule.mem_inf.mp hv).2
  refine Submodule.finiteDimensional_of_le (S₂ := W.map restrictK) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  exact ⟨rightTranslation ℂ H k.val v, Submodule.subset_span ⟨k, rfl⟩, rfl⟩

/-- Godement sections of polynomial Gaussian tests whose lower input is K-finite in the
lower position principal series. -/
def gaussianSections (μ : Measure G) (c : RealCharacterData) (ds : List RealBlock) :
    Set (H → ℂ) :=
  {F | ∃ (P : Poly) (f : G → ℂ),
    f ∈ kFiniteFunctions (principalSeries ℝ m (realPositionCharacter ds)) (unitaryCompact ℝ m) ∧
      F = sectionValue μ c f (gaussianPolynomial P)}

/-- In the real Godement convergence half-plane, the polynomial Gaussian Godement sections with
K-finite lower inputs span the K-finite upper position principal series. -/
def RealGodementGaussianSpanningStatement : Prop :=
  ∀ (m : ℕ) (μ : Measure (Langlands.GeneralLinear m ℝ)) [μ.IsHaarMeasure]
    (c : RealCharacterData) (ds : List RealBlock),
    (∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) →
    Submodule.span ℂ (gaussianSections μ c ds) =
      kFiniteFunctions (principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
        (unitaryCompact ℝ (m + 1))

private theorem spanning_aux (μ : Measure G) [μ.IsHaarMeasure] (c : RealCharacterData)
    (ds : List RealBlock)
    (hc : ∀ i : Fin m, (m : ℝ) + normExponent (realPositionExponent ds) m i ≤
      c.exponent.re + ((m : ℝ) + 1) / 2) :
    Submodule.span ℂ (gaussianSections μ c ds) =
      kFiniteFunctions (principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
        K := by
  let : μ.IsMulRightInvariant := (realMatrixHaar_symmetries μ).1
  let A := Submodule.span ℂ (gaussianSections μ c ds)
  have hA : A ≤ kFiniteFunctions
      (principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds))) K := by
    apply Submodule.span_le.mpr
    rintro _ ⟨P, f, hf, rfl⟩
    exact gaussianSection_mem_kFinite μ c ds (Submodule.mem_inf.mp hf).1 hc P
  refine le_antisymm hA (fun F hF => ?_)
  let κ := haarK (m + 1)
  let S : Set (K → ℂ) := restrictK '' gaussianSections μ c ds
  have hPair {f : G → ℂ} (hf : f ∈ principalSeries ℝ m (realPositionCharacter ds))
      (w : K → ℂ) (hw : Continuous w) :=
    realGodementGaussianPairing m μ c ds f hf hc κ w hw
  have hS : ∀ g ∈ S, FiniteDimensional ℂ (rightSpan g) ∧ rightSpan g ≤ Submodule.span ℂ S := by
    rintro _ ⟨_, ⟨P, f, hf, rfl⟩, rfl⟩
    refine ⟨finiteDimensional_rightSpan_restrictK
      (gaussianSection_mem_kFinite μ c ds (Submodule.mem_inf.mp hf).1 hc P), ?_⟩
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    obtain ⟨Q, -, hQ⟩ := exists_rightTranslate_gaussianPolynomial P k
    have he : rightTranslation ℂ K k (restrictK (sectionValue μ c f (gaussianPolynomial P))) =
        determinantWeight c ((m : ℂ) / 2) k.val •
          restrictK (sectionValue μ c f (gaussianPolynomial Q)) := by
      funext x
      change sectionValue μ c f (gaussianPolynomial P) (x.val * k.val) =
        determinantWeight c ((m : ℂ) / 2) k.val * sectionValue μ c f (gaussianPolynomial Q) x.val
      rw [sectionValue_mul_right]
      congr 2
      funext y
      exact hQ y
    change rightTranslation ℂ K k (restrictK (sectionValue μ c f (gaussianPolynomial P))) ∈
      Submodule.span ℂ S
    rw [he]
    exact (Submodule.span ℂ S).smul_mem _ (Submodule.subset_span ⟨_, ⟨Q, f, hf, rfl⟩, rfl⟩)
  have hInt : ∀ g ∈ S, ∀ w : K → ℂ, Continuous w → Integrable (fun k => w k * g k) κ := by
    rintro _ ⟨_, ⟨P, f, hf, rfl⟩, rfl⟩ w hw
    exact (hPair (Submodule.mem_inf.mp hf).1 w hw).1 _
  have hDetect : ∀ w : K → ℂ, Continuous w →
      (∀ g ∈ S, (∫ k, w k * g k ∂κ) = 0) → (∫ k, w k * restrictK F k ∂κ) = 0 := by
    intro w hw h0
    have hmem := realGodementFiniteGenerationKFiniteLower m μ c ds F hF
    clear hF
    have hcont {x : H → ℂ} (hx : x ∈ compactKFiniteLowerSectionSpan μ c ds) :
        Integrable (fun k : K => w k * x k.val) κ := by
      have hx' := compactSectionSpan_le_principalSeries μ c ds
        (compactKFiniteLowerSectionSpan_le μ c ds hx)
      exact (hw.mul (hx'.1.continuous.comp continuous_subtype_val)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    change (∫ k, w k * F k.val ∂κ) = 0
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, T, Φ, hf, hT, -, hΦ, hZero, rfl⟩ := hx
      have hΦc : HasCompactSupport Φ := HasCompactSupport.intro hT hZero
      exact (hPair (Submodule.mem_inf.mp hf).1 w hw).2
        (fun P => h0 _ ⟨_, ⟨P, f, hf, rfl⟩, rfl⟩) Φ hΦ.continuous.measurable hΦc
        (hΦ.continuous.bounded_above_of_compact_support hΦc)
    | zero => simp
    | add x y hx hy ihx ihy =>
      simp only [Pi.add_apply, mul_add]
      rw [integral_add (hcont hx) (hcont hy), ihx, ihy, add_zero]
    | smul a x hx ih =>
      simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm (w _) a]
      rw [integral_const_mul, ih, mul_zero]
  have hρF : restrictK F ∈ Submodule.span ℂ S :=
    compactPairingSpanning K κ (restrictK F) S
      ((Submodule.mem_inf.mp hF).1.1.continuous.comp continuous_subtype_val)
      (finiteDimensional_rightSpan_restrictK hF) hS hInt hDetect
  rw [← Submodule.map_span] at hρF
  obtain ⟨F', hF'A, hF'⟩ := hρF
  have he : F' = F := eq_of_restrictK (Submodule.mem_inf.mp hF).1
    (Submodule.mem_inf.mp (hA hF'A)).1 hF'
  exact he ▸ hF'A

theorem realGodementGaussianSpanning : RealGodementGaussianSpanningStatement :=
  fun _ μ _ c ds hc => spanning_aux μ c ds hc

end Langlands.Global.RankinSelbergGlobal.RealGodement
