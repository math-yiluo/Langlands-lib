import Langlands.Global.RankinSelberg.RealAdjacentSplitEquation
import Langlands.Global.RankinSelberg.RealAdjacentGaussianSplit
import Langlands.Global.RankinSelberg.RealGodementGaussianSpanning
import Langlands.Global.RankinSelberg.RealGodementSchwartzJoint
import Langlands.Global.RankinSelberg.RealGodementCanonicalModel
import Langlands.Global.RankinSelberg.RealLocalAdjacentIntegrals

/-! # The real normalized adjacent-rank equation in a strong chamber

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "G" => Langlands.GeneralLinear (r + 2) ℝ
local notation "gap" => Nat.lt_succ_self r

/-! ### The normalized adjacent-rank subspace -/

theorem realUnequalIntegrand_add' (W₁ W₂ : G → ℂ) (V : H → ℂ) (s : ℂ) :
    realUnequalIntegrand gap (W₁ + W₂) V s =
      realUnequalIntegrand gap W₁ V s + realUnequalIntegrand gap W₂ V s := by
  funext q
  simp only [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, Pi.add_apply]
  ring

theorem realUnequalIntegrand_smul' (c : ℂ) (W : G → ℂ) (V : H → ℂ) (s : ℂ) :
    realUnequalIntegrand gap (c • W) V s = c • realUnequalIntegrand gap W V s := by
  funext q
  simp only [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand, Pi.smul_apply, smul_eq_mul]
  ring

/-- For a fixed smaller function `V`, the larger functions whose adjacent-rank integrals
converge on a right half-plane and admit the normalized equation with strip growth for the
given data. -/
def adjacentGrowthSubmodule (D : RealQuotientMeasureData r) (b : ℝˣ) (V : H → ℂ)
    (xs ys xsd ysd : List RealBlock) (eb : ℝˣ) (c : ℝ≥0) (hc : 0 < c) (sign : ℂ) :
    Submodule ℂ (G → ℂ) where
  carrier := {W | ∃ σ : ℝ, (∀ s : ℂ, σ < s.re →
      Integrable (realUnequalIntegrand gap W V s) D.measure ∧
      Integrable (realUnequalIntegrand gap (ArchimedeanLocal.dualFunction (r + 2) W)
        (ArchimedeanLocal.dualFunction (r + 1) V) s) D.measure) ∧
    HasRealPairNormalizedGrowth xs ys xsd ysd eb c hc sign
      (realUnequalIntegral gap D W V) (realUnequalDualIntegral gap b D W V)}
  zero_mem' := by
    refine ⟨0, fun s _ => ⟨?_, ?_⟩, ?_⟩
    · have h : realUnequalIntegrand gap (0 : G → ℂ) V s = 0 := by
        funext q
        simp [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand]
      rw [h]
      exact integrable_zero _ _ _
    · have h : realUnequalIntegrand gap (ArchimedeanLocal.dualFunction (r + 2) (0 : G → ℂ))
          (ArchimedeanLocal.dualFunction (r + 1) V) s = 0 := by
        funext q
        simp [realUnequalIntegrand, ArchimedeanLocal.unequalIntegrand,
          ArchimedeanLocal.dualFunction]
      rw [h]
      exact integrable_zero _ _ _
    · refine HasRealPairNormalizedGrowth.zero.congr (τ := 0) (fun s _ => ?_) (fun s _ => ?_)
      · simp [realUnequalIntegral, ArchimedeanLocal.unequalIntegral,
          ArchimedeanLocal.unequalIntegrand]
      · rw [realUnequalDualIntegral_adjacent]
        simp [realUnequalIntegral, ArchimedeanLocal.unequalIntegral,
          ArchimedeanLocal.unequalIntegrand, ArchimedeanLocal.dualFunction]
  add_mem' := by
    rintro W₁ W₂ ⟨σ₁, hI₁, hG₁⟩ ⟨σ₂, hI₂, hG₂⟩
    refine ⟨max σ₁ σ₂, fun s hs => ?_, ?_⟩
    · obtain ⟨a₁, b₁⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
      obtain ⟨a₂, b₂⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
      have hd : ArchimedeanLocal.dualFunction (r + 2) (W₁ + W₂) =
          ArchimedeanLocal.dualFunction (r + 2) W₁ + ArchimedeanLocal.dualFunction (r + 2) W₂ := rfl
      rw [realUnequalIntegrand_add', hd, realUnequalIntegrand_add']
      exact ⟨a₁.add a₂, b₁.add b₂⟩
    · refine (hG₁.add hG₂).congr (τ := max σ₁ σ₂) (fun s hs => ?_) (fun s hs => ?_)
      · obtain ⟨a₁, -⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
        obtain ⟨a₂, -⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
        change realUnequalIntegral gap D W₁ V s + realUnequalIntegral gap D W₂ V s =
          realUnequalIntegral gap D (W₁ + W₂) V s
        unfold realUnequalIntegral ArchimedeanLocal.unequalIntegral
        change (∫ q, realUnequalIntegrand gap W₁ V s q ∂D.measure) +
            (∫ q, realUnequalIntegrand gap W₂ V s q ∂D.measure) =
          ∫ q, realUnequalIntegrand gap (W₁ + W₂) V s q ∂D.measure
        rw [realUnequalIntegrand_add']
        exact (integral_add a₁ a₂).symm
      · obtain ⟨-, b₁⟩ := hI₁ s ((le_max_left _ _).trans_lt hs)
        obtain ⟨-, b₂⟩ := hI₂ s ((le_max_right _ _).trans_lt hs)
        change realUnequalDualIntegral gap b D W₁ V s + realUnequalDualIntegral gap b D W₂ V s =
          realUnequalDualIntegral gap b D (W₁ + W₂) V s
        rw [realUnequalDualIntegral_adjacent, realUnequalDualIntegral_adjacent,
          realUnequalDualIntegral_adjacent]
        unfold realUnequalIntegral ArchimedeanLocal.unequalIntegral
        have hd : ArchimedeanLocal.dualFunction (r + 2) (W₁ + W₂) =
            ArchimedeanLocal.dualFunction (r + 2) W₁ + ArchimedeanLocal.dualFunction (r + 2) W₂ :=
          rfl
        change (∫ q, realUnequalIntegrand gap (ArchimedeanLocal.dualFunction (r + 2) W₁)
              (ArchimedeanLocal.dualFunction (r + 1) V) s q ∂D.measure) +
            (∫ q, realUnequalIntegrand gap (ArchimedeanLocal.dualFunction (r + 2) W₂)
              (ArchimedeanLocal.dualFunction (r + 1) V) s q ∂D.measure) =
          ∫ q, realUnequalIntegrand gap (ArchimedeanLocal.dualFunction (r + 2) (W₁ + W₂))
            (ArchimedeanLocal.dualFunction (r + 1) V) s q ∂D.measure
        rw [hd, realUnequalIntegrand_add']
        exact (integral_add b₁ b₂).symm
  smul_mem' := by
    rintro c₀ W ⟨σ, hI, hG⟩
    have hd : ArchimedeanLocal.dualFunction (r + 2) (c₀ • W) =
        c₀ • ArchimedeanLocal.dualFunction (r + 2) W := rfl
    refine ⟨σ, fun s hs => ?_, ?_⟩
    · obtain ⟨a₁, b₁⟩ := hI s hs
      rw [realUnequalIntegrand_smul', hd, realUnequalIntegrand_smul']
      exact ⟨a₁.smul c₀, b₁.smul c₀⟩
    · refine (hG.const_mul c₀).congr (τ := σ) (fun s _ => ?_) (fun s _ => ?_)
      · change c₀ * realUnequalIntegral gap D W V s = realUnequalIntegral gap D (c₀ • W) V s
        unfold realUnequalIntegral ArchimedeanLocal.unequalIntegral
        change c₀ * (∫ q, realUnequalIntegrand gap W V s q ∂D.measure) =
          ∫ q, realUnequalIntegrand gap (c₀ • W) V s q ∂D.measure
        rw [realUnequalIntegrand_smul']
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (integral_const_mul c₀ _).symm
      · change c₀ * realUnequalDualIntegral gap b D W V s =
          realUnequalDualIntegral gap b D (c₀ • W) V s
        rw [realUnequalDualIntegral_adjacent, realUnequalDualIntegral_adjacent, hd]
        unfold realUnequalIntegral ArchimedeanLocal.unequalIntegral
        change c₀ * (∫ q, realUnequalIntegrand gap (ArchimedeanLocal.dualFunction (r + 2) W)
              (ArchimedeanLocal.dualFunction (r + 1) V) s q ∂D.measure) =
          ∫ q, realUnequalIntegrand gap (c₀ • ArchimedeanLocal.dualFunction (r + 2) W)
            (ArchimedeanLocal.dualFunction (r + 1) V) s q ∂D.measure
        rw [realUnequalIntegrand_smul']
        simp only [Pi.smul_apply, smul_eq_mul]
        exact (integral_const_mul c₀ _).symm

/-! ### Spanning the canonical values by split Godement coefficients -/

section Span

open Langlands.Archimedean Langlands.Archimedean.GramFormula Langlands.Archimedean.PartialJacquet
open RealGodement (canonicalJacquetMap canonicalJacquetMap_agrees realSpectralChamber
  isStrictlyDominant_characterList sectionValue gaussianSections realGodementGaussianSpanning
  gaussianSection_mem_kFinite realGodementSchwartzJoint additiveJacquetIntegral
  realGodementSchwartzMajorant sectionValue_eq_integral determinantWeight rowPoint
  realGodementCanonicalModel)
open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial)

private theorem integrable_sectionIntegrand' (μ : Measure H) [μ.IsHaarMeasure]
    (c : RealCharacterData) (ds : List RealBlock) {f : H → ℂ}
    (hf : f ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds))
    (hc : ∀ i : Fin (r + 1), ((r + 1 : ℕ) : ℝ) + normExponent (realPositionExponent ds) (r + 1) i ≤
      c.exponent.re + (((r + 1 : ℕ) : ℝ) + 1) / 2)
    (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℝ, ℂ)) (g : G) :
    Integrable (fun h : H => f h⁻¹ * determinantWeight c ((((r + 1 : ℕ) : ℂ) + 1) / 2) h *
      Φ (rowPoint h.val g)) μ := by
  obtain ⟨b, hb, hB⟩ := realGodementSchwartzMajorant (r + 1) μ c ds f hf hc Φ {g}
    isCompact_singleton
  have hC : Continuous (fun h : H => f h⁻¹ * determinantWeight c ((((r + 1 : ℕ) : ℂ) + 1) / 2) h *
      Φ (rowPoint h.val g)) :=
    ((hf.1.continuous.comp continuous_inv).mul
      (RealGodement.contMDiff_determinantWeight c _).continuous).mul
      (Φ.continuous.comp (Units.continuous_val.matrix_mul continuous_const))
  refine hb.mono' hC.aestronglyMeasurable (ae_of_all _ fun h => ?_)
  simpa only [norm_mul] using hB g rfl h

/-- In the convergence half-plane the real Godement section is additive in finite sums of
Schwartz tests. -/
theorem sectionValue_finset_sum {ι : Type*} (T : Finset ι) (μ : Measure H) [μ.IsHaarMeasure]
    (c : RealCharacterData) (ds : List RealBlock) {f : H → ℂ}
    (hf : f ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds))
    (hc : ∀ i : Fin (r + 1), ((r + 1 : ℕ) : ℝ) + normExponent (realPositionExponent ds) (r + 1) i ≤
      c.exponent.re + (((r + 1 : ℕ) : ℝ) + 1) / 2)
    (Φ : ι → 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℝ, ℂ)) :
    sectionValue μ c f (⇑(∑ i ∈ T, Φ i)) = ∑ i ∈ T, sectionValue μ c f (Φ i) := by
  funext g
  simp only [sectionValue_eq_integral, Finset.sum_apply, sum_apply, Finset.mul_sum]
  rw [← Finset.mul_sum, ← integral_finsetSum T
    (fun i _ => integrable_sectionIntegrand' μ c ds hf hc (Φ i) g)]

/-- The split Godement coefficients attached to the tail of an inducing parameter: functions of
the uniform model of the larger character list that are Godement coefficients of separated tests,
whose square factor is a polynomial Gaussian test, over values of the smaller canonical map. -/
def adjacentSplitGenerators (D : RealQuotientMeasureData r) (a : ℝˣ) (P : Fin (r + 2) → Fin 2)
    (Z : Fin (r + 2) → ℂ) : Set (G → ℂ) :=
  {W | W ∈ realUniformWhittakerModel (r + 1) (RealGodementProfiles.characterList P Z) (-a) ∧
    ∃ (f : Automorphic.realStandardKFinite (r + 1)
        (RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z)))
      (q : MvPolynomial (Coordinates (r + 1) (r + 1)) ℂ) (φ : 𝓢(Fin (r + 1) → ℝ, ℂ)),
      W = realAdjacentGodementCoefficient D a (realColumnProduct (gaussianPolynomial q) φ)
        (canonicalJacquetMap a (Fin.tail P) (Fin.tail Z) f)
        (RealJacquetFrobenius.charData (P 0) (Z 0))}

theorem isCharacterList_characterList {n : ℕ} (p : Fin n → Fin 2) (z : Fin n → ℂ) :
    RealStrictCharacterLanglandsQuotient.IsCharacterList (RealGodementProfiles.characterList p z) :=
  fun b hb => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hb
    exact ⟨x, rfl⟩

theorem characterList_succ (P : Fin (r + 2) → Fin 2) (Z : Fin (r + 2) → ℂ) :
    RealGodementProfiles.characterList P Z =
      RealBlock.character (RealJacquetFrobenius.charData (P 0) (Z 0)) ::
        RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z) := by
  simp only [RealGodementProfiles.characterList, List.ofFn_succ, List.map_cons]
  rfl

theorem realStandardKFinite_characterList {n : ℕ} (p : Fin n → Fin 2) (z : Fin n → ℂ) :
    Automorphic.realStandardKFinite n (RealGodementProfiles.characterList p z) =
      kFiniteFunctions (principalSeries ℝ n
        (realPositionCharacter (RealGodementProfiles.characterList p z))) (unitaryCompact ℝ n) := by
  unfold Automorphic.realStandardKFinite
  rw [RealStrictCharacterLanglandsQuotient.realStandardModule_eq (isCharacterList_characterList p z)]

/-- In the Godement convergence region of a strict chamber, every value of the larger canonical
map lies in the span of the split Godement coefficients. -/
theorem canonicalJacquetMap_mem_span_adjacentSplitGenerators (D : RealQuotientMeasureData r)
    (a : ℝˣ) (P : Fin (r + 2) → Fin 2) (Z : Fin (r + 2) → ℂ)
    (hZ : Z ∈ realSpectralChamber (r + 1))
    (hc : ∀ i : Fin (r + 1), ((r + 1 : ℕ) : ℝ) + normExponent (realPositionExponent
        (RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z))) (r + 1) i ≤
      (RealJacquetFrobenius.charData (P 0) (Z 0)).exponent.re + (((r + 1 : ℕ) : ℝ) + 1) / 2)
    (F : Automorphic.realStandardKFinite (r + 2) (RealGodementProfiles.characterList P Z)) :
    canonicalJacquetMap a P Z F ∈ Submodule.span ℂ (adjacentSplitGenerators D a P Z) := by
  classical
  let μ := D.groupHaar
  have : μ.IsHaarMeasure := D.groupHaar_isHaar
  let c := RealJacquetFrobenius.charData (P 0) (Z 0)
  let ds := RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z)
  have hlist := characterList_succ P Z
  let V := Automorphic.realStandardKFinite (r + 2) (RealGodementProfiles.characterList P Z)
  have hV : V = kFiniteFunctions (principalSeries ℝ (r + 2)
      (realPositionCharacter (RealBlock.character c :: ds))) (unitaryCompact ℝ (r + 2)) := by
    change Automorphic.realStandardKFinite (r + 2) (RealGodementProfiles.characterList P Z) = _
    rw [realStandardKFinite_characterList, hlist]
  have hspan := realGodementGaussianSpanning (r + 1) μ c ds hc
  have hZt : Fin.tail Z ∈ realSpectralChamber r := fun i => hZ i.succ
  have hDom : IsStrictlyDominant (realPositionExponent (RealBlock.character c :: ds)) (r + 1) := by
    have h := isStrictlyDominant_characterList P hZ
    rwa [hlist] at h
  let J := canonicalJacquetMap a P Z
  let S := Submodule.span ℂ (adjacentSplitGenerators D a P Z)
  let T := (S.comap J).map V.subtype
  have hgen : gaussianSections μ c ds ⊆ T := by
    rintro _ ⟨Q, f, hf, rfl⟩
    have hfps : f ∈ principalSeries ℝ (r + 1) (realPositionCharacter ds) := hf.1
    have hft : f ∈ Automorphic.realStandardKFinite (r + 1) ds := by
      rw [realStandardKFinite_characterList]
      exact hf
    let U := canonicalJacquetMap a (Fin.tail P) (Fin.tail Z) ⟨f, hft⟩
    have hU : U = additiveJacquetIntegral a f :=
      canonicalJacquetMap_agrees a (Fin.tail P) hZt ⟨f, hft⟩
    let sect (u : Coordinates (r + 1) (r + 1 + 1) →₀ ℕ) : G → ℂ :=
      sectionValue μ c f (gaussianPolynomial (MvPolynomial.monomial u (Q.coeff u)))
    have hmem (u : Coordinates (r + 1) (r + 1 + 1) →₀ ℕ) : sect u ∈ V := by
      rw [hV]
      exact gaussianSection_mem_kFinite μ c ds hfps hc _
    have hQ : sectionValue μ c f (gaussianPolynomial Q) ∈ V := by
      rw [hV]
      exact gaussianSection_mem_kFinite μ c ds hfps hc _
    refine ⟨⟨_, hQ⟩, ?_, rfl⟩
    have hdecomp : (⟨_, hQ⟩ : V) = ∑ u ∈ Q.support, ⟨sect u, hmem u⟩ := by
      apply Subtype.ext
      simp only [Submodule.coe_sum]
      rw [gaussianPolynomial_sum_monomials Q]
      exact sectionValue_finset_sum Q.support μ c ds hfps hc _
    change J ⟨_, hQ⟩ ∈ S
    rw [hdecomp, map_sum]
    refine S.sum_mem fun u _ => Submodule.subset_span ⟨Submodule.mem_iSup_of_mem J
      (Submodule.mem_iSup_of_mem (realGodementCanonicalModel (r + 1) a P Z) ⟨_, rfl⟩), ?_⟩
    refine ⟨⟨f, hft⟩, MvPolynomial.monomial (leadingExponents u) (Q.coeff u),
      columnGaussianMonomial fun i => u (i, Fin.last (r + 1)), ?_⟩
    rw [← gaussianMonomial_eq_realColumnProduct]
    funext g
    change canonicalJacquetMap a P Z ⟨sect u, hmem u⟩ g = _
    rw [canonicalJacquetMap_agrees a P hZ]
    have hjoint := (realGodementSchwartzJoint r D a c ds f hfps hDom hc
      (gaussianPolynomial (MvPolynomial.monomial u (Q.coeff u))) g).2
    change additiveJacquetIntegral a (sectionValue μ c f _) g = _
    rw [hjoint]
    change _ = realAdjacentGodementCoefficient D a _ U c g
    rw [hU]
    rfl
  have hle : Submodule.span ℂ (gaussianSections μ c ds) ≤ T := Submodule.span_le.mpr hgen
  have hF : F.val ∈ T := hle (by rw [hspan, ← hV]; exact F.2)
  obtain ⟨v, hv, he⟩ := hF
  have hvF : v = F := Subtype.ext he
  rw [← hvF]
  exact hv

end Span

/-! ### The normalized equation in the chamber -/

section Chamber

open Langlands.Archimedean Langlands.Archimedean.GramFormula Langlands.Archimedean.PartialJacquet
open Langlands.HarmonicAnalysis
open RealGodement (canonicalJacquetMap realSpectralChamber realGodementCanonicalModel
  realRectangularSchwartzFourier hasRealPairNormalizedGrowth_scale_congr realRowSchwartzFourier
  exists_realCompactMatrixWeight realLocalCompactFourierWeight realRectangularSchwartzFourier_apply)
open RealGodementGaussianPolynomial (Coordinates gaussianPolynomial)

local notation "O" => Matrix.unitaryGroup (Fin (r + 1)) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ

/-- On orthogonal matrices the compact translate does not see the difference between a real
character and its inverse, since the determinant is `±1`. -/
theorem realCompactMatrixTranslate_inverse_of_mem {n : ℕ} (c : RealCharacterData)
    (Ψ : Matrix (Fin n) (Fin n) ℝ → ℂ) {g : Langlands.GeneralLinear n ℝ}
    (hg : g ∈ unitaryCompact ℝ n) (A : Matrix (Fin n) (Fin n) ℝ) :
    RealGodement.realCompactMatrixTranslate c.inverse Ψ g A =
      RealGodement.realCompactMatrixTranslate c Ψ g A := by
  unfold RealGodement.realCompactMatrixTranslate
  congr 1
  have hinv : g⁻¹ ∈ unitaryCompact ℝ n := (unitaryCompact ℝ n).inv_mem hg
  have habs := MaximalParabolicIntegration.abs_det_unitary (⟨g⁻¹, hinv⟩ : unitaryCompact ℝ n)
  set u := GeneralLinear.determinant g⁻¹ with hu_def
  have hu : u * u = 1 := by
    apply Units.ext
    have hval : (u : ℝ) = ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ).det :=
      rfl
    rw [Units.val_mul, Units.val_one, hval, ← sq, ← sq_abs]
    simp only [habs, one_pow]
  have hc : c.character u * c.character u = 1 := by rw [← map_mul, hu, map_one]
  rw [RealCharacterData.inverse_character]
  change (((c.character u)⁻¹ : ℂˣ) : ℂ) = (c.character u : ℂ)
  rw [inv_eq_of_mul_eq_one_right hc]

set_option synthInstance.maxHeartbeats 200000 in
variable (r) in
/-- The compact projection of standard vectors along the orthogonal group, for uniform real
Whittaker maps: averaging translates of a standard vector against a weight whose left translates
span a finite-dimensional space gives a standard vector, compatibly with the map. -/
def RealOrthogonalCompactProjectionPremise : Prop :=
  ∀ (es : List RealBlock) (a : ℝˣ) (κ : Matrix.unitaryGroup (Fin (r + 1)) ℝ → ℂ), Continuous κ →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range
      fun x : Matrix.unitaryGroup (Fin (r + 1)) ℝ => fun k => κ (x⁻¹ * k))) →
  ∀ (B : Automorphic.realStandardKFinite (r + 1) es →ₗ[ℂ]
      (Langlands.GeneralLinear (r + 1) ℝ → ℂ)),
    IsRealUniformWhittakerIntertwiner r es a B →
  ∀ (f : Automorphic.realStandardKFinite (r + 1) es) (g : Langlands.GeneralLinear (r + 1) ℝ),
    ∃ p : Automorphic.realStandardKFinite (r + 1) es,
      (∀ x : Matrix.unitaryGroup (Fin (r + 1)) ℝ,
        (p : Langlands.GeneralLinear (r + 1) ℝ → ℂ) (Unitary.toUnits x) =
          ∫ k, κ k * (f : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
            (Unitary.toUnits x * Unitary.toUnits k * g) ∂Measure.haar) ∧
      ∀ x : Langlands.GeneralLinear (r + 1) ℝ,
        B p x = ∫ k, κ k * B f (x * Unitary.toUnits k * g) ∂Measure.haar

/-- In the Godement convergence region of a strict chamber, the larger canonical values lie in
the normalized adjacent-rank subspace attached to every value of a smaller uniform Whittaker
map, given compact projection at the smaller rank and the smaller equal-rank growth. -/
theorem realAdjacentCanonicalChamberGrowth (hProjO : RealOrthogonalCompactProjectionPremise r)
    (hEqual : RealLocalEqualCharacterGrowthAtRank r)
    (D : RealQuotientMeasureData r) (a : ℝˣ) (P : Fin (r + 2) → Fin 2) (Z : Fin (r + 2) → ℂ)
    (hZ : Z ∈ realSpectralChamber (r + 1))
    (hc : ∀ i : Fin (r + 1), ((r + 1 : ℕ) : ℝ) + normExponent (realPositionExponent
        (RealGodementProfiles.characterList (Fin.tail P) (Fin.tail Z))) (r + 1) i ≤
      (RealJacquetFrobenius.charData (P 0) (Z 0)).exponent.re + (((r + 1 : ℕ) : ℝ) + 1) / 2)
    (fs : List RealCharacterData) (hfs : fs.length = r + 1)
    (B : Automorphic.realStandardKFinite (r + 1) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner r (fs.map RealBlock.character) a B)
    (v : Automorphic.realStandardKFinite (r + 1) (fs.map RealBlock.character))
    (F : Automorphic.realStandardKFinite (r + 2) (RealGodementProfiles.characterList P Z)) :
    canonicalJacquetMap a P Z F ∈ adjacentGrowthSubmodule D (-a) (B v)
      (RealGodementProfiles.characterList P Z) (fs.map RealBlock.character)
      ((RealGodementProfiles.characterList P Z).map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((determinant (RealGodementProfiles.characterList P Z) (-1) : ℂ) ^ (r + 1) *
        (determinant (fs.map RealBlock.character) (-1) : ℂ)) := by
  classical
  refine Submodule.span_le.mpr ?_
    (canonicalJacquetMap_mem_span_adjacentSplitGenerators D a P Z hZ hc F)
  rintro _ ⟨hWmodel, f₀, q, φ, rfl⟩
  let c := RealJacquetFrobenius.charData (P 0) (Z 0)
  let cs : List RealCharacterData :=
    List.ofFn fun i => RealJacquetFrobenius.charData (Fin.tail P i) (Fin.tail Z i)
  have hcs : cs.length = r + 1 := List.length_ofFn
  let es := fs.map RealBlock.character
  let U := canonicalJacquetMap a (Fin.tail P) (Fin.tail Z) f₀
  have hU : U ∈ realUniformWhittakerModel r (cs.map RealBlock.character) (-a) :=
    Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem
      (realGodementCanonicalModel r a (Fin.tail P) (Fin.tail Z)) ⟨f₀, rfl⟩)
  have hV : B v ∈ realUniformWhittakerModel r es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨v, rfl⟩)
  -- the compact weight
  let ν : Measure O := Measure.haar
  let Ψ : 𝓢(Mat, ℂ) := gaussianPolynomial q
  have hmem (k : O) : (Unitary.toUnits k : H) ∈ unitaryCompact ℝ (r + 1) := k.property
  have hsurj (g : H) (hg : g ∈ unitaryCompact ℝ (r + 1)) : ∃ k : O, Unitary.toUnits k = g :=
    ⟨⟨g.val, hg⟩, Units.ext rfl⟩
  have hFfin := finiteDimensional_gaussianPolynomial_left (Unitary.toUnits : O →* H) hmem q
  obtain ⟨κ, hκ, hκfin, hrep⟩ := exists_realCompactMatrixWeight ν Unitary.toUnits
    continuous_unitary_toUnits c Ψ Ψ.continuous hFfin
  have hrep' (A : Mat) : ∫ k, κ k * RealGodement.realCompactMatrixTranslate c.inverse Ψ
      (Unitary.toUnits k) A ∂ν = Ψ A := by
    rw [← hrep A]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    change κ k * _ = κ k * _
    rw [realCompactMatrixTranslate_inverse_of_mem c Ψ (hmem k)]
  have hΨint : Integrable (Ψ : Mat → ℂ)
      (RankinSelberg.rectangularMeasure (realSelfDualMeasure a) (r + 1) (r + 1)) := by
    let νR := realSelfDualMeasure a
    let : νR.measure.IsAddHaarMeasure := νR.isAddHaar
    let : (RankinSelberg.rectangularMeasure νR (r + 1) (r + 1)).IsAddHaarMeasure :=
      RankinSelberg.rectangularMeasure_isAddHaar νR (r + 1) (r + 1)
    exact Ψ.integrable
  have hrepd (A : Mat) : ∫ k, κ k * RealGodement.realCompactMatrixTranslate c.inverse
      (realRectangularSchwartzFourier a Ψ) (Unitary.toUnits k) A ∂ν =
        realRectangularSchwartzFourier a Ψ A := by
    have hF : (realRectangularSchwartzFourier a Ψ : Mat → ℂ) =
        rectangularFourierIntegral (realScaledCharacter a) (realSelfDualMeasure a) Ψ :=
      funext (realRectangularSchwartzFourier_apply a Ψ)
    rw [hF]
    exact realLocalCompactFourierWeight a ν κ hκ c.inverse Ψ hΨint hrep' A
  have hFdfin := finiteDimensional_fourier_left (Unitary.toUnits : O →* H) hmem a Ψ hFfin
  -- the smaller equal-rank inputs
  have hLower (V : H → ℂ) (hV' : V ∈ realUniformWhittakerModel r es a) :
      HasRealPairNormalizedGrowth (cs.map RealBlock.character) es
        ((cs.map RealBlock.character).map RealLocalJacquet.dualBlock)
        (es.map RealLocalJacquet.dualBlock) a
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
        ((determinant (cs.map RealBlock.character) (-1) : ℂ) ^ r)
        (realEqualIntegral D U V (realRowSchwartzFourier (r + 1) a φ))
        (realEqualDualIntegral a D U V (realRowSchwartzFourier (r + 1) a φ)) := by
    have h := hEqual (cs.map RealBlock.character) es ⟨cs, rfl⟩ ⟨fs, rfl⟩
      (by rw [realRank_map_character, hcs]) (by rw [realRank_map_character, hfs]) (-a) D U V
      (realRowSchwartzFourier (r + 1) a φ) hU (by rw [neg_neg]; exact hV')
    rw [neg_neg] at h
    have hscale : NNReal.sqrt ‖((-a : ℝˣ) : ℝ)‖₊ = NNReal.sqrt ‖(a : ℝ)‖₊ := by
      rw [Units.val_neg, nnnorm_neg]
    exact hasRealPairNormalizedGrowth_scale_congr hscale h
  have hNorm := realAdjacentSplitGrowth D ν (Unitary.toUnits : O →* H) continuous_unitary_toUnits
    hmem hsurj κ hκ hκfin a c Ψ φ hFfin hFdfin hrep hrepd cs fs hcs hfs U hU v B hB
    (fun g => hProjO es a κ hκ hκfin B hB v g) hLower
  -- convergence
  have hWreg := realUniformWhittakerRegularity (r + 1) _ (-a) _ hWmodel
  have hVreg := realUniformWhittakerRegularity r es a (B v) hV
  obtain ⟨σ, h₁, h₂, -, -⟩ := realUnequalPairConvergence (r + 1) r gap D (-a) _ (B v)
    hWreg.1 hWreg.2 (by rw [neg_neg]; exact hVreg.1) hVreg.2
  refine ⟨σ, fun s hs => ⟨h₁ s hs,
    (integrable_realUnequalDualKernel_adjacent_iff (-a) D _ (B v) s).mp (h₂ s hs)⟩, ?_⟩
  rw [characterList_succ P Z]
  exact hNorm

end Chamber

end Langlands.Global.RankinSelbergGlobal.RealJacquet
