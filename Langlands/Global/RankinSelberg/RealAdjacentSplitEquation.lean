import Langlands.Global.RankinSelberg.RealAdjacentCompactAverage
import Langlands.Global.RankinSelberg.RealAdjacentSquareGrowth
import Langlands.Global.RankinSelberg.RealAdjacentNormalizedProducts
import Langlands.Global.RankinSelberg.RealAdjacentGodementHalfPlane
import Langlands.Global.RankinSelberg.RealPlaceEqualReflection
import Langlands.Global.RankinSelberg.RealLocalUniformCentralCharacter
import Langlands.Global.RankinSelberg.RealUniformWhittakerDual
import Langlands.Global.RankinSelberg.RealGodementRowFourierInversion

/-! # The real adjacent-rank equation for a split Godement coefficient

See the paired Markdown file.
-/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal
open Langlands.RankinSelberg (LeftUnipotentQuotient lastRow)
open Langlands.LocalFactor Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal RealEqualConvergence
open RealGodement (realCompactMatrixTranslate realRectangularSchwartzFourier realRowSchwartzFourier)

attribute [local instance] archimedeanEquationRealGLMeasurable
  archimedeanEquationRealGLBorel archimedeanEquationRealNMeasurable
  archimedeanEquationRealNBorel archimedeanEquationRealQMeasurable
  archimedeanEquationRealQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℝ
local notation "Q" => LeftUnipotentQuotient r ℝ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "Rows" => Fin (r + 1) → ℝ
local notation "ι" => GeneralLinear.inverseTranspose (r + 1) ℝ
local notation "dualH" => ArchimedeanLocal.dualFunction (r + 1)

local instance splitMatrixSecondCountable : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance splitGLSecondCountable : SecondCountableTopology H :=
  (Units.isOpenEmbedding_val (R := Mat)).isInducing.secondCountableTopology
local instance splitQuotientSigmaCompact : SigmaCompactSpace Q := by
  have hq := QuotientIntegration.leftQuotient_isOpenQuotientMap N
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hq.surjective]
  exact isSigmaCompact_range hq.continuous

/-! ### Uniform model helpers -/

theorem splitModel_regular {ds : List RealBlock} {a : ℝˣ} {U : H → ℂ}
    (hU : U ∈ realUniformWhittakerModel r ds a) :
    U ∈ RealLocalWhittaker.regularFunctions r a :=
  (realUniformWhittakerRegularity r ds a U hU).1 []

theorem splitModel_gauge {ds : List RealBlock} {a : ℝˣ} {U : H → ℂ}
    (hU : U ∈ realUniformWhittakerModel r ds a) : HasGauge U :=
  RealWhittakerGauge.exists_gauge_bound (realUniformWhittakerRegularity r ds a U hU).1
    (realUniformWhittakerRegularity r ds a U hU).2

theorem splitModel_growth {ds : List RealBlock} {a : ℝˣ} {V : H → ℂ}
    (hV : V ∈ realUniformWhittakerModel r ds a) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ M := by
  obtain ⟨M, hM⟩ := (realUniformWhittakerRegularity r ds a V hV).2
  obtain ⟨C, hC, hb⟩ := hM []
  exact ⟨C, M, hC, hb⟩

theorem splitPair_invariant {a : ℝˣ} {U V : H → ℂ}
    (hU : U ∈ RealLocalWhittaker.regularFunctions r (-a))
    (hV : V ∈ RealLocalWhittaker.regularFunctions r a) :
    ∀ u ∈ N, ∀ g z : H, U (u * g) * V (u * g * z) = U g * V (g * z) := by
  intro u hu g z
  rw [hU.1 u hu g, mul_assoc u g z, hV.1 u hu (g * z)]
  linear_combination (U g * V (g * z)) * realWhittakerCharacter_mul_neg a u

/-- The central element `-1` acts on a uniform model element by the determinant sign. -/
theorem splitModel_minusOne {ds : List RealBlock} (hds : realRank ds = r + 1) {a : ℝˣ}
    {U : H → ℂ} (hU : U ∈ realUniformWhittakerModel r ds a) (g : H) :
    U (g * -1) = (determinant ds (-1) : ℂ) * U g := by
  have h := realUniformWhittakerCentralCharacter r ds hds a U hU (-1) g
  have hs : (GeneralLinear.scalar (-1 : ℝˣ) : H) = -1 := by
    apply Units.ext
    simp only [GeneralLinear.scalar]
    simp only [Units.val_neg, Units.val_one]
    change Matrix.diagonal (fun i => -((fun _ => (1 : ℝ)) i)) = -1
    rw [← Matrix.diagonal_neg, Matrix.diagonal_one]
  rwa [hs] at h

/-- The determinant sign of a list of real characters squares to one. -/
theorem determinant_characterList_sq (cs : List RealCharacterData) :
    ((determinant (cs.map RealBlock.character) (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
  induction cs with
  | nil => simp [determinant]
  | cons c cs ih =>
    have hcons : determinant ((c :: cs).map RealBlock.character) (-1) =
        c.character (-1) * determinant (cs.map RealBlock.character) (-1) := rfl
    have hc : ((c.character (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
    rw [hcons, Units.val_mul, mul_pow, hc, ih, one_mul]

/-- The dual character list has the same determinant sign. -/
theorem determinant_dualCharacterBlocks (cs : List RealCharacterData) :
    determinant (RealUniformWhittakerDual.dualCharacterBlocks cs) (-1) =
      determinant (cs.map RealBlock.character) (-1) := by
  have hinv (c : RealCharacterData) : c.inverse.character (-1) = c.character (-1) := by
    rw [RealCharacterData.inverse_character]
    change (c.character (-1))⁻¹ = c.character (-1)
    have h2 : c.character (-1) * c.character (-1) = 1 := by
      rw [← map_mul, neg_one_mul, neg_neg, map_one]
    exact inv_eq_of_mul_eq_one_right h2
  unfold determinant RealUniformWhittakerDual.dualCharacterBlocks
  simp only [List.map_map, Function.comp_def, List.map_reverse, List.prod_reverse]
  congr 1
  refine List.map_congr_left fun c _ => ?_
  exact hinv c

/-! ### The dual equal-rank integral after row Fourier inversion -/

/-- With the Fourier test of the original row test, the dual equal-rank integral of `(U, V)` is
the ordinary equal-rank integral of the duals with the original row test, up to the central
sign `k` of the dual pair. -/
theorem realEqualIntegral_dual_reflect (D : RealQuotientMeasureData r) (U V : H → ℂ)
    (hP : ∀ (u : N) (g : H), dualH U (u.val * g) * dualH V (u.val * g) = dualH U g * dualH V g)
    (k : ℂ) (hk : k ^ 2 = 1) (hPk : ∀ g : H, dualH U (g * -1) * dualH V (g * -1) =
      k * (dualH U g * dualH V g))
    (a : ℝˣ) (φ : 𝓢(Rows, ℂ)) (s : ℂ) :
    realEqualIntegral D (dualH U) (dualH V) φ s =
      k * realEqualDualIntegral a D U V (realRowSchwartzFourier (r + 1) a φ) s := by
  let P : H → ℂ := fun g => dualH U g * dualH V g
  have h := (RealPlaceReflection.reflection P hP k hk hPk a D
    (realRowSchwartzFourier (r + 1) a φ) s).2
  have hinv : realFourierTransform (-a) (realRowSchwartzFourier (r + 1) a φ) = (φ : Rows → ℂ) := by
    funext y
    rw [← RealGodement.realRowSchwartzFourier_apply, RealGodement.realRowSchwartzFourier_neg_comp]
  rw [hinv] at h
  exact h

/-! ### Expansion of the unfolded integral -/

/-- On a right half-plane, the unfolded adjacent integral of `(U, V)` with a reproduced square
test is the finite sum of smaller equal-rank integrals times matrix integrals given by a compact
expansion of the right translates of `V`. -/
theorem realAdjacentUnfoldedIntegral_expansion (D : RealQuotientMeasureData r)
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν]
    (iK : K →* H) (hiK : Continuous iK) (hdet : ∀ k, |(iK k).val.det| = 1)
    (κ : K → ℂ) (hκ : Continuous κ) (c : RealCharacterData) (F : 𝓢(Mat, ℂ))
    (hfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : K => fun X : Mat => F (((iK k)⁻¹).val * X))))
    (hrep : ∀ A, ∫ k, κ k * realCompactMatrixTranslate c F (iK k) A ∂ν = F A)
    (f : Rows → ℂ) (hf : Continuous f) (hfd : HasRapidDecay f) (U V : H → ℂ)
    (hU : Continuous U) (hV : Continuous V)
    (hinv : ∀ u ∈ N, ∀ g z : H, U (u * g) * V (u * g * z) = U g * V (g * z))
    (hgU : HasGauge U) (hVg : ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ g, ‖V g‖ ≤ C * realMatrixHeight g ^ M)
    (m : ℕ) (W C : Fin m → H → ℂ)
    (hexp : ∀ x z, (∫ k, κ k * V (x * iK k * z) ∂ν) = ∑ j, W j x * C j z)
    (hW : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ j, Integrable (realEqualIntegrand U (W j) f s) D.measure)
    (hC : ∃ σ : ℝ, ∀ s : ℂ, σ < s.re → ∀ j,
      Integrable (fun z => realAdjacentMatrixWeight c.character.toMonoidHom F s z * C j z)
        D.groupHaar) :
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      realAdjacentUnfoldedIntegral D c.character.toMonoidHom F f U V s =
        ∑ j, realEqualIntegral D U (W j) f s *
          ∫ z, realAdjacentMatrixWeight c.character.toMonoidHom F s z * C j z ∂D.groupHaar := by
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  obtain ⟨σ₁, h₁⟩ := realAdjacentConvergence (r := r) D c F f U V hU hV hf hfd hinv hgU hVg
  obtain ⟨σ₂, h₂⟩ := realAdjacentCompactAverage (r := r) D ν iK hiK hdet κ hκ c F hfin hrep f hf
    hfd U V hU hV hinv hgU hVg
  obtain ⟨σ₃, h₃⟩ := hW
  obtain ⟨σ₄, h₄⟩ := hC
  refine ⟨max (max σ₁ σ₂) (max σ₃ σ₄), fun s hs => ?_⟩
  simp only [max_lt_iff] at hs
  obtain ⟨⟨hs₁, hs₂⟩, hs₃, hs₄⟩ := hs
  let η := c.character.toMonoidHom
  have hK := h₁ s hs₁
  have hjoint : realAdjacentUnfoldedIntegral D η F f U V s =
      ∫ p, realAdjacentUnfoldedKernel η F f U V s p ∂(D.measure.prod D.groupHaar) := by
    rw [integral_prod_symm _ hK]
    unfold realAdjacentUnfoldedIntegral realEqualIntegral ArchimedeanLocal.equalIntegral
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    dsimp only
    rw [← integral_mul_const]
    rfl
  rw [hjoint, (h₂ s hs₂).2]
  exact realAdjacentProductExpansion (r := r) D η F f s U m W C
    (fun x z => ∫ k, κ k * V (x * iK k * z) ∂ν) hexp (h₄ s hs₄) (h₃ s hs₃)

/-! ### The split adjacent-rank equation -/

/-- The normalized adjacent-rank equation for the Godement coefficient of a separated test
`[A | x] ↦ F(A) φ(x)` and a smaller Whittaker function `U`, against the value of a uniform
Whittaker map on a standard vector. The inputs are the smaller equal-rank normalized equations
on the row Fourier test, a compact weight reproducing `F` and its Fourier transform, and the
compact projection of the standard vector. -/
theorem realAdjacentSplitGrowth (D : RealQuotientMeasureData r)
    {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsFiniteMeasure ν] [ν.IsHaarMeasure]
    (iK : K →* H) (hiK : Continuous iK)
    (hmem : ∀ k, iK k ∈ Langlands.Archimedean.unitaryCompact ℝ (r + 1))
    (hsurj : ∀ g ∈ Langlands.Archimedean.unitaryCompact ℝ (r + 1), ∃ k, iK k = g)
    (κ : K → ℂ) (hκ : Continuous κ)
    (hκfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun x : K => fun k => κ (x⁻¹ * k))))
    (a : ℝˣ) (c : RealCharacterData) (F : 𝓢(Mat, ℂ)) (φ : 𝓢(Rows, ℂ))
    (hFfin : FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : K => fun X : Mat => F (((iK k)⁻¹).val * X))))
    (hFdfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K => fun X : Mat =>
      realRectangularSchwartzFourier a F (((iK k)⁻¹).val * X))))
    (hrep : ∀ A, ∫ k, κ k * realCompactMatrixTranslate c F (iK k) A ∂ν = F A)
    (hrepd : ∀ A, ∫ k, κ k * realCompactMatrixTranslate c.inverse
      (realRectangularSchwartzFourier a F) (iK k) A ∂ν = realRectangularSchwartzFourier a F A)
    (cs fs : List RealCharacterData) (hcs : cs.length = r + 1) (hfs : fs.length = r + 1)
    (U : H → ℂ) (hU : U ∈ realUniformWhittakerModel r (cs.map RealBlock.character) (-a))
    (f : Automorphic.realStandardKFinite (r + 1) (fs.map RealBlock.character))
    (B : Automorphic.realStandardKFinite (r + 1) (fs.map RealBlock.character) →ₗ[ℂ] (H → ℂ))
    (hB : IsRealUniformWhittakerIntertwiner r (fs.map RealBlock.character) a B)
    (hProj : ∀ g : H, ∃ p : Automorphic.realStandardKFinite (r + 1) (fs.map RealBlock.character),
      (∀ x : K, (p : H → ℂ) (iK x) = ∫ k, κ k * (f : H → ℂ) (iK x * iK k * g) ∂ν) ∧
      ∀ x : H, B p x = ∫ k, κ k * B f (x * iK k * g) ∂ν)
    (hLower : ∀ V ∈ realUniformWhittakerModel r (fs.map RealBlock.character) a,
      HasRealPairNormalizedGrowth (cs.map RealBlock.character) (fs.map RealBlock.character)
        ((cs.map RealBlock.character).map RealLocalJacquet.dualBlock)
        ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
        (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
        ((determinant (cs.map RealBlock.character) (-1) : ℂ) ^ r)
        (realEqualIntegral D U V (realRowSchwartzFourier (r + 1) a φ))
        (realEqualDualIntegral a D U V (realRowSchwartzFourier (r + 1) a φ))) :
    HasRealPairNormalizedGrowth (RealBlock.character c :: cs.map RealBlock.character)
      (fs.map RealBlock.character)
      ((RealBlock.character c :: cs.map RealBlock.character).map RealLocalJacquet.dualBlock)
      ((fs.map RealBlock.character).map RealLocalJacquet.dualBlock) a
      (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((determinant (RealBlock.character c :: cs.map RealBlock.character) (-1) : ℂ) ^ (r + 1) *
        (determinant (fs.map RealBlock.character) (-1) : ℂ))
      (realUnequalIntegral (Nat.lt_succ_self r) D
        (realAdjacentGodementCoefficient D a (realColumnProduct F φ) U c) (B f))
      (realUnequalDualIntegral (Nat.lt_succ_self r) (-a) D
        (realAdjacentGodementCoefficient D a (realColumnProduct F φ) U c) (B f)) := by
  classical
  let ds := cs.map RealBlock.character
  let es := fs.map RealBlock.character
  let dds := RealUniformWhittakerDual.dualCharacterBlocks cs
  let dfs := RealUniformWhittakerDual.dualCharacterBlocks fs
  have hddsR : realRank dds = r + 1 := by
    simp only [dds, RealUniformWhittakerDual.dualCharacterBlocks, Langlands.Archimedean.realRank_map_character,
      List.length_map, List.length_reverse, hcs]
  have hdfsR : realRank dfs = r + 1 := by
    simp only [dfs, RealUniformWhittakerDual.dualCharacterBlocks, Langlands.Archimedean.realRank_map_character,
      List.length_map, List.length_reverse, hfs]
  let V := B f
  have hV : V ∈ realUniformWhittakerModel r es a :=
    Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)
  have hUd : dualH U ∈ realUniformWhittakerModel r dds a := by
    simpa only [neg_neg] using
      RealUniformWhittakerDual.realUniformWhittakerCharacterDual r cs hcs (-a) U hU
  have hdual (V' : H → ℂ) (hV' : V' ∈ realUniformWhittakerModel r es a) :
      dualH V' ∈ realUniformWhittakerModel r dfs (-a) :=
    RealUniformWhittakerDual.realUniformWhittakerCharacterDual r fs hfs a V' hV'
  -- compact projection of the standard vector
  choose p hp hpB using hProj
  obtain ⟨m, Wj, κ', hWj, hexp⟩ := realLocalCompactProjectionReduction (r := r) iK hiK hmem hsurj
    es a ν inferInstance κ hκ hκfin f B hB p (fun g x => hp g x) (fun x g => hpB g x)
  let C (j : Fin m) (z : H) : ℂ := ∫ k, κ' j k * (f : H → ℂ) (iK k * z) ∂ν
  -- the square factors
  have hSq (j : Fin m) := realAdjacentSquareGrowth (r := r) D iK hiK hmem ν (κ' j) (hWj j).2 a c
    F fs hfs f
  choose σsq hσsq using fun j => (hSq j).1
  obtain ⟨βsq, hβsq⟩ := (Set.finite_range σsq).bddAbove
  -- equal-rank convergence of the summands
  have hU' := realUniformWhittakerRegularity r ds (-a) U hU
  have hUd' := realUniformWhittakerRegularity r dds a (dualH U) hUd
  have hconv (j : Fin m) := realEqualPairConvergence r D (-a) a U (Wj j)
    (realRowSchwartzFourier (r + 1) a φ) hU'.1 hU'.2
    (by simpa only [neg_neg] using (realUniformWhittakerRegularity r es a (Wj j) (hWj j).1).1)
    (realUniformWhittakerRegularity r es a (Wj j) (hWj j).1).2
  have hconvd (j : Fin m) := realEqualPairConvergence r D a a (dualH U) (dualH (Wj j)) φ
    hUd'.1 hUd'.2 (realUniformWhittakerRegularity r dfs (-a) _ (hdual _ (hWj j).1)).1
    (realUniformWhittakerRegularity r dfs (-a) _ (hdual _ (hWj j).1)).2
  choose σe hσe using hconv
  choose σed hσed using hconvd
  obtain ⟨βe, hβe⟩ := (Set.finite_range σe).bddAbove
  obtain ⟨βed, hβed⟩ := (Set.finite_range σed).bddAbove
  -- the two expansions
  have hUr := splitModel_regular hU
  have hVr := splitModel_regular hV
  have hUdr := splitModel_regular hUd
  have hVdr := splitModel_regular (hdual V hV)
  obtain ⟨σp, hσp⟩ := realAdjacentUnfoldedIntegral_expansion (r := r) D ν iK hiK
    (fun k => Langlands.Archimedean.MaximalParabolicIntegration.abs_det_unitary ⟨iK k, hmem k⟩)
    κ hκ c F hFfin hrep (realRowSchwartzFourier (r + 1) a φ) (SchwartzMap.continuous _)
    (hasRapidDecay_schwartz _) U V hUr.2.1.continuous hVr.2.1.continuous
    (splitPair_invariant hUr hVr) (splitModel_gauge hU) (splitModel_growth hV) m Wj C
    (fun x z => (hexp x z).1)
    ⟨βe, fun s hs j => (hσe j).1 s (((hβe (Set.mem_range_self j))).trans_lt hs)⟩
    ⟨βsq, fun s hs j => (hσsq j s ((hβsq (Set.mem_range_self j)).trans_lt hs)).1⟩
  obtain ⟨σd, hσd⟩ := realAdjacentUnfoldedIntegral_expansion (r := r) D ν iK hiK
    (fun k => Langlands.Archimedean.MaximalParabolicIntegration.abs_det_unitary ⟨iK k, hmem k⟩)
    κ hκ c.inverse (realRectangularSchwartzFourier a F) hFdfin hrepd φ (SchwartzMap.continuous _)
    (hasRapidDecay_schwartz _) (dualH U) (dualH V) hUdr.2.1.continuous hVdr.2.1.continuous
    (splitPair_invariant (a := -a) (by simpa only [neg_neg] using hUdr) hVdr)
    (splitModel_gauge hUd) (splitModel_growth (hdual V hV)) m (fun j => dualH (Wj j))
    (fun j z => C j (ι z)) (fun x z => (hexp x z).2)
    ⟨βed, fun s hs j => (hσed j).1 s (((hβed (Set.mem_range_self j))).trans_lt hs)⟩
    ⟨βsq, fun s hs j => (hσsq j s ((hβsq (Set.mem_range_self j)).trans_lt hs)).2⟩
  obtain ⟨σh, hσh⟩ := realAdjacentGodementHalfPlane (r := r) D a c F φ ds dds es U V hU hUd hV
  -- the central sign of the dual summands
  let k : ℂ := (determinant dds (-1) : ℂ) * (determinant dfs (-1) : ℂ)
  have hkdet : k = (determinant ds (-1) : ℂ) * (determinant es (-1) : ℂ) := by
    simp only [k, dds, dfs, determinant_dualCharacterBlocks]
    rfl
  have hk : k ^ 2 = 1 := by
    rw [hkdet, mul_pow, determinant_characterList_sq, determinant_characterList_sq, one_mul]
  have hrefl (j : Fin m) (s : ℂ) : realEqualIntegral D (dualH U) (dualH (Wj j)) φ s =
      k * realEqualDualIntegral a D U (Wj j) (realRowSchwartzFourier (r + 1) a φ) s := by
    have hWdr := splitModel_regular (hdual _ (hWj j).1)
    refine realEqualIntegral_dual_reflect D U (Wj j) (fun u g => ?_) k hk (fun g => ?_) a φ s
    · have h := splitPair_invariant (a := a) hWdr hUdr u.val u.2 g 1
      simp only [mul_one] at h
      rw [mul_comm (dualH U (u.val * g)), h, mul_comm]
    · rw [splitModel_minusOne hddsR hUd, splitModel_minusOne hdfsR (hdual _ (hWj j).1)]
      ring
  -- assemble the normalized products
  let b := realAdjacentWeylSign r c
  let A (j : Fin m) := realEqualIntegral D U (Wj j) (realRowSchwartzFourier (r + 1) a φ)
  let Ad (j : Fin m) := realEqualDualIntegral a D U (Wj j) (realRowSchwartzFourier (r + 1) a φ)
  let Z (j : Fin m) (s : ℂ) := ∫ z, realAdjacentMatrixWeight c.character.toMonoidHom F s z * C j z
    ∂D.groupHaar
  let Zd (j : Fin m) (s : ℂ) := ∫ z, realAdjacentMatrixWeight c.inverse.character.toMonoidHom
    (realRectangularSchwartzFourier a F) s z * C j (ι z) ∂D.groupHaar
  let κd : ℂ := (c.character ((-1 : ℝˣ) ^ (r + 1)) : ℂ) * b * k
  have hsign : κd * (determinant ds (-1) : ℂ) ^ r =
      ((determinant (RealBlock.character c :: ds) (-1) : ℂ) ^ (r + 1) *
        (determinant es (-1) : ℂ)) * b := by
    have hcons : determinant (RealBlock.character c :: ds) (-1) =
        c.character (-1) * determinant ds (-1) := rfl
    simp only [κd, hkdet, hcons, Units.val_mul, map_pow, Units.val_pow_eq_pow_val]
    ring
  have hP := realAdjacentNormalizedProducts m (RealBlock.character c) ds es a
    (NNReal.sqrt ‖(a : ℝ)‖₊) (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
    ((determinant ds (-1) : ℂ) ^ r) b κd _ A Ad Z Zd hsign
    (fun j => hLower (Wj j) (hWj j).1) (fun j => (hSq j).2)
  refine hP.congr (τ := max σh (max σp σd)) ?_ ?_
  · intro s hs
    have hs₁ : σh < s.re := (le_max_left _ _).trans_lt hs
    have hs₂ : σp < s.re := ((le_max_left _ _).trans (le_max_right _ _)).trans_lt hs
    rw [(hσh s hs₁).1, hσp s hs₂]
  · intro s hs
    have hs₁ : σh < s.re := (le_max_left _ _).trans_lt hs
    have hs₃ : σd < s.re := ((le_max_right _ _).trans (le_max_right _ _)).trans_lt hs
    rw [(hσh s hs₁).2, hσd s hs₃]
    simp only [hrefl, κd, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Ad, Zd]
    ring

end Langlands.Global.RankinSelbergGlobal.RealJacquet
