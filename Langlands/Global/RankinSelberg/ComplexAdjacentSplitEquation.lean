import Langlands.Global.RankinSelberg.ComplexAdjacentCompactWeight
import Langlands.Global.RankinSelberg.ComplexAdjacentCompactAverage
import Langlands.Global.RankinSelberg.ComplexAdjacentCompactTransport
import Langlands.Global.RankinSelberg.ComplexAdjacentSplitIntegrals
import Langlands.Global.RankinSelberg.ComplexAdjacentProductExpansion
import Langlands.Global.RankinSelberg.ComplexAdjacentTwistedZeta
import Langlands.Global.RankinSelberg.ComplexAdjacentNormalizedProducts
import Langlands.Global.RankinSelberg.ComplexLocalCompactProjection

/-! # The adjacent-rank functional equation on a continued split Godement value -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal
open scoped Langlands.Archimedean.ComplexDuality

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure complexUnequalIntegral
  complexUnequalDualIntegral complexFourierTransform complexEqualIntegral complexEqualDualIntegral
  complexEqualIntegrand)
open Langlands.Archimedean Langlands.Archimedean.ComplexReverseTwist
open Langlands.Archimedean.ComplexDeterminantTwist (detCharacter)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.GeneralLinear Langlands.Automorphic Langlands.LocalFactor.Archimedean
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue)
open ComplexJacquet (complexAdjacentCompactWeight complexLocalCompactProjectionReduction
  HasComplexPairNormalizedGrowth)
open ComplexSquareFourier (matrixTransform)
open ComplexSquareZeta (compactCoefficient complexAdjacentTwistedZetaGrowth zetaKernel)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Kc" => unitaryCompact ℂ (r + 1)
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "Kspace" => MeasurableSpace.comap (Subtype.val : Kc → H) (borel H)
local notation "dualH" => ArchimedeanLocal.dualFunction (r + 1)
local notation "ι" => inverseTranspose (r + 1) ℂ
local notation "gap" => Nat.lt_succ_self r
local notation "columnProd" => ComplexGodementColumnProduct.columnProduct

private theorem zetaKernel_weight (d : ComplexCharacterData) (Φ : Mat → ℂ)
    (C : H → ℂ) (s : ℂ) (g : H) :
    zetaKernel Φ (fun z => detCharacter d.character z * C z) s g =
      Φ g.val * characterWeight d ((r : ℂ) / 2 + s) (determinant g) * C g := by
  unfold zetaKernel
  rw [show s + (((r + 1 : ℕ) : ℂ) - 1) / 2 = (r : ℂ) / 2 + s by push_cast; ring]
  change _ = Φ g.val * ((d.character (determinant g) : ℂ) *
    ComplexGodement.normPower ((r : ℂ) / 2 + s) (determinant g)) * C g
  unfold detCharacter
  ring

private theorem twistedBlocks (d : ComplexCharacterData) (es : Fin (r + 1) → ComplexCharacterData) :
    (List.ofFn fun i => (es i).mul d) = complexPairBlocks [d] (List.ofFn es) := by
  apply List.ext_getElem
  · simp [complexPairBlocks]
  · intro i hi hj
    simp only [complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
      List.getElem_map, List.getElem_ofFn]
    exact Langlands.Archimedean.ComplexPermutation.eq_of_params
      (add_comm _ _) (add_comm _ _)

private theorem inversePairBlocks (d : ComplexCharacterData) (es : List ComplexCharacterData) :
    (complexPairBlocks [d] es).map ComplexCharacterData.inv =
      complexPairBlocks [d.inv] (es.map ComplexCharacterData.inv) := by
  simp only [complexPairBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_map]
  congr 1
  funext e
  apply Langlands.Archimedean.ComplexPermutation.eq_of_params
  · simp only [Function.comp_apply, ComplexCharacterData.inv_weight, ComplexCharacterData.mul]
    exact neg_add _ _
  · simp only [Function.comp_apply, ComplexCharacterData.inv_exponent, ComplexCharacterData.mul]
    exact neg_add _ _

private theorem twistedSquare_normalization (μ : Measure H) [μ.IsHaarMeasure]
    (κ : @Measure Kc Kspace) (hk : letI := Kspace; IsFiniteMeasure κ)
    (hHaar : letI := Kspace; κ.IsHaarMeasure) (a : ℂˣ) (d : ComplexCharacterData)
    (es : Fin (r + 1) → ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (f : H → ℂ)
    (hf : f ∈ complexStandardModule (r + 1) (List.ofFn es)) (w : Kc → ℂ) (hw : Continuous w) :
    let C := compactCoefficient κ id w f
    let P := fun (s : ℂ) (g : H) => Φ g.val *
      characterWeight d ((r : ℂ) / 2 + s) (determinant g) * C g
    let Pd := fun (s : ℂ) (g : H) => splitSquareTransform a Φ g.val *
      characterWeight d.inv ((r : ℂ) / 2 + s) (determinant g) * C (ι g)
    (∃ σ : ℝ, ∀ s : ℂ, σ < s.re → Integrable (P s) μ ∧ Integrable (Pd s) μ) ∧
    HasComplexPairNormalizedGrowth [d] (List.ofFn es) a 1
      (fun s => ∫ g, P s g ∂μ) (fun s => ∫ g, Pd s g ∂μ) := by
  dsimp only
  obtain ⟨σ, N, Nd, hN, hNd, hNg, hNdg, hσ, hEq⟩ :=
    @complexAdjacentTwistedZetaGrowth r μ _ κ hk hHaar a d es Φ f w hf hw
  let C := compactCoefficient κ id w f
  have hP (s : ℂ) := funext (zetaKernel_weight d Φ C s)
  have hPd (s : ℂ) := funext
    (zetaKernel_weight d.inv (splitSquareTransform a Φ) (fun z => C (ι z)) s)
  simp only [C, ← splitSquareTransform_eq_matrixTransform_neg, hP, hPd,
    twistedBlocks, inversePairBlocks] at hσ
  refine ⟨⟨σ, fun s hs => ⟨(hσ s hs).1, (hσ s hs).2.1⟩⟩,
    N, Nd, hN, hNd, hNg, hNdg, ⟨σ, fun s hs => ?_⟩, ?_⟩
  · simpa only [complexPairLFactor, List.map_cons, List.map_nil] using (hσ s hs).2.2
  · simpa only [one_mul, complexPairEpsilon, twistedBlocks] using hEq

/-- The split-value adjacent equation from the smaller equal-rank equations and
the compact convolution identity on the inducing vector and its Whittaker image. -/
def ComplexAdjacentSplitEquationStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : Kc => fun X => Φ (k.val⁻¹.val * X))) →
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a)) (f : complexStandardKFinite (r + 1) es)
    (B : complexStandardKFinite (r + 1) es →ₗ[ℂ] (H → ℂ)),
    IsComplexWhittakerIntertwiner r es a B →
    (∀ (w : Kc → ℂ), Continuous w →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : Kc => fun k => w (h⁻¹ * k))) →
      ∀ g : H, ∃ p : complexStandardKFinite (r + 1) es,
        (∀ x : H, p.val x = ∫ k : Kc, w k * f.val (x * k.val * g) ∂κ) ∧
        ∀ x : H, B p x = ∫ k : Kc, w k * B f (x * k.val * g) ∂κ) →
    (∀ V ∈ complexWhittakerModel r es a,
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexEqualIntegrand U.val V (splitRowTransform a φ) s) D.measure ∧
        Integrable (complexEqualIntegrand (dualH U.val) (dualH V) φ s) D.measure) ∧
      HasComplexPairNormalization ds es (-a) (complexCentralSign es ^ r)
        (complexEqualIntegral D U.val V (splitRowTransform a φ))
        (complexEqualDualIntegral (-a) D U.val V (splitRowTransform a φ))) →
    let W : G → ℂ := fun g => continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProd Φ φ)) U.val g 0
    HasComplexPairNormalization (d :: ds) es (-a) (complexCentralSign es ^ (r + 1))
      (complexUnequalIntegral gap D W (B f)) (complexUnequalDualIntegral gap (-a) D W (B f))

/-- The finite factorization of the split ordinary and dual adjacent integrals into
lower equal-rank integrals and strip-growing square pairs. -/
def ComplexAdjacentSplitDecompositionStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : Kc => fun X => Φ (k.val⁻¹.val * X))) →
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a)) (f : complexStandardKFinite (r + 1) es)
    (B : complexStandardKFinite (r + 1) es →ₗ[ℂ] (H → ℂ)),
    IsComplexWhittakerIntertwiner r es a B →
    (∀ (w : Kc → ℂ), Continuous w →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : Kc => fun k => w (h⁻¹ * k))) →
      ∀ g : H, ∃ p : complexStandardKFinite (r + 1) es,
        (∀ x : H, p.val x = ∫ k : Kc, w k * f.val (x * k.val * g) ∂κ) ∧
        ∀ x : H, B p x = ∫ k : Kc, w k * B f (x * k.val * g) ∂κ) →
    (∀ V ∈ complexWhittakerModel r es a,
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexEqualIntegrand U.val V (splitRowTransform a φ) s) D.measure ∧
        Integrable (complexEqualIntegrand (dualH U.val) (dualH V) φ s) D.measure)) →
    let W : G → ℂ := fun g => continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProd Φ φ)) U.val g 0
    ∃ (m : ℕ) (Q : Fin m → H → ℂ) (Z Zd : Fin m → ℂ → ℂ),
      (∀ j, Q j ∈ complexWhittakerModel r es a) ∧
      (∀ j, HasComplexPairNormalizedGrowth [d] es a 1 (Z j) (Zd j)) ∧
      ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        complexUnequalIntegral gap D W (B f) s =
          (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
            ∑ j, complexEqualIntegral D U.val (Q j) (splitRowTransform a φ) s * Z j s ∧
        complexUnequalDualIntegral gap (-a) D W (B f) s =
          ∑ j, complexEqualDualIntegral (-a) D U.val (Q j) (splitRowTransform a φ) s * Zd j s

set_option maxHeartbeats 1500000 in
theorem complexAdjacentSplitDecomposition : ComplexAdjacentSplitDecompositionStatement (r := r) := by
  classical
  intro D _ κ _ hκ a d Φ φ hΦ ds es hds hes U f B hB hProjection hEq W
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (r + 1)
  let : LocallyCompactSpace H := e.locallyCompactSpace
  let : SecondCountableTopology H := e.secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let V : complexWhittakerModel r es a :=
    ⟨B f, Submodule.mem_iSup_of_mem B (Submodule.mem_iSup_of_mem hB ⟨f, rfl⟩)⟩
  let V₀ : complexWhittakerModel r es (-(-a)) := ⟨V.val, by simpa only [neg_neg] using V.2⟩
  let Ud : complexWhittakerModel r (dualData ds) a :=
    ⟨dualH U.val, by simpa only [neg_neg] using dualFunction_mem hds U.2⟩
  let Vd : complexWhittakerModel r (dualData es) (-a) :=
    ⟨dualH V.val, dualFunction_mem hes V.2⟩
  obtain ⟨σs, hspl⟩ := complexAdjacentSplitIntegrals D a d 0 Φ φ ds es hds hes U V
  obtain ⟨w, hw, hwfin, hp, hpd⟩ := complexAdjacentCompactWeight κ d.character.toMonoidHom
    d.character.continuous (-a) Φ hΦ
  have hmean (X : Mat) : (∫ k : Kc, w k * (d.character ((determinant (id k : Kc).val)⁻¹) : ℂ) *
      Φ ((id k : Kc).val⁻¹.val * X) ∂κ) = Φ X := by
    rw [← hp X]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    change w k * (d.character ((determinant k.val)⁻¹) : ℂ) * Φ (k.val⁻¹.val * X) =
      w k * ((d.character ((determinant k.val)⁻¹) : ℂ) * Φ (k.val⁻¹.val * X))
    exact mul_assoc _ _ _
  have hmeanD (X : Mat) : (∫ k : Kc, w k *
      (d.inv.character ((determinant (conjK (r + 1) k).val)⁻¹) : ℂ) *
      matrixTransform (-a) Φ ((conjK (r + 1) k).val⁻¹.val * X) ∂κ) =
      matrixTransform (-a) Φ X := by
    rw [← hpd X]
    refine integral_congr_ae (ae_of_all _ fun k => ?_)
    let g := (conjK (r + 1) k).val
    have hc : (d.inv.character ((determinant g)⁻¹) : ℂ) = (d.character (determinant g) : ℂ) := by
      rw [ComplexCharacterData.inv_character_apply, map_inv, Units.val_inv_eq_inv_val, inv_inv]
    change w k * (d.inv.character ((determinant g)⁻¹) : ℂ) * matrixTransform (-a) Φ (g⁻¹.val * X) =
      w k * ((d.character (determinant g) : ℂ) * matrixTransform (-a) Φ (g⁻¹.val * X))
    rw [hc, mul_assoc]
  obtain ⟨σa, hA⟩ := complexAdjacentCompactAverage D D.groupHaar κ id continuous_id w hw d
    ((r : ℂ) / 2) Φ (splitRowTransform a φ) hΦ hmean (-a) ds es U V₀
  obtain ⟨σd, hAd⟩ := complexAdjacentCompactAverage D D.groupHaar κ (conjK (r + 1))
    (continuous_conjK (n := r + 1)) w hw d.inv ((r : ℂ) / 2) (matrixTransform (-a) Φ) φ
    (complexAdjacentCompactTransport (-a) Φ hΦ) hmeanD a (dualData ds) (dualData es) Ud Vd
  choose projection hproj using hProjection w hw hwfin
  obtain ⟨m, Q, w', hQ, hExp⟩ := complexLocalCompactProjectionReduction (r := r) es a κ hκ w hw hwfin
    f B hB projection (fun g (x : Kc) => (hproj g).1 x.val) (fun x g => (hproj g).2 x)
  obtain ⟨κ', hk', hH', hcoeff⟩ := exists_inducedUnitaryMeasure κ
  let C (j : Fin m) := compactCoefficient κ' id (w' j) f.val
  have hc (j : Fin m) (z : H) : (∫ k : Kc, w' j k * f.val (k.val * z) ∂κ) = C j z :=
    hcoeff (fun k => w' j k * f.val (k.val * z))
  have hV₁ (x z : H) : (∫ k : Kc, w k * V.val (x * (id k : Kc).val * z) ∂κ) =
      ∑ j, Q j x * C j z := by
    simpa only [V, id_eq, hc] using (hExp x z).1
  have hV₂ (x z : H) : (∫ k : Kc, w k * Vd.val (x * (conjK (r + 1) k).val * z) ∂κ) =
      ∑ j, dualH (Q j) x * C j (ι z) := by
    have hi (g : H) : ι g = conjAut g := Units.ext rfl
    simpa only [Vd, V, conjK_val, hc, hi] using (hExp x z).2
  let Ad (j : Fin m) := complexEqualIntegral D Ud.val (dualH (Q j)) φ
  let Z (j : Fin m) (s : ℂ) := ∫ z : H, Φ z.val *
    characterWeight d ((r : ℂ) / 2 + s) (determinant z) * C j z ∂D.groupHaar
  let Zd (j : Fin m) (s : ℂ) := ∫ z : H, splitSquareTransform a Φ z.val *
    characterWeight d.inv ((r : ℂ) / 2 + s) (determinant z) * C j (ι z) ∂D.groupHaar
  let es' (i : Fin (r + 1)) := es.get (i.cast hes.symm)
  have he : List.ofFn es' = es :=
    (List.ofFn_congr hes es.get).symm.trans (List.ofFn_get es)
  have hf' : (f.val : H → ℂ) ∈ complexStandardModule (r + 1) (List.ofFn es') := he.symm ▸ f.2.1
  have hZ (j : Fin m) := twistedSquare_normalization D.groupHaar κ' hk' hH' a d es' Φ
    f.val hf' (w' j) (hQ j).2
  choose σz hZint using fun j => (hZ j).1
  have hnZ (j : Fin m) : HasComplexPairNormalizedGrowth [d] es a 1 (Z j) (Zd j) := by
    simpa only [he, Z, Zd, C] using (hZ j).2
  have hrow : complexFourierTransform (-a) (splitRowTransform a φ) = (φ : Vec → ℂ) :=
    funext (complexFourierTransform_splitRowTransform a φ)
  have heqD (j : Fin m) : complexEqualDualIntegral (-a) D U.val (Q j) (splitRowTransform a φ) = Ad j := by
    funext s
    unfold complexEqualDualIntegral
    rw [hrow]
    rfl
  choose σe hEint using fun j => hEq (Q j) (hQ j).1
  obtain ⟨β, hβ⟩ := (Set.finite_range fun j : Fin m => max (σz j) (σe j)).bddAbove
  let σ := max (max σs σa) (max σd β)
  refine ⟨m, Q, Z, Zd, fun j => (hQ j).1, hnZ, σ, fun s hs => ?_⟩
  simp only [σ, max_lt_iff] at hs
  obtain ⟨⟨hs', ha'⟩, hd', hb'⟩ := hs
  have hz (j : Fin m) := hZint j s (((le_max_left (σz j) (σe j)).trans
    (hβ (Set.mem_range_self j))).trans_lt hb')
  have heq (j : Fin m) := hEint j s (((le_max_right (σz j) (σe j)).trans
    (hβ (Set.mem_range_self j))).trans_lt hb')
  have hpSum := complexAdjacentProductExpansion D D.groupHaar d ((r : ℂ) / 2) s Φ
    (splitRowTransform a φ) U.val m Q C _ hV₁ (fun j => (hz j).1) (fun j => (heq j).1)
  have hdSum := complexAdjacentProductExpansion D D.groupHaar d.inv ((r : ℂ) / 2) s
    (matrixTransform (-a) Φ) φ Ud.val m (fun j => dualH (Q j)) (fun j z => C j (ι z)) _
    hV₂ (fun j => by simpa only [splitSquareTransform_eq_matrixTransform_neg] using (hz j).2)
    (fun j => (heq j).2)
  have hPr := (hspl s hs').2.2.1
  have hDu := (hspl s hs').2.2.2
  simp only [zero_add, neg_zero, splitSquareTransform_eq_matrixTransform_neg] at hPr hDu
  rw [(hA s ha').2, hpSum] at hPr
  rw [(hAd s hd').2, hdSum] at hDu
  exact ⟨hPr, by simpa only [heqD, Ad, Zd, splitSquareTransform_eq_matrixTransform_neg] using hDu⟩

theorem complexAdjacentSplitEquation : ComplexAdjacentSplitEquationStatement (r := r) := by
  intro D _ κ _ _ a d Φ φ hΦ ds es hds hes U f B hB hProjection hEq W
  obtain ⟨m, Q, Z, Zd, hQ, hZ, σ, hσ⟩ := complexAdjacentSplitDecomposition D κ a d Φ φ hΦ
    ds es hds hes U f B hB hProjection (fun V hV => (hEq V hV).1)
  obtain ⟨N, Nd, hN, hNd, ⟨τ, hτ⟩, hFE⟩ := complexAdjacentNormalizedProducts r m d ds es hes a
    _ _ Z Zd (fun j => (hEq (Q j) (hQ j)).2) (fun j => normalization_of_growth (hZ j))
  refine ⟨N, Nd, hN, hNd, ⟨max σ τ, ?_⟩, hFE⟩
  intro s hs
  obtain ⟨hOrd, hDual⟩ := hσ s ((le_max_left _ _).trans_lt hs)
  rw [hOrd, hDual]
  exact hτ s ((le_max_right _ _).trans_lt hs)

/-- The adjacent split-value equation with strip growth in both lower and upper pairs. -/
def ComplexAdjacentSplitGrowthStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (κ : Measure Kc) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (a : ℂˣ) (d : ComplexCharacterData) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ)),
    FiniteDimensional ℂ
      (Submodule.span ℂ (Set.range fun k : Kc => fun X => Φ (k.val⁻¹.val * X))) →
  ∀ (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a)) (f : complexStandardKFinite (r + 1) es)
    (B : complexStandardKFinite (r + 1) es →ₗ[ℂ] (H → ℂ)),
    IsComplexWhittakerIntertwiner r es a B →
    (∀ (w : Kc → ℂ), Continuous w →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun h : Kc => fun k => w (h⁻¹ * k))) →
      ∀ g : H, ∃ p : complexStandardKFinite (r + 1) es,
        (∀ x : H, p.val x = ∫ k : Kc, w k * f.val (x * k.val * g) ∂κ) ∧
        ∀ x : H, B p x = ∫ k : Kc, w k * B f (x * k.val * g) ∂κ) →
    (∀ V ∈ complexWhittakerModel r es a,
      (∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
        Integrable (complexEqualIntegrand U.val V (splitRowTransform a φ) s) D.measure ∧
        Integrable (complexEqualIntegrand (dualH U.val) (dualH V) φ s) D.measure) ∧
      HasComplexPairNormalizedGrowth ds es (-a) (complexCentralSign es ^ r)
        (complexEqualIntegral D U.val V (splitRowTransform a φ))
        (complexEqualDualIntegral (-a) D U.val V (splitRowTransform a φ))) →
    let W : G → ℂ := fun g => continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProd Φ φ)) U.val g 0
    HasComplexPairNormalizedGrowth (d :: ds) es (-a) (complexCentralSign es ^ (r + 1))
      (complexUnequalIntegral gap D W (B f)) (complexUnequalDualIntegral gap (-a) D W (B f))

theorem complexAdjacentSplitGrowth : ComplexAdjacentSplitGrowthStatement (r := r) := by
  intro D _ κ _ _ a d Φ φ hΦ ds es hds hes U f B hB hProjection hEq W
  obtain ⟨m, Q, Z, Zd, hQ, hZ, σ, hσ⟩ := complexAdjacentSplitDecomposition D κ a d Φ φ hΦ
    ds es hds hes U f B hB hProjection (fun V hV => (hEq V hV).1)
  obtain ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨τ, hτ⟩, hFE⟩ := complexAdjacentNormalizedProductsGrowth r m d ds es hes a
    _ _ Z Zd (fun j => (hEq (Q j) (hQ j)).2) hZ
  refine ⟨N, Nd, hN, hNd, hNg, hNdg, ⟨max σ τ, ?_⟩, hFE⟩
  intro s hs
  obtain ⟨hOrd, hDual⟩ := hσ s ((le_max_left _ _).trans_lt hs)
  rw [hOrd, hDual]
  exact hτ s ((le_max_right _ _).trans_lt hs)

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
