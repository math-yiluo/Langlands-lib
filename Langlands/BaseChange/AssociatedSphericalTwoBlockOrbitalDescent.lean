import Langlands.BaseChange.AssociatedTwoBlockHaar
import Langlands.BaseChange.ExactNormLeviModulus
import Langlands.BaseChange.OrbitalMeasureExistence
import Langlands.BaseChange.RegularCyclicTwistedOrbit
import Langlands.BaseChange.TwistedTwoBlockRadicalJacobian

/-! Matched ordinary and twisted spherical orbital descent at exact block norms. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure _root_.Topology Langlands.GeneralLinear
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg
open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.HarmonicAnalysis Langlands.Unramified
open scoped NNReal

universe u v w

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

local instance associatedDescentFieldMeasurable {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) :
    MeasurableSpace K.Carrier := borel _
local instance associatedDescentFieldBorel {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) :
    BorelSpace K.Carrier := ⟨rfl⟩
local instance associatedDescentFieldT2 {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) :
    T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance associatedDescentFieldSecondCountable {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) :
    SecondCountableTopology K.Carrier := K.canonicalTopologicalData.secondCountableTopology
local instance associatedDescentGLLocallyCompact {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) (n : ℕ) :
    LocallyCompactSpace (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace K.Carrier n
local instance associatedDescentGLSecondCountable {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) (n : ℕ) :
    SecondCountableTopology (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_secondCountableTopology K.Carrier n
local instance associatedDescentGLSigmaCompact {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) (n : ℕ) :
    SigmaCompactSpace (GeneralLinear n K.Carrier) :=
  LocalFieldTopology.generalLinear_sigmaCompactSpace K.Carrier n
local instance associatedDescentGLHaarRightInvariant {p : ℕ} [Fact p.Prime] (K : PadicField.{w} p) (n : ℕ) :
    (generalLinearHaar K.Carrier n).IsMulRightInvariant := generalLinearHaarRightInvariant K.Carrier n

section Pointwise

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  [IsModuleTopology F.Carrier E.Carrier]
  {σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier} {l r : ℕ} {m : Fin 2 → ℕ}
  (h : ∑ i, (m i + 1) = r + 1)

local notation "B" => succBlockShape m h
local notation "M" => BlockShape.Levi B E.Carrier
local notation "G" => GeneralLinear (r + 1) E.Carrier
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) E.Carrier

omit [IsScalarTower (Padic p) F.Carrier E.Carrier] in
private theorem compactContinuous_twistedSphericalOrbitFunction {t : ℕ}
    (hσ : IsCyclicAlgebra σ l) (d : GeneralLinear (t + 1) E.Carrier)
    (hd : IsRegularSemisimple (cyclicNorm σ l d)) (f : SphericalHeckeAlgebra E t) :
    Continuous (twistedOrbitFunction (entrywiseAut σ (t + 1)) d ⇑f) ∧
      HasCompactSupport (twistedOrbitFunction (entrywiseAut σ (t + 1)) d ⇑f) := by
  let ψ : SchwartzBruhat (GeneralLinear (t + 1) E.Carrier) := f.val
  exact continuous_hasCompactSupport_cyclicTwistedOrbitFunction hσ d ψ hd ψ.continuous ψ.hasCompactSupport

set_option maxHeartbeats 3500000 in
/-- The twisted orbital formula has exactly the ordinary scalar when its
centralizer scale is the common scale at an exact block norm. -/
theorem sigmaOrbitalIntegral_twoBlock_of_expansion
    (hσ : IsCyclicAlgebra σ l) (L : (B).Levi F.Carrier) (D : M)
    (hΓ : IsRegularSemisimple ((B).leviEmbedding F.Carrier L))
    (hReg : ∀ i : Fin 2, IsRegularSemisimple (L i))
    (hCop : Pairwise fun i j => IsCoprime (L i).val.charpoly (L j).val.charpoly)
    (hn : ∀ i : Fin 2, cyclicNorm σ l (D i) = baseChange F.Carrier E.Carrier (m i + 1) (L i))
    (μ : ∀ i : Fin 2, Measure (sigmaCentralizer σ (m i + 1) (D i)))
    [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsMulRightInvariant]
    (ν : ∀ i : Fin 2, Measure (LeftQuotient (sigmaCentralizer σ (m i + 1) (D i))))
    (hν : ∀ i, IsCompatible (sigmaCentralizer σ (m i + 1) (D i))
      (sphericalHaar E (m i)) (μ i) (ν i))
    (μδ : Measure (sigmaCentralizer σ (r + 1) ((B).leviEmbedding E.Carrier D)))
    [μδ.IsHaarMeasure] [μδ.IsMulRightInvariant]
    (νδ : Measure (LeftQuotient (sigmaCentralizer σ (r + 1) ((B).leviEmbedding E.Carrier D))))
    (hνδ : IsCompatible _ (sphericalHaar E r) μδ νδ)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hScale : μδ = c • Measure.map (sigmaLeviCentralizerEquiv B L D hσ hReg hn hΓ hCop)
      (finTwoSubgroupMeasure (fun i => sigmaCentralizer σ (m i + 1) (D i)) (μ 0) (μ 1)))
    (dx : Measure Rect) [dx.IsAddHaarMeasure]
    (hdx : dx {x | ∀ i j, x i j ∈ (ValuativeRel.valuation E.Carrier).integer} = 1)
    (f : SphericalHeckeAlgebra E r) {N : ℕ}
    (α : Fin N → SphericalHeckeAlgebra E (m 0)) (β : Fin N → SphericalHeckeAlgebra E (m 1))
    (hExpansion : ∀ V : M, (E.canonicalTopologicalData.leviHalfModulus B V : ℂ) *
      (∫ x, f (parabolicPoint h (V, x)) ∂dx) = ∑ j, α j (V 0) * β j (V 1)) :
    sigmaOrbitalIntegral σ (r + 1) ((B).leviEmbedding E.Carrier D) νδ ⇑f =
      ordinaryTwoBlockOrbitalFactor F h L c * ∑ j,
        sigmaOrbitalIntegral σ (m 0 + 1) (D 0) (ν 0) ⇑(α j) *
          sigmaOrbitalIntegral σ (m 1 + 1) (D 1) (ν 1) ⇑(β j) := by
  let θ := entrywiseAut σ (r + 1)
  let δ := (B).leviEmbedding E.Carrier D
  let H := sigmaCentralizer σ (r + 1) δ
  let C := fun i : Fin 2 => sigmaCentralizer σ (m i + 1) (D i)
  let A := Subgroup.pi Set.univ C
  let e : A ≃ₜ* H := sigmaLeviCentralizerEquiv B L D hσ hReg hn hΓ hCop
  have he (a : A) : (e a).val = (B).leviEmbedding E.Carrier a.val :=
    sigmaLeviCentralizerEquiv_apply_val B L D hσ hReg hn hΓ hCop a
  let νA := finTwoQuotientMeasure C (ν 0) (ν 1)
  let μA := finTwoSubgroupMeasure C (μ 0) (μ 1)
  have hH : IsClosed (H : Set G) := isClosed_twistedCentralizer θ
    (SigmaLiftCharacterIdentity.continuous_entrywiseAut σ) δ
  have hC (i : Fin 2) : IsClosed (C i : Set (GeneralLinear (m i + 1) E.Carrier)) :=
    isClosed_twistedCentralizer (entrywiseAut σ (m i + 1))
      (SigmaLiftCharacterIdentity.continuous_entrywiseAut σ) (D i)
  let : ∀ i : Fin 2, LocallyCompactSpace (C i) := fun i => (hC i).locallyCompactSpace
  let : ∀ i : Fin 2, SecondCountableTopology (C i) := fun _ => IsEmbedding.subtypeVal.secondCountableTopology
  let : ∀ i : Fin 2, LocallyCompactSpace (LeftQuotient (C i)) := fun i => leftQuotient_locallyCompactSpace (C i)
  let : ∀ i : Fin 2, SecondCountableTopology (LeftQuotient (C i)) := fun i =>
    (leftQuotient_isOpenQuotientMap (C i)).secondCountableTopology
  let : ∀ i : Fin 2, (ν i).Regular := fun i => (hν i).regular
  let : μA.IsMulRightInvariant := by dsimp only [μA, C]; infer_instance
  have hA : IsClosed (A : Set M) := isClosed_set_pi (fun i _ => hC i)
  have hνA : IsCompatible A (Measure.pi fun i => generalLinearHaar E.Carrier (m i)) μA νA := by
    apply finTwoQuotientMeasure_isCompatible C hC
    · rw [← sphericalHaar_eq_generalLinearHaar]
      exact hν 0
    · rw [← sphericalHaar_eq_generalLinearHaar]
      exact hν 1
  have hδ : IsRegularSemisimple (cyclicNorm σ l δ) := by
    change IsRegularSemisimple (cyclicNorm σ l ((B).leviEmbedding E.Carrier D))
    rw [cyclicNorm_leviEmbedding_eq_of_blockwise B L D hn]
    exact isRegularSemisimple_baseChange hΓ
  let φ := twistedOrbitFunction θ δ ⇑f
  obtain ⟨hφ, hφ₀⟩ := compactContinuous_twistedSphericalOrbitFunction F E hσ δ hδ f
  have hInv (q : LeftQuotient H) (k : sphericalOpenSubgroup E r) :
      φ (rightTranslate H k.val q) = φ q := by
    induction q using Quotient.inductionOn with
    | h U =>
      change f ((U * k.val)⁻¹ * δ * θ (U * k.val)) = f (U⁻¹ * δ * θ U)
      have hMul : (U * k.val)⁻¹ * δ * θ (U * k.val) =
          (k⁻¹).val * (U⁻¹ * δ * θ U) * θ k.val := by
        change (U * k.val)⁻¹ * δ * θ (U * k.val) = k.val⁻¹ * (U⁻¹ * δ * θ U) * θ k.val
        simp only [mul_inv_rev, map_mul, mul_assoc]
      rw [hMul]
      let k' : sphericalOpenSubgroup E r := ⟨θ k.val, entrywiseAut_mem_sphericalOpenSubgroup F E σ k.property⟩
      calc
        _ = f ((k⁻¹).val * (U⁻¹ * δ * θ U)) := Hecke.HeckeAlgebra.Corner.rightInvariant _ _ _ f k' _
        _ = _ := Hecke.HeckeAlgebra.Corner.leftInvariant _ _ _ f k⁻¹ _
  have hOrb := integral_twoBlock_leviRadicalQuotientPoint E h A H e he hA hH μA μδ c hc hScale
    νA νδ hνA hνδ dx hdx φ hφ hφ₀ hInv
  let qCoord := finTwoLeftQuotientHomeomorph C
  let a (j : Fin N) := twistedOrbitFunction (entrywiseAut σ (m 0 + 1)) (D 0) (α j)
  let b (j : Fin N) := twistedOrbitFunction (entrywiseAut σ (m 1 + 1)) (D 1) (β j)
  let jac := (F.canonicalTopologicalData.normalizedAbsHom (ordinaryRadicalMatrix h L).det)⁻¹
  let d : ℂ := jac.toReal
  let kF : ℂ := (F.canonicalTopologicalData.leviHalfModulus B L : ℂ)
  have hkF : kF ≠ 0 := Units.ne_zero _
  have hJac : Measure.map (twistedRadicalDifference σ h D) dx = jac • dx :=
    map_twistedRadicalDifference_of_exactNorm F E h hσ L D hn hCop dx
  have hInner (q : LeftQuotient A) :
      (∫ x, φ (leviRadicalQuotientPoint h A H e he (q, x)) ∂dx) =
        d * kF⁻¹ * ∑ j, a j (qCoord q).1 * b j (qCoord q).2 := by
    induction q using Quotient.inductionOn with
    | h U =>
      let V : M := U⁻¹ * D * leviAut σ B U
      let Ψ (y : Rect) := f (parabolicPoint h (V, y))
      let f₀ : SchwartzBruhat G := f.val
      have hΨ : Continuous Ψ := f₀.continuous.comp
        ((continuous_parabolicPoint h E.Carrier).comp (continuous_const.prodMk continuous_id))
      have hConj (x : Rect) :
          φ (leviRadicalQuotientPoint h A H e he (leftQuotientMap A U, x)) =
            Ψ (twistedRadicalDifference σ h V x) := by
        rw [leviRadicalQuotientPoint_mk]
        change f ((parabolicPoint h (U, x))⁻¹ * δ * θ (parabolicPoint h (U, x))) = _
        exact congrArg (fun g : G => f g) (twistedConj_parabolicPoint σ h D U x)
      have hV : Measure.map (twistedRadicalDifference σ h V) dx = jac • dx :=
        map_twistedRadicalDifference_twistedConj F E σ h D U dx jac hJac
      have hHalf : (E.canonicalTopologicalData.leviHalfModulus B V : ℂ) = kF := by
        exact congrArg Units.val ((leviHalfModulus_twistedConj F E σ B D U).trans
          (leviHalfModulus_eq_of_exactNorm F E σ B L D hσ hn))
      have hs := hExpansion V
      rw [hHalf] at hs
      change (∫ x, φ (leviRadicalQuotientPoint h A H e he (leftQuotientMap A U, x)) ∂dx) =
        d * kF⁻¹ * ∑ j, α j (V 0) * β j (V 1)
      simp_rw [hConj]
      calc
        _ = ∫ x, Ψ x ∂Measure.map (twistedRadicalDifference σ h V) dx :=
          (integral_map (continuous_twistedRadicalDifference σ h V).measurable.aemeasurable
            hΨ.aestronglyMeasurable).symm
        _ = d * (∫ x, Ψ x ∂dx) := by
          rw [hV, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
        _ = _ := by rw [← hs, mul_assoc d, ← mul_assoc kF⁻¹, inv_mul_cancel₀ hkF, one_mul]
  have hRegD (i : Fin 2) : IsRegularSemisimple (cyclicNorm σ l (D i)) :=
    (hn i).symm ▸ isRegularSemisimple_baseChange (hReg i)
  have hIntA (j : Fin N) : Integrable (a j) (ν 0) := by
    obtain ⟨ha, ha₀⟩ := compactContinuous_twistedSphericalOrbitFunction F E hσ (D 0) (hRegD 0) (α j)
    exact ha.integrable_of_hasCompactSupport ha₀
  have hIntB (j : Fin N) : Integrable (b j) (ν 1) := by
    obtain ⟨hb, hb₀⟩ := compactContinuous_twistedSphericalOrbitFunction F E hσ (D 1) (hRegD 1) (β j)
    exact hb.integrable_of_hasCompactSupport hb₀
  have hIntProd (j : Fin N) : Integrable (fun q => a j (qCoord q).1 * b j (qCoord q).2) νA := by
    apply (integrable_map_equiv qCoord.symm.toMeasurableEquiv _).mpr
    change Integrable (fun q => a j (qCoord (qCoord.symm q)).1 * b j (qCoord (qCoord.symm q)).2)
      ((ν 0).prod (ν 1))
    simpa only [Homeomorph.apply_symm_apply] using (hIntA j).mul_prod (hIntB j)
  have hTerms (j : Fin N) :
      (∫ q, a j (qCoord q).1 * b j (qCoord q).2 ∂νA) =
        sigmaOrbitalIntegral σ (m 0 + 1) (D 0) (ν 0) ⇑(α j) *
          sigmaOrbitalIntegral σ (m 1 + 1) (D 1) (ν 1) ⇑(β j) := by
    change (∫ q, a j (qCoord q).1 * b j (qCoord q).2
      ∂Measure.map qCoord.symm.toMeasurableEquiv ((ν 0).prod (ν 1))) = _
    rw [integral_map_equiv]
    change (∫ q, a j (qCoord (qCoord.symm q)).1 * b j (qCoord (qCoord.symm q)).2
      ∂(ν 0).prod (ν 1)) = _
    simp only [Homeomorph.apply_symm_apply]
    exact integral_prod_mul (a j) (b j)
  change (∫ q, φ q ∂νδ) = _
  rw [hOrb]
  simp_rw [hInner, integral_const_mul]
  rw [integral_finsetSum _ (fun j _ => hIntProd j)]
  simp only [hTerms, ordinaryTwoBlockOrbitalFactor, jac, d, kF, mul_assoc]

end Pointwise

set_option maxHeartbeats 3000000 in
/-- The ordinary and twisted formulas hold with associated block measures and a common scalar. -/
theorem associatedSphericalTwoBlockOrbitalDescent : AssociatedSphericalTwoBlockOrbitalDescentStatement.{u,v} := by
  intro p _ F E _ _ σ l r m h dxF _ dxE _ hσ _ hdxF hdxE L D
  dsimp only
  intro hΓ hReg hCop hn _ μδ _ _ μγ _ _ νδ νγ hνδ hνγ hAssoc
  let : Module.Finite F.Carrier E.Carrier := hσ.1
  let : IsModuleTopology F.Carrier E.Carrier := isModuleTopology_padic_extension F E
  let B := succBlockShape m h
  let H := glCentralizer (B.leviEmbedding F.Carrier L)
  let C := fun i : Fin 2 => glCentralizer (L i)
  let Cσ := fun i : Fin 2 => sigmaCentralizer σ (m i + 1) (D i)
  have hMeasures (i : Fin 2) :
      ∃ (μF : Measure (C i)) (νF : Measure (LeftQuotient (C i)))
        (μE : Measure (Cσ i)) (νE : Measure (LeftQuotient (Cσ i))),
        μF.IsHaarMeasure ∧ μE.IsHaarMeasure ∧
          ∃ (hRF : μF.IsMulRightInvariant) (hRE : μE.IsMulRightInvariant),
            letI := hRF
            letI := hRE
            IsCompatible (C i) (sphericalHaar F (m i)) μF νF ∧
            IsCompatible (Cσ i) (sphericalHaar E (m i)) μE νE ∧
            IsAssociatedMeasure σ l (D i) (L i) μE μF := by
    have hData := orbitalMeasureExistence F.Carrier E.Carrier σ l (m i + 1) hσ
      (sphericalHaar F (m i)) (sphericalHaar E (m i))
    obtain ⟨⟨μF, hHF, hRF⟩, hνF⟩ := hData.1 (L i) (hReg i)
    let : μF.IsHaarMeasure := hHF
    let : μF.IsMulRightInvariant := hRF
    obtain ⟨νF, hνF⟩ := hνF μF
    have hNorm : IsNormAssociated σ l (D i) (L i) :=
      ⟨1, by simpa only [inv_one, one_mul, mul_one] using hn i⟩
    obtain ⟨μE, hHE, hRE, hAss, νE, hνE⟩ := hData.2 (D i) (L i) hNorm (hReg i) μF
    exact ⟨μF, νF, μE, νE, hHF, hHE, hRF, hRE, hνF, hνE, hAss⟩
  choose μF νF μE νE hM using hMeasures
  let : ∀ i, (μF i).IsHaarMeasure := fun i => (hM i).1
  let : ∀ i, (μE i).IsHaarMeasure := fun i => (hM i).2.1
  let : ∀ i, (μF i).IsMulRightInvariant := fun i => (hM i).2.2.choose
  let : ∀ i, (μE i).IsMulRightInvariant := fun i => (hM i).2.2.choose_spec.choose
  have hνs (i : Fin 2) := (hM i).2.2.choose_spec.choose_spec
  have hClosed {n : ℕ} (g : GeneralLinear n F.Carrier) :
      IsClosed (glCentralizer g : Set (GeneralLinear n F.Carrier)) := by
    rw [glCentralizer_eq_centralizer]
    exact Set.isClosed_centralizer _
  let : LocallyCompactSpace H := (hClosed (B.leviEmbedding F.Carrier L)).locallyCompactSpace
  let : SecondCountableTopology H := IsEmbedding.subtypeVal.secondCountableTopology
  let : ∀ i : Fin 2, LocallyCompactSpace (C i) := fun i => (hClosed (L i)).locallyCompactSpace
  let : ∀ i : Fin 2, SecondCountableTopology (C i) := fun _ => IsEmbedding.subtypeVal.secondCountableTopology
  let eF := ordinaryLeviCentralizerEquiv F h L hCop
  let productF := finTwoSubgroupMeasure C (μF 0) (μF 1)
  let : productF.IsHaarMeasure := by dsimp only [productF, C]; infer_instance
  let μ₀ := Measure.map eF productF
  let : μ₀.IsHaarMeasure := eF.isHaarMeasure_map productF
  let c := haarScalarFactor μγ μ₀
  have hc : c ≠ 0 := (haarScalarFactor_pos_of_isHaarMeasure μγ μ₀).ne'
  have hScaleF : μγ = c • μ₀ := isMulLeftInvariant_eq_smul μγ μ₀
  have hScaleE := twoBlockHaarScale_of_associated F E h L D hσ hΓ hReg hCop hn
    μF μE (fun i => (hνs i).2.2) μγ μδ hAssoc c hScaleF
  refine ⟨ordinaryTwoBlockOrbitalFactor F h L c, μF, νF, μE, νE, hM, ?_, ?_⟩
  · intro f N α β hExpansion
    exact orbitalIntegral_twoBlock_of_expansion F h L hΓ hReg hCop μF νF
      (fun i => (hνs i).1) μγ νγ hνγ c hc hScaleF dxF hdxF f α β hExpansion
  · intro f N α β hExpansion
    exact sigmaOrbitalIntegral_twoBlock_of_expansion F E h hσ L D hΓ hReg hCop hn μE νE
      (fun i => (hνs i).2.1) μδ νδ hνδ c hc hScaleE dxE hdxE f α β hExpansion

/-- The fundamental lemma follows from its regular elliptic case and the existence
of the unramified base-change homomorphisms. The full two-block descent is proved. -/
def FundamentalLemmaEllipticReductionStatement : Prop :=
  RegularEllipticFundamentalLemmaStatement.{u,v} →
    UnramifiedBaseChangeHomStatement.{u,v} → FundamentalLemmaStatement.{u,v}

theorem fundamentalLemmaEllipticReduction : FundamentalLemmaEllipticReductionStatement.{u,v} := by
  intro hEll hBase
  exact fundamentalLemmaOrdinaryDescentReduction hEll hBase associatedSphericalTwoBlockOrbitalDescent

end Langlands.BaseChange
