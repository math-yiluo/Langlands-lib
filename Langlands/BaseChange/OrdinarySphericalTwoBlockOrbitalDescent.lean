import Langlands.Analysis.Local.QuotientFinTwoCompatibility
import Langlands.BaseChange.FundamentalLemmaSphericalDescentReduction
import Langlands.BaseChange.LeviBlockCentralizer
import Langlands.BaseChange.OrdinaryTwoBlockRadical
import Langlands.BaseChange.RegularSemisimpleOrbit
import Langlands.BaseChange.TwoBlockQuotientIntegration
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity

/-! Ordinary orbital descent in the exact spherical two-block coordinates. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory MeasureTheory.Measure _root_.Topology Langlands.GeneralLinear
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg Langlands.RankinSelberg.TwoBlockJacquet
open Langlands.JacquetLanglands Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.HarmonicAnalysis Langlands.Unramified
open scoped NNReal

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

local instance ordinaryDescentFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance ordinaryDescentFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance ordinaryDescentFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance ordinaryDescentFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance ordinaryDescentGlLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_locallyCompactSpace F.Carrier n
local instance ordinaryDescentGlSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_secondCountableTopology F.Carrier n
local instance ordinaryDescentGlSigmaCompact (n : ℕ) : SigmaCompactSpace (GeneralLinear n F.Carrier) :=
  LocalFieldTopology.generalLinear_sigmaCompactSpace F.Carrier n
local instance ordinaryDescentGlHaarRightInvariant (n : ℕ) :
    (generalLinearHaar F.Carrier n).IsMulRightInvariant :=
  generalLinearHaarRightInvariant F.Carrier n

private abbrev ordinaryOrbitFunction {n : ℕ} (g : GeneralLinear n F.Carrier)
    (f : GeneralLinear n F.Carrier → ℂ) : LeftQuotient (glCentralizer g) → ℂ :=
  twistedOrbitFunction (MonoidHom.id _) g f

private theorem closed_glCentralizer {n : ℕ} (g : GeneralLinear n F.Carrier) :
    IsClosed (glCentralizer g : Set (GeneralLinear n F.Carrier)) := by
  rw [glCentralizer_eq_centralizer]
  exact Set.isClosed_centralizer _

private theorem compactContinuous_ordinaryOrbitFunction {r : ℕ}
    (g : GeneralLinear (r + 1) F.Carrier) (hg : IsRegularSemisimple g)
    (f : SphericalHeckeAlgebra F r) :
    Continuous (ordinaryOrbitFunction F g f) ∧ HasCompactSupport (ordinaryOrbitFunction F g f) := by
  let φ : SchwartzBruhat (GeneralLinear (r + 1) F.Carrier) := f.val
  refine ⟨?_, hasCompactSupport_regularSemisimpleOrbitFunction g hg φ.hasCompactSupport⟩
  change Continuous (twistedOrbitFunction (MonoidHom.id _) g (φ : _ → ℂ))
  rw [regularSemisimpleOrbitFunction_eq_comp g hg]
  exact φ.continuous.comp
    (continuous_subtype_val.comp (regularSemisimpleOrbitHomeomorph g hg).continuous)

private theorem exists_glCentralizerHaar_compatible {r : ℕ}
    (g : GeneralLinear (r + 1) F.Carrier) (hg : IsRegularSemisimple g) :
    ∃ (μ : Measure (glCentralizer g)) (ν : Measure (LeftQuotient (glCentralizer g))),
      μ.IsHaarMeasure ∧ ∃ hRight : μ.IsMulRightInvariant,
        letI := hRight
        IsCompatible (glCentralizer g) (sphericalHaar F r) μ ν := by
  have hClosed := closed_glCentralizer F g
  let : LocallyCompactSpace (glCentralizer g) := hClosed.locallyCompactSpace
  let : SecondCountableTopology (glCentralizer g) := IsEmbedding.subtypeVal.secondCountableTopology
  let μ : Measure (glCentralizer g) := Measure.haar
  let : μ.IsHaarMeasure := inferInstance
  let hRight : μ.IsMulRightInvariant := ⟨fun t => by
    have heq : (· * t) = (t * ·) := funext fun s => glCentralizer_mul_comm hg s t
    rw [heq, map_mul_left_eq_self]⟩
  let : μ.IsMulRightInvariant := hRight
  let : μ.Regular := Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure μ
  obtain ⟨ν, hν⟩ := compatibleMeasureExists (glCentralizer g) hClosed
    (generalLinearHaar F.Carrier r) μ
  exact ⟨μ, ν, inferInstance, hRight, (sphericalHaar_eq_generalLinearHaar F r).symm ▸ hν⟩

variable {r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = r + 1)

local notation "B" => succBlockShape m h
local notation "M" => BlockShape.Levi B F.Carrier
local notation "G" => GeneralLinear (r + 1) F.Carrier
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier
local notation "T" => F.canonicalTopologicalData

/-- The ordinary block centralizer subgroup of the Levi in its product coordinates
is isomorphic to the centralizer in the ambient group. -/
def ordinaryLeviCentralizerEquiv (L : M)
    (hCop : Pairwise fun i j => IsCoprime (L i).val.charpoly (L j).val.charpoly) :
    (Subgroup.pi Set.univ fun i => glCentralizer (L i)) ≃ₜ*
      glCentralizer ((B).leviEmbedding F.Carrier L) :=
  (piSubgroupHomeomorph fun i => glCentralizer (L i)).trans
    (glCentralizerLeviPiEquiv B L hCop).symm

/-- The common scalar in the ordinary orbital expansion, with subgroup Haar
scale `c`, the inverse radical Jacobian, and the inverse half modulus. -/
def ordinaryTwoBlockOrbitalFactor (L : M) (c : ℝ≥0) : ℂ :=
  ((c : ℝ) : ℂ)⁻¹ * (((T).normalizedAbsHom (ordinaryRadicalMatrix h L).det)⁻¹ : ℝ≥0).toReal *
    ((T).leviHalfModulus B L : ℂ)⁻¹

set_option maxHeartbeats 3000000 in
/-- Integrating a normalized finite spherical expansion on the ordinary block
centralizer quotients recovers the original orbital integral up to the displayed scalar. -/
theorem orbitalIntegral_twoBlock_of_expansion
    (L : M) (hreg : IsRegularSemisimple ((B).leviEmbedding F.Carrier L))
    (hRegBlocks : ∀ i : Fin 2, IsRegularSemisimple (L i))
    (hCop : Pairwise fun i j => IsCoprime (L i).val.charpoly (L j).val.charpoly)
    (μ : ∀ i : Fin 2, Measure (glCentralizer (L i)))
    [∀ i, (μ i).IsHaarMeasure] [∀ i, (μ i).IsMulRightInvariant]
    (ν : ∀ i : Fin 2, Measure (LeftQuotient (glCentralizer (L i))))
    (hν : ∀ i, IsCompatible (glCentralizer (L i)) (sphericalHaar F (m i)) (μ i) (ν i))
    (μγ : Measure (glCentralizer ((B).leviEmbedding F.Carrier L))) [μγ.IsHaarMeasure]
    [μγ.IsMulRightInvariant]
    (νγ : Measure (LeftQuotient (glCentralizer ((B).leviEmbedding F.Carrier L))))
    (hνγ : IsCompatible _ (sphericalHaar F r) μγ νγ)
    (c : ℝ≥0) (hc : c ≠ 0)
    (hScale : μγ = c • Measure.map (ordinaryLeviCentralizerEquiv F h L hCop)
      (finTwoSubgroupMeasure (fun i => glCentralizer (L i)) (μ 0) (μ 1)))
    (dx : Measure Rect) [dx.IsAddHaarMeasure]
    (hdx : dx {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F.Carrier).integer} = 1)
    (f : SphericalHeckeAlgebra F r) {N : ℕ}
    (α : Fin N → SphericalHeckeAlgebra F (m 0)) (β : Fin N → SphericalHeckeAlgebra F (m 1))
    (hExpansion : ∀ V : M, ((T).leviHalfModulus B V : ℂ) *
      (∫ x, f (parabolicPoint h (V, x)) ∂dx) = ∑ j, α j (V 0) * β j (V 1)) :
    orbitalIntegral ((B).leviEmbedding F.Carrier L) νγ ⇑f =
      ordinaryTwoBlockOrbitalFactor F h L c * ∑ j,
        orbitalIntegral (L 0) (ν 0) ⇑(α j) * orbitalIntegral (L 1) (ν 1) ⇑(β j) := by
  let γ := (B).leviEmbedding F.Carrier L
  let H := glCentralizer γ
  let C := fun i : Fin 2 => glCentralizer (L i)
  let A := Subgroup.pi Set.univ C
  let e : A ≃ₜ* H := ordinaryLeviCentralizerEquiv F h L hCop
  have he (a : A) : (e a).val = (B).leviEmbedding F.Carrier a.val := rfl
  let νA := finTwoQuotientMeasure C (ν 0) (ν 1)
  let μA := finTwoSubgroupMeasure C (μ 0) (μ 1)
  have hC (i : Fin 2) : IsClosed (C i : Set (GeneralLinear (m i + 1) F.Carrier)) :=
    closed_glCentralizer F (L i)
  let : ∀ i : Fin 2, LocallyCompactSpace (C i) := fun i => (hC i).locallyCompactSpace
  let : ∀ i : Fin 2, SecondCountableTopology (C i) := fun _ =>
    IsEmbedding.subtypeVal.secondCountableTopology
  let : ∀ i : Fin 2, LocallyCompactSpace (LeftQuotient (C i)) := fun i =>
    leftQuotient_locallyCompactSpace (C i)
  let : ∀ i : Fin 2, SecondCountableTopology (LeftQuotient (C i)) := fun i =>
    (leftQuotient_isOpenQuotientMap (C i)).secondCountableTopology
  let : ∀ i : Fin 2, (ν i).Regular := fun i => (hν i).regular
  let : μA.IsMulRightInvariant := by dsimp only [μA, C]; infer_instance
  have h_A : IsClosed (A : Set M) := isClosed_set_pi (fun i _ => hC i)
  have hνA : IsCompatible A (Measure.pi fun i => generalLinearHaar F.Carrier (m i)) μA νA := by
    apply finTwoQuotientMeasure_isCompatible C hC
    · rw [← sphericalHaar_eq_generalLinearHaar]
      exact hν 0
    · rw [← sphericalHaar_eq_generalLinearHaar]
      exact hν 1
  let φ := ordinaryOrbitFunction F γ f
  obtain ⟨hφ, hφ₀⟩ := compactContinuous_ordinaryOrbitFunction F γ hreg f
  have hInv (q : LeftQuotient H) (k : sphericalOpenSubgroup F r) :
      φ (rightTranslate H k.val q) = φ q := by
    induction q using Quotient.inductionOn with
    | h U =>
      change f ((U * k.val)⁻¹ * γ * (U * k.val)) = f (U⁻¹ * γ * U)
      have hMul : (U * k.val)⁻¹ * γ * (U * k.val) =
          (k⁻¹).val * (U⁻¹ * γ * U) * k.val := by
        change (U * k.val)⁻¹ * γ * (U * k.val) = k.val⁻¹ * (U⁻¹ * γ * U) * k.val
        simp only [mul_inv_rev, mul_assoc]
      rw [hMul]
      calc
        _ = f ((k⁻¹).val * (U⁻¹ * γ * U)) :=
          Hecke.HeckeAlgebra.Corner.rightInvariant _ _ _ f k _
        _ = _ := Hecke.HeckeAlgebra.Corner.leftInvariant _ _ _ f k⁻¹ _
  have hOrb := integral_twoBlock_leviRadicalQuotientPoint F h A H e he h_A
    (closed_glCentralizer F γ) μA μγ c hc hScale νA νγ hνA hνγ dx hdx φ hφ hφ₀ hInv
  let qCoord := finTwoLeftQuotientHomeomorph C
  let a (j : Fin N) := ordinaryOrbitFunction F (L 0) (α j)
  let b (j : Fin N) := ordinaryOrbitFunction F (L 1) (β j)
  let d : ℂ := (((T).normalizedAbsHom (ordinaryRadicalMatrix h L).det)⁻¹ : ℝ≥0).toReal
  let δ : ℂ := ((T).leviHalfModulus B L : ℂ)
  have hδ : δ ≠ 0 := Units.ne_zero _
  have hInner (q : LeftQuotient A) :
      (∫ x, φ (leviRadicalQuotientPoint h A H e he (q, x)) ∂dx) =
        d * δ⁻¹ * ∑ j, a j (qCoord q).1 * b j (qCoord q).2 := by
    induction q using Quotient.inductionOn with
    | h U =>
      let V : M := U⁻¹ * L * U
      have hChar (i : Fin 2) : (V i).val.charpoly = (L i).val.charpoly := by
        change ((U i)⁻¹ * L i * U i).val.charpoly = (L i).val.charpoly
        simp only [Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
      have hVCop : Pairwise fun i j => IsCoprime (V i).val.charpoly (V j).val.charpoly := by
        simpa only [hChar] using hCop
      have hConj (x : Rect) :
          φ (leviRadicalQuotientPoint h A H e he (leftQuotientMap A U, x)) =
            f ((upperRadical h F.Carrier x)⁻¹ * (B).leviEmbedding F.Carrier V *
              upperRadical h F.Carrier x) := by
        rw [leviRadicalQuotientPoint_mk]
        change f ((parabolicPoint h (U, x))⁻¹ * γ * parabolicPoint h (U, x)) = _
        simp only [parabolicPoint, γ, V, map_mul, map_inv, mul_inv_rev, mul_assoc]
      change (∫ x, φ (leviRadicalQuotientPoint h A H e he (leftQuotientMap A U, x)) ∂dx) = _
      simp_rw [hConj]
      let f₀ : SchwartzBruhat G := f.val
      rw [integral_upperRadical_conj_leviEmbedding F h V hVCop dx ⇑f f₀.continuous,
        ordinaryRadicalMatrix_det_conj h L U, NNReal.smul_def, Complex.real_smul]
      have hHalf : ((T).leviHalfModulus B V : ℂ) = δ := by
        let κ := (T).leviHalfModulus B
        have hκ : κ V = κ L := by
          rw [show V = U⁻¹ * L * U from rfl, map_mul, map_mul, map_inv,
            mul_comm (κ U)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
        exact congrArg Units.val hκ
      have hs := hExpansion V
      rw [hHalf] at hs
      change d * (∫ x, f (parabolicPoint h (V, x)) ∂dx) =
        d * δ⁻¹ * ∑ j, α j (V 0) * β j (V 1)
      rw [← hs, mul_assoc d, ← mul_assoc δ⁻¹, inv_mul_cancel₀ hδ, one_mul]
  have hIntA (j : Fin N) : Integrable (a j) (ν 0) := by
    obtain ⟨ha, ha₀⟩ := compactContinuous_ordinaryOrbitFunction F (L 0) (hRegBlocks 0) (α j)
    exact ha.integrable_of_hasCompactSupport ha₀
  have hIntB (j : Fin N) : Integrable (b j) (ν 1) := by
    obtain ⟨hb, hb₀⟩ := compactContinuous_ordinaryOrbitFunction F (L 1) (hRegBlocks 1) (β j)
    exact hb.integrable_of_hasCompactSupport hb₀
  have hIntProd (j : Fin N) : Integrable (fun q => a j (qCoord q).1 * b j (qCoord q).2) νA := by
    apply (integrable_map_equiv qCoord.symm.toMeasurableEquiv _).mpr
    change Integrable (fun q => a j (qCoord (qCoord.symm q)).1 * b j (qCoord (qCoord.symm q)).2)
      ((ν 0).prod (ν 1))
    simpa only [Homeomorph.apply_symm_apply] using (hIntA j).mul_prod (hIntB j)
  have hTerms (j : Fin N) :
      (∫ q, a j (qCoord q).1 * b j (qCoord q).2 ∂νA) =
        orbitalIntegral (L 0) (ν 0) ⇑(α j) * orbitalIntegral (L 1) (ν 1) ⇑(β j) := by
    change (∫ q, a j (qCoord q).1 * b j (qCoord q).2
      ∂Measure.map qCoord.symm.toMeasurableEquiv ((ν 0).prod (ν 1))) = _
    rw [integral_map_equiv]
    change (∫ q, a j (qCoord (qCoord.symm q)).1 * b j (qCoord (qCoord.symm q)).2
      ∂(ν 0).prod (ν 1)) = _
    simp only [Homeomorph.apply_symm_apply]
    exact integral_prod_mul (a j) (b j)
  change (∫ q, φ q ∂νγ) = _
  rw [hOrb]
  simp_rw [hInner, integral_const_mul]
  rw [integral_finsetSum _ (fun j _ => hIntProd j)]
  simp only [hTerms, ordinaryTwoBlockOrbitalFactor, d, δ, mul_assoc]

set_option maxHeartbeats 2000000 in
/-- The ordinary descent premise of the spherical base-change reduction holds
with block quotient measures and a scalar independent of the test function. -/
theorem ordinarySphericalTwoBlockOrbitalDescent :
    OrdinarySphericalTwoBlockOrbitalDescentStatement.{u} := by
  intro p _ F r m h dx _ hdx L
  dsimp only
  intro hreg hRegBlocks hCop μγ _ _ νγ hνγ
  choose μ ν hμ using fun i : Fin 2 => exists_glCentralizerHaar_compatible F (L i) (hRegBlocks i)
  let : ∀ i, (μ i).IsHaarMeasure := fun i => (hμ i).1
  let : ∀ i, (μ i).IsMulRightInvariant := fun i => (hμ i).2.choose
  let C := fun i : Fin 2 => glCentralizer (L i)
  let H := glCentralizer ((succBlockShape m h).leviEmbedding F.Carrier L)
  let : LocallyCompactSpace H :=
    (closed_glCentralizer F ((succBlockShape m h).leviEmbedding F.Carrier L)).locallyCompactSpace
  let : SecondCountableTopology H := IsEmbedding.subtypeVal.secondCountableTopology
  let : ∀ i : Fin 2, LocallyCompactSpace (C i) := fun i =>
    (closed_glCentralizer F (L i)).locallyCompactSpace
  let : ∀ i : Fin 2, SecondCountableTopology (C i) := fun _ =>
    IsEmbedding.subtypeVal.secondCountableTopology
  let e := ordinaryLeviCentralizerEquiv F h L hCop
  let μA := finTwoSubgroupMeasure C (μ 0) (μ 1)
  let : μA.IsHaarMeasure := by dsimp only [μA, C]; infer_instance
  let μ₀ := Measure.map e μA
  let : μ₀.IsHaarMeasure := e.isHaarMeasure_map μA
  let c := haarScalarFactor μγ μ₀
  have hc : c ≠ 0 := (haarScalarFactor_pos_of_isHaarMeasure μγ μ₀).ne'
  have hScale : μγ = c • μ₀ := isMulLeftInvariant_eq_smul μγ μ₀
  refine ⟨ordinaryTwoBlockOrbitalFactor F h L c, μ, ν, hμ, ?_⟩
  intro f N α β hExpansion
  exact orbitalIntegral_twoBlock_of_expansion F h L hreg hRegBlocks hCop μ ν
    (fun i => (hμ i).2.choose_spec) μγ νγ hνγ c hc hScale dx hdx f α β hExpansion

/-- With ordinary descent proved, only regular elliptic concordance,
base-change existence and associated orbital descent are needed. -/
def FundamentalLemmaOrdinaryDescentReductionStatement : Prop :=
  RegularEllipticFundamentalLemmaStatement.{u, v} →
    UnramifiedBaseChangeHomStatement.{u, v} →
    AssociatedSphericalTwoBlockOrbitalDescentStatement.{u, v} →
    FundamentalLemmaStatement.{u, v}

theorem fundamentalLemmaOrdinaryDescentReduction :
    FundamentalLemmaOrdinaryDescentReductionStatement.{u, v} := by
  intro hEll hBase hAssoc
  exact fundamentalLemmaSphericalDescentReduction hEll hBase ordinarySphericalTwoBlockOrbitalDescent hAssoc

end Langlands.BaseChange
