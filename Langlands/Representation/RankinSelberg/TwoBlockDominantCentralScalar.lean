import Langlands.Representation.RankinSelberg.TwoBlockJacquetData
import Langlands.Representation.RankinSelberg.GammaFactor

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  Polynomial TwoBlockJacquet LocalFactor
open scoped NNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance equalGammaTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalGammaValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalGammaLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalGammaT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance equalGammaMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalGammaBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalGammaGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalGammaGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalGammaUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalGammaQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalGammaQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [hadd : ∀ i, AddCommGroup (W i)]
  [hmod : ∀ i, Module ℂ (W i)]

local instance equalGammaReverseAdd : ∀ i : Fin 2, AddCommGroup (W i.rev) :=
  fun i => hadd i.rev
local instance equalGammaReverseModule : ∀ i : Fin 2, Module ℂ (W i.rev) :=
  fun i => hmod i.rev

section CentralScalar

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (ζ : Fin 2 → ℂˣ)
  (hζ : ∀ i, HasModelMinusOneScalar (σ i) (ell i) (ζ i))

include hζ

theorem tensorContraction_blockMinusOne (v : PiTensorProduct ℂ W) :
    tensorContraction (fun i => (ell i).val)
        ((succBlockShape m h).blockTensor σ (fun _ => -1) v) =
      (∏ i, (ζ i : ℂ)) * tensorContraction (fun i => (ell i).val) v := by
  have hell (i : Fin 2) (v : W i) :
      (ell i).val (σ i (-1) v) = (ζ i : ℂ) * (ell i).val v := by
    have ht := hζ i (modelMap (σ i) (ell i) v) 1
    change (ell i).val (σ i ((-1) * 1) v) =
      (ζ i : ℂ) * (ell i).val (σ i 1 v) at ht
    simpa only [mul_one, map_one, Module.End.one_apply] using ht
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    rw [map_smul, map_smul, map_smul, BlockShape.blockTensor_tprod,
      tensorContraction_tprod, tensorContraction_tprod, smul_eq_mul, smul_eq_mul,
      mul_left_comm, ← Finset.prod_mul_distrib]
    congr 2
    funext i
    exact hell i (v i)
  | add v v' hv hv' =>
    rw [map_add, map_add, hv, hv', map_add, mul_add]

omit ψ σ ell ζ hζ in
theorem leviEmbedding_blockMinusOne :
    (succBlockShape m h).leviEmbedding F.Carrier (fun _ => -1) =
      (-1 : GeneralLinear (t + 1) F.Carrier) := by
  let B := succBlockShape m h
  apply Units.ext
  ext x y
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective y
  change B.leviEmbedding F.Carrier (fun _ => -1) (B.index i a) (B.index j b) = _
  by_cases hij : i = j
  · subst j
    rw [BlockShape.leviEmbedding_apply_same]
    change (-1 : GeneralLinear (B.size i) F.Carrier).val a b =
      (-1 : GeneralLinear (t + 1) F.Carrier).val (B.index i a) (B.index i b)
    simp only [Units.val_neg, Units.val_one, Matrix.neg_apply, Matrix.one_apply,
      (B.index i).injective.eq_iff]
  · rw [BlockShape.leviEmbedding_apply_ne _ _ _ _ _ hij]
    have hne : B.index i a ≠ B.index j b := by
      intro heq
      have hh := B.indexEquiv.injective heq
      exact hij (congrArg Sigma.fst hh)
    change (0 : F.Carrier) =
      (-1 : GeneralLinear (t + 1) F.Carrier).val (B.index i a) (B.index j b)
    simp [hne]

omit ψ σ ell ζ hζ in
theorem leviModulus_blockMinusOne :
    F.canonicalTopologicalData.leviModulus (succBlockShape m h) (fun _ => -1) = 1 := by
  let L : (succBlockShape m h).Levi F.Carrier := fun _ => -1
  have hL : L * L = 1 := by
    funext i
    change (-1 : GeneralLinear (m i + 1) F.Carrier) * (-1) = 1
    simp
  let q := F.canonicalTopologicalData.leviModulus (succBlockShape m h) L
  have hq : q * q = 1 := by rw [← map_mul, hL, map_one]
  apply Units.ext
  apply NNReal.eq
  have he : (q : ℝ) * (q : ℝ) = 1 := by
    simpa only [Units.val_mul, NNReal.coe_mul, Units.val_one, NNReal.coe_one] using
      congrArg (fun x : ℝ≥0ˣ => ((x : ℝ≥0) : ℝ)) hq
  have hp : 0 ≤ (q : ℝ) := (q : ℝ≥0).coe_nonneg
  change (q : ℝ) = 1
  nlinarith

theorem scalarSection_blockMinusOne
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    scalarSection (fun i => (ell i).val) f ((-1) * g) 1 =
      (∏ i, (ζ i : ℂ)) * scalarSection (fun i => (ell i).val) f g 1 := by
  have hc := F.canonicalTopologicalData.normalizedOppositeParabolicInduced_covariant
    (succBlockShape m h) ((succBlockShape m h).blockTensor σ) f
    ((succBlockShape m h).oppositeLeviInParabolic F.Carrier (fun _ => -1)) g
  have he : sectionEval F h σ f ((-1) * g) =
      (succBlockShape m h).blockTensor σ (fun _ => -1) (sectionEval F h σ f g) := by
    simpa only [BlockShape.oppositeLeviInParabolic_val,
      BlockShape.oppositeLeviProjection_section, leviEmbedding_blockMinusOne,
      leviModulus_blockMinusOne, Units.val_one, NNReal.sqrt_one, NNReal.coe_one,
      Complex.ofReal_one, inv_one, one_smul] using hc
  rw [scalarSection_one, he, tensorContraction_blockMinusOne F h ψ σ ell ζ hζ,
    scalarSection_one]

theorem jacquetFunction_blockMinusOne
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier) :
    jacquetFunction ψ (fun i => (ell i).val) μR f ((-1) * g) =
      (∏ i, (ζ i : ℂ)) * jacquetFunction ψ (fun i => (ell i).val) μR f g := by
  simp only [jacquetFunction_def, integrand_def]
  have heq (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
      upperRadical h F.Carrier x * ((-1) * g) =
        (-1) * (upperRadical h F.Carrier x * g) := by simp
  simp_rw [heq, scalarSection_blockMinusOne F h ψ σ ell ζ hζ, mul_assoc]
  exact integral_const_mul _ _

theorem hasModelMinusOneScalar_of_jacquetRealization
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (J : glInverseFunctionals ψ t (inducedRep F h σ))
    (hJ : ∀ (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier),
      J.val (inducedRep F h σ g f) =
        jacquetFunction ψ (fun i => (ell i).val) μR f g) :
    HasModelMinusOneScalar (inducedRep F h σ) J (∏ i, ζ i) := by
  intro U g
  obtain ⟨f, rfl⟩ := modelMap_surjective (inducedRep F h σ) J U
  change J.val (inducedRep F h σ ((-1) * g) f) =
    ((∏ i, ζ i : ℂˣ) : ℂ) * J.val (inducedRep F h σ g f)
  rw [hJ, hJ, jacquetFunction_blockMinusOne F h ψ σ ell ζ hζ]
  simp

omit hζ in
def JacquetCentralScalarLaw : Prop :=
  ∀ (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    (J : glInverseFunctionals ψ t (inducedRep F h σ)),
    (∀ (f : Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier),
      J.val (inducedRep F h σ g f) =
        jacquetFunction ψ (fun i => (ell i).val) μR f g) →
    HasModelMinusOneScalar (inducedRep F h σ) J (∏ i, ζ i)

theorem jacquetCentralScalarLaw : JacquetCentralScalarLaw F h ψ σ ell ζ := by
  intro μR J hJ
  exact hasModelMinusOneScalar_of_jacquetRealization F h ψ σ ell ζ hζ μR J hJ

end CentralScalar

end Langlands.RankinSelberg.DominantRankTransport
