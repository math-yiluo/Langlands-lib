import Langlands.Representation.GodementJacquet.ComplexJacquetOpenCellCoordinates
import Langlands.Representation.GodementJacquet.ComplexJacquetRecursionWeil
import Langlands.Representation.Archimedean.TransposeHaar

/-! # The open-cell unfolding of a complex Godement section -/

noncomputable section

open MeasureTheory Topology
open scoped Matrix.Norms.Elementwise NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.Global.RankinSelbergGlobal.ComplexGodement
open Langlands.Global.RankinSelbergGlobal hiding detPower
open Langlands.RankinSelberg (lastRow unipotent_det)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "G" => GeneralLinear n ℂ
local notation "H" => GeneralLinear m ℂ
local notation "U" => upperUnipotent m ℂ
local notation "Z" => Fin m → ℂ
local notation "R" => Matrix (Fin m) (Fin n) ℂ
local notation "sm" => ((m : ℕ) : ℂ) / 2
local notation "sn" => ((n : ℕ) : ℂ) / 2

/-- The upper-Borel open-cell integral of a smaller standard section. -/
def complexOpenJacquet (a : ℂˣ) (ν : Measure U) (f : H → ℂ) (g : H) : ℂ :=
  ∫ u : U, f (weylLong m ℂ * u.val * g) * traceCharacter (-a) (unipotentFourierSum r u) ∂ν

theorem complexOpenJacquet_unipotent (a : ℂˣ) (ν : Measure U) [ν.IsMulRightInvariant]
    (f : H → ℂ) (v : U) (g : H) :
    complexOpenJacquet a ν f (v.val * g) =
      traceCharacter a (unipotentFourierSum r v) * complexOpenJacquet a ν f g := by
  let τ (u : U) :=
    f (weylLong m ℂ * u.val * g) * traceCharacter (-a) (unipotentFourierSum r u)
  unfold complexOpenJacquet
  change _ = traceCharacter a (unipotentFourierSum r v) * ∫ u, τ u ∂ν
  rw [← integral_mul_right_eq_self (μ := ν) τ v, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    have hphase : unipotentFourierSum r (u * v) =
        unipotentFourierSum r u + unipotentFourierSum r v := by
      simp only [unipotentFourierSum, UpperUnipotent.mul_adjacent_entry, Finset.sum_add_distrib]
    have hcancel : traceCharacter a (unipotentFourierSum r v) *
        traceCharacter (-a) (unipotentFourierSum r v) = 1 := by
      rw [traceCharacter_neg_scale, ← traceCharacter_add, add_neg_cancel, traceCharacter_zero]
    simp only [τ, Subgroup.coe_mul, mul_assoc, hphase, traceCharacter_add]
    rw [show traceCharacter a (unipotentFourierSum r v) *
      (f (weylLong m ℂ * (u.val * (v.val * g))) *
        (traceCharacter (-a) (unipotentFourierSum r u) *
          traceCharacter (-a) (unipotentFourierSum r v))) =
      (traceCharacter a (unipotentFourierSum r v) *
        traceCharacter (-a) (unipotentFourierSum r v)) *
        (f (weylLong m ℂ * (u.val * (v.val * g))) *
          traceCharacter (-a) (unipotentFourierSum r u)) by ring, hcancel, one_mul]

/-- The joint kernel after absorbing the smaller Weyl and unipotent factors
into the smaller general linear integration variable. -/
def complexOpenGodementKernel (a : ℂˣ) (c : ComplexCharacterData)
    (Φ : R → ℂ) (f : H → ℂ) (g : G) (p : (Z × U) × H) : ℂ :=
  Φ (p.2.val * rectangularJoin 1 p.1.1 * g.val) *
    complexJacquetDetWeight c.character p.2 sn *
    f (weylLong m ℂ * p.1.2.val * p.2⁻¹) *
    traceCharacter (-a) (p.1.1 (Fin.last r) + unipotentFourierSum r p.1.2)

private theorem characterWeight_det (c : ComplexCharacterData) {j : ℕ}
    (x : GeneralLinear j ℂ) (s : ℂ) :
    characterWeight c s (determinant x) = complexJacquetDetWeight c.character x s := by
  change (c.character (determinant x) : ℂ) *
      ((complexNormalizedAbs x.val.det : ℝ) : ℂ) ^ s =
    (c.character (determinant x) : ℂ) * Complex.exp (s * Real.log (complexNormalizedAbs x.val.det))
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (complexNormalizedAbs_det_pos x).ne'),
    Complex.ofReal_log (complexNormalizedAbs_det_pos x).le, mul_comm (s : ℂ)]

private theorem godementSection_openCell (a : ℂˣ) (μ : Measure H)
    [μ.IsMulRightInvariant] (c : ComplexCharacterData)
    (Φ : R → ℂ) (f : H → ℂ) (g : G) (u : U) (z : Z) :
    godementSection μ c Φ f (weylLong n ℂ * (openCellUnipotent u z).val * g) *
        traceCharacter (-a) (unipotentFourierSum m (openCellUnipotent u z)) =
      ((c.character (-1) : ℂˣ) : ℂ) ^ m * complexJacquetDetWeight c.character g sm *
        ∫ h, complexOpenGodementKernel a c Φ f g ((z, u), h) ∂μ := by
  let v := weylLong m ℂ * u.val
  let C : ℂ := (c.character (determinant (weylLong m ℂ)) : ℂ)
  have hC : C * C = 1 := by
    dsimp only [C]
    rw [← Units.val_mul, ← map_mul, ← map_mul, weylLong_mul_self, map_one, map_one]
    rfl
  have hdet (j : ℕ) (x : upperUnipotent (j + 1) ℂ) : determinant x.val = 1 :=
    Units.ext (unipotent_det x)
  have hUWeight (j : ℕ) (x : upperUnipotent (j + 1) ℂ) (s : ℂ) :
      complexJacquetDetWeight c.character x.val s = 1 := by
    have hd := congrArg Units.val (hdet j x)
    change x.val.val.det = (1 : ℂ) at hd
    simp [complexJacquetDetWeight, detPower, hdet j x, hd, complexNormalizedAbs]
  have hInv (h : H) : weylLong m ℂ * u.val * (h * v)⁻¹ = h⁻¹ := by
    change v * (h * v)⁻¹ = h⁻¹
    rw [mul_inv_rev, mul_inv_cancel_left]
  have hV : complexJacquetDetWeight c.character v sn = C := by
    rw [show v = weylLong m ℂ * u.val from rfl, complexJacquetDetWeight_mul,
      complexJacquetDetWeight_weylLong, hUWeight r u, mul_one]
    rfl
  have hintegrand (h : H) :
      godementSectionIntegrand c Φ f (weylLong n ℂ * (openCellUnipotent u z).val * g) h *
          traceCharacter (-a) (unipotentFourierSum m (openCellUnipotent u z)) =
        C * complexOpenGodementKernel a c Φ f g ((z, u), h * v) := by
    rw [godementSectionIntegrand, trailingRows_weylLong_openCell,
      unipotentFourierSum_openCellUnipotent, characterWeight_det,
      show (((m : ℕ) : ℂ) + 1) / 2 = sn by push_cast; ring]
    simp only [complexOpenGodementKernel, hInv, complexJacquetDetWeight_mul _ h v, hV]
    simp only [v, Units.val_mul, Matrix.mul_assoc]
    conv_lhs =>
      rw [← mul_one (traceCharacter (-a) (z (Fin.last r) + unipotentFourierSum r u)), ← hC]
    ring
  unfold godementSection
  let τ := fun h : H => complexOpenGodementKernel a c Φ f g ((z, u), h)
  rw [mul_assoc, ← integral_mul_const,
    integral_congr_ae (Filter.Eventually.of_forall hintegrand), integral_const_mul,
    integral_mul_right_eq_self (μ := μ) τ v, ← mul_assoc, characterWeight_det,
    complexJacquetDetWeight_mul, complexJacquetDetWeight_mul,
    complexJacquetDetWeight_weylLong, hUWeight m (openCellUnipotent u z), mul_one]
  have hsign : (c.character (determinant (weylLong n ℂ)) : ℂ) * C =
      ((c.character (-1) : ℂˣ) : ℂ) ^ m := by
    dsimp [C]
    rw [← Units.val_mul, ← map_mul, determinant_weylLong_adjacent, map_pow, Units.val_pow_eq_pow_val]
  rw [mul_right_comm _ _ C]
  change ((c.character (determinant (weylLong n ℂ)) : ℂ) * C) * _ * _ = _
  rw [hsign]

private theorem integral_openGodementKernel (a : ℂˣ) (ν : Measure U)
    (c : ComplexCharacterData) (Φ : R → ℂ) (f : H → ℂ) (g : G) (h : H) :
    (∫ z : Z, ∫ u : U, complexOpenGodementKernel a c Φ f g ((z, u), h) ∂ν
        ∂complexCoordinateMeasure (Fin m) (-a)) =
      complexJacquetDetWeight c.character h (sn - 1) * complexOpenJacquet a ν f h⁻¹ *
        complexLastColumnFourier (-a) (fun X => Φ (X * g.val)) h.val
          (lastRow h⁻¹) := by
  let η := complexCoordinateMeasure (Fin m) (-a)
  let F := fun z : Z => Φ (rectangularJoin h.val z * g.val) *
    traceCharacter (-a) (complexCoordinatePair (lastRow h⁻¹) z)
  have hPair (z : Z) :
      complexCoordinatePair (lastRow h⁻¹) (complexColumnMul h z) = z (Fin.last r) := by
    calc
      _ = ((h⁻¹).val.mulVec (h.val.mulVec z)) (Fin.last r) := by
        simp only [complexCoordinatePair, complexColumnMul_apply, lastRow,
          Matrix.mulVec, dotProduct]
      _ = _ := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hF (z : Z) :
      F (complexColumnMul h z) =
        Φ (h.val * rectangularJoin 1 z * g.val) * traceCharacter (-a) (z (Fin.last r)) := by
    rw [show F (complexColumnMul h z) =
        Φ (rectangularJoin h.val (complexColumnMul h z) * g.val) *
          traceCharacter (-a) (complexCoordinatePair (lastRow h⁻¹) (complexColumnMul h z)) from rfl,
      hPair, complexColumnMul_apply, ← rectangularJoin_left_mul, Matrix.mul_one]
  have hDensity : (((complexAbsHom h.val.det)⁻¹ : ℝ≥0) : ℂ) =
      detPower complexNormalizedAbs h (-1) := by
    have hd : (h⁻¹).val.det = h.val.det⁻¹ := by
      change ((determinant h⁻¹ : ℂˣ) : ℂ) = ((determinant h : ℂˣ) : ℂ)⁻¹
      rw [map_inv, Units.val_inv_eq_inv_val]
    rw [← detPower_complex_inv,
      show (1 : ℂ) = ((1 : ℕ) : ℂ) by norm_num, detPower_complex_natCast, pow_one,
      hd, map_inv₀]
  have hChange :
      (∫ z : Z, Φ (h.val * rectangularJoin 1 z * g.val) *
          traceCharacter (-a) (z (Fin.last r)) ∂η) =
        detPower complexNormalizedAbs h (-1) * ∫ z : Z, F z ∂η := by
    simp_rw [← hF]
    let e := (complexColumnMul h).toHomeomorph.toMeasurableEquiv
    change (∫ z : Z, F (e z) ∂η) = _
    rw [← integral_map_equiv e F]
    change (∫ z : Z, F z ∂η.map (complexColumnMul h)) = _
    rw [map_complexColumnMul, integral_smul_nnreal_measure, NNReal.smul_def,
      Complex.real_smul, hDensity]
  have hInner (z : Z) :
      (∫ u : U, complexOpenGodementKernel a c Φ f g ((z, u), h) ∂ν) =
        (complexJacquetDetWeight c.character h sn * complexOpenJacquet a ν f h⁻¹) *
          (Φ (h.val * rectangularJoin 1 z * g.val) * traceCharacter (-a) (z (Fin.last r))) := by
    rw [complexOpenJacquet, ← integral_const_mul, ← integral_mul_const]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun u => by
      simp only [complexOpenGodementKernel, traceCharacter_add]
      ring
  simp_rw [hInner, integral_const_mul]
  change (_ * _) * (∫ z : Z, _ ∂η) = _
  rw [hChange]
  change _ = complexJacquetDetWeight c.character h (sn - 1) *
    complexOpenJacquet a ν f h⁻¹ * ∫ z, F z ∂η
  rw [sub_eq_add_neg, complexJacquetDetWeight_add]
  ring

/-- The open-cell integral of a Godement section equals the smaller-group
recursion when the three-variable unfolding kernel is integrable. -/
theorem complexOpenJacquet_godementSection_eq_groupIntegral (a : ℂˣ)
    (D : ComplexQuotientMeasureData r) (c : ComplexCharacterData)
    (Φ : R → ℂ) (f : H → ℂ) (g : G)
    (hI : Integrable (complexOpenGodementKernel a c Φ f g)
      (((complexCoordinateMeasure (Fin m) (-a)).prod D.unipotentHaar).prod D.groupHaar)) :
    let W := complexOpenJacquet a D.unipotentHaar f
    Integrable (complexJacquetRecursionGroupKernel a Φ W c.character g) D.groupHaar ∧
      (∫ z : Z, ∫ u : U,
        godementSection D.groupHaar c Φ f (weylLong n ℂ * (openCellUnipotent u z).val * g) *
          traceCharacter (-a) (unipotentFourierSum m (openCellUnipotent u z))
        ∂D.unipotentHaar ∂complexCoordinateMeasure (Fin m) (-a)) =
        ((c.character (-1) : ℂˣ) : ℂ) ^ m *
          ∫ k : H, complexJacquetRecursionGroupKernel a Φ W c.character g k ∂D.groupHaar := by
  let W := complexOpenJacquet a D.unipotentHaar f
  let e := upperEntryCoordinates m (K := ℂ)
  let : LocallyCompactSpace U := e.isClosedEmbedding.locallyCompactSpace
  let : SecondCountableTopology U := e.secondCountableTopology
  let t := RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := t.locallyCompactSpace
  let : SecondCountableTopology H := t.isInducing.secondCountableTopology
  let : TopologicalSpace.PseudoMetrizableSpace H := t.isInducing.pseudoMetrizableSpace
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.unipotentHaar.IsHaarMeasure := D.unipotentHaar_isHaar
  let : D.groupHaar.Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure D.groupHaar
  let : D.groupHaar.IsMulRightInvariant :=
    Archimedean.isMulRightInvariant_archimedeanGL ℂ m D.groupHaar
  let : D.groupHaar.IsInvInvariant := Langlands.isInvInvariant_of_isMulRightInvariant D.groupHaar
  let μ := D.groupHaar
  let ν := D.unipotentHaar
  let η := complexCoordinateMeasure (Fin m) (-a)
  let F := complexOpenGodementKernel a c Φ f g
  let J := complexJacquetRecursionGroupKernel a Φ W c.character g
  let C := complexJacquetDetWeight c.character g sm
  let s := ((c.character (-1) : ℂˣ) : ℂ) ^ m
  change Integrable J μ ∧
    (∫ z : Z, ∫ u : U, _ ∂ν ∂η) = s * ∫ k : H, J k ∂μ
  have hFerr (h : H) :
      C * (∫ z : Z, ∫ u : U, F ((z, u), h) ∂ν ∂η) = J h⁻¹ := by
    rw [integral_openGodementKernel]
    unfold J complexJacquetRecursionGroupKernel
    simp only [inv_inv, C, W]
    ring
  have hEq : (fun h : H => C * ∫ p : Z × U, F (p, h) ∂(η.prod ν)) =ᵐ[μ]
      fun h => J h⁻¹ := by
    filter_upwards [hI.prod_left_ae] with h hh
    rw [integral_prod _ hh]
    exact hFerr h
  have hInt : Integrable (fun h : H => J h⁻¹) μ :=
    (hI.integral_prod_right.const_mul C).congr hEq
  have hmp : MeasurePreserving (Inv.inv : H → H) μ μ := Measure.measurePreserving_inv μ
  refine ⟨?_, ?_⟩
  · exact (hmp.integrable_comp_emb (Homeomorph.inv H).measurableEmbedding).mp hInt
  calc
    _ = s * (C * ∫ z : Z, ∫ u : U, ∫ h : H, F ((z, u), h) ∂μ ∂ν ∂η) := by
      simp_rw [godementSection_openCell, integral_const_mul]
      ring
    _ = s * (C * ∫ h : H, ∫ p : Z × U, F (p, h) ∂(η.prod ν) ∂μ) := by
      rw [← integral_prod _ hI.integral_prod_left]
      have h' : Integrable (Function.uncurry (fun (p : Z × U) (h : H) => F (p, h)))
          ((η.prod ν).prod μ) := hI
      exact congrArg (fun v : ℂ => s * (C * v)) (integral_integral_swap h')
    _ = _ := by
      rw [← integral_const_mul, integral_congr_ae hEq, integral_inv_eq_self]

/-- The upper-Borel open-cell calculation for a Godement section, with
absolute integrability of the unfolded kernel as its premise. -/
def ComplexJacquetOpenCellUnfoldingStatement : Prop :=
  ∀ (r : ℕ) (a : ℂˣ) (D : ComplexQuotientMeasureData r) (c : ComplexCharacterData)
    (Φ : Matrix (Fin (r + 1)) (Fin ((r + 1) + 1)) ℂ → ℂ)
    (f : GeneralLinear (r + 1) ℂ → ℂ) (g : GeneralLinear ((r + 1) + 1) ℂ),
    Integrable (complexOpenGodementKernel a c Φ f g)
      (((complexCoordinateMeasure (Fin (r + 1)) (-a)).prod D.unipotentHaar).prod D.groupHaar) →
    let W := complexOpenJacquet a D.unipotentHaar f
    Integrable (complexJacquetRecursionGroupKernel a Φ W c.character g) D.groupHaar ∧
      (∫ z : Fin (r + 1) → ℂ, ∫ u : upperUnipotent (r + 1) ℂ,
        godementSection D.groupHaar c Φ f (weylLong ((r + 1) + 1) ℂ * (openCellUnipotent u z).val * g) *
          traceCharacter (-a) (unipotentFourierSum (r + 1) (openCellUnipotent u z))
        ∂D.unipotentHaar ∂complexCoordinateMeasure (Fin (r + 1)) (-a)) =
        ((c.character (-1) : ℂˣ) : ℂ) ^ (r + 1) * complexJacquetRecursion a D Φ W c.character g

theorem complexJacquetOpenCellUnfolding : ComplexJacquetOpenCellUnfoldingStatement := by
  intro r a D c Φ f g hI
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  obtain ⟨hJ, hEq⟩ := complexOpenJacquet_godementSection_eq_groupIntegral a D c Φ f g hI
  exact ⟨hJ, hEq.trans (congrArg (_ * ·)
    (complexJacquetRecursion_eq_integral_group a D Φ _ c.character
      (complexOpenJacquet_unipotent a D.unipotentHaar f) g hJ).symm)⟩

end Langlands.GodementJacquet
