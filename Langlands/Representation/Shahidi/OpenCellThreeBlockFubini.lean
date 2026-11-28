import Langlands.Representation.Shahidi.OpenCellThreeBlockSection
import Langlands.Representation.Shahidi.OpenCellThreeBlockMeasure

/-! # Transitivity of the open-cell integrals for the block sizes `(1, d + 1, t + 1)`

For `ψ` of conductor `𝒪` and every pair of degrees `(D, e₁)`, the open-cell integral at `1` for the parabolic of type
`(d + 2, t + 1)` of the degree-`D` piece of `δ^(1/2) J₁ ⊗ W°_c`, where `J₁` is the Jacquet
function of the degree-`e₁` piece of the `(1, d + 1)` section with parameters `(a₁, a')`,
equals the open-cell integral at `1` for the parabolic of type `(1, d + t + 2)` of the degree-
`e₁` piece of `δ^(1/2) W°_(a₁) ⊗ J₂`, where `J₂` is the Jacquet function of the degree-`(D - e₁)`
piece of the `(d + 1, t + 1)` section with parameters `(a', c)`. Both are the integral of the
three-block section over the open cell of the `(1, d + 1, t + 1)` parabolic: the integrand
is integrable since the degree pieces restrict to compact sets, and the two iterated integrals
are related by the measure-preserving change of variables `(Y, z) ↦ (Y_a, [Y_b - Y_a z; z])`. -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocTBFTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocTBFValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocTBFLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocTBFT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocTBFSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocTBFMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocTBFBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩
local instance ocTBFMatrixOpens (a b : ℕ) : OpensMeasurableSpace (Matrix (Fin a) (Fin b) K.Carrier) :=
  inferInstanceAs (OpensMeasurableSpace (Fin a → Fin b → K.Carrier))
local instance ocTBFMatrixSecondCountable (a b : ℕ) :
    SecondCountableTopology (Matrix (Fin a) (Fin b) K.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → K.Carrier))

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

section General

/-- A function on `GL_(n+1)(K)` that is right invariant under `GL_(n+1)(𝒪)` is continuous. -/
theorem continuous_of_mul_integral {n : ℕ} {F : Langlands.GeneralLinear (n + 1) K.Carrier → ℂ}
    (hF : ∀ g k, k ∈ integralSubgroup K.canonicalTopologicalData.Integers n → F (g * k) = F g) :
    Continuous F := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have hopen : IsOpen ((fun x => g⁻¹ * x) ⁻¹'
      (integralSubgroup K.canonicalTopologicalData.Integers n : Set _)) :=
    (isOpen_integralSubgroup _ n K.canonicalTopologicalData.isOpen_integers).preimage
      (continuous_const.mul continuous_id)
  have hmem : g ∈ (fun x => g⁻¹ * x) ⁻¹'
      (integralSubgroup K.canonicalTopologicalData.Integers n : Set _) := by
    simp only [Set.mem_preimage, inv_mul_cancel, SetLike.mem_coe]
    exact one_mem _
  filter_upwards [hopen.mem_nhds hmem] with x hx
  have h := hF g (g⁻¹ * x) hx
  rwa [mul_inv_cancel_left] at h

theorem intertwiningUnipotent_mem_integralSubgroup {r t : ℕ}
    (Z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) (hZ : Z ∈ integralMatrices K (t + 1) (r + 1)) :
    intertwiningUnipotent (r + 1) (t + 1) K.Carrier Z ∈
      integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t) := by
  have h := lower_mem_integralSubgroup Z hZ
  have hw := blockWeyl_mem_integralSubgroup K r t
  have e : intertwiningUnipotent (r + 1) (t + 1) K.Carrier Z =
      (blockWeyl (r + 1) (t + 1) K.Carrier)⁻¹ * lower (r + 1) (t + 1) K.Carrier Z *
        blockWeyl (r + 1) (t + 1) K.Carrier := by
    rw [lower]
    group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hw) h) hw

/-- **The inner integrand of an unfolded lift**, for a Levi-invariant `Φ₁` and `Ψ₂` right
invariant under `GL_(t+1)(𝒪)`. -/
theorem exists_kernel_mul_liftFunction_eq {r₁ t₁ t : ℕ}
    {Φ₁ : Langlands.GeneralLinear (r₁ + 1) K.Carrier → Langlands.GeneralLinear (t₁ + 1) K.Carrier → ℂ}
    (hΦ₁ : IsLeviInvariant Φ₁) {Ψ₂ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΨ₂ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ₂ (g * k) = Ψ₂ g)
    (s : ℂ) (D : ℤ) (g : Langlands.GeneralLinear (((r₁ + 1) + (t₁ + 1)) + (t + 1)) K.Carrier) :
    ∃ m₁ : Langlands.GeneralLinear (r₁ + 1 + t₁ + 1) K.Carrier, ∃ C : ℂ,
      detExponent hϖ m₁ = liftDegree (r := r₁ + 1 + t₁) (t := t) hϖ g ∧
      (detExponent hϖ m₁ ≠ D → C = 0) ∧
      ∀ z : Matrix (Fin (t₁ + 1)) (Fin (r₁ + 1)) K.Carrier,
        intertwiningJacquetKernel r₁ t₁ ψ z *
          liftFunction hϖ (degreePiece hϖ D (prodΦ (r := r₁ + 1 + t₁) (t := t) s
            (liftFunction hϖ Φ₁) Ψ₂))
            (GeneralLinear.blockSum (blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
              intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier z, 1) * g) =
          C * jacquetIntegrandAt ψ hϖ Φ₁ m₁ z := by
  have hF : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r₁ + 1 + t₁),
      liftFunction hϖ Φ₁ (g * k) = liftFunction hϖ Φ₁ g :=
    fun g k hk => liftFunction_mul_integral hϖ hΦ₁ g k hk
  have hR := isLeviInvariant_degreePiece hϖ D
    (isLeviInvariant_prodΦ (r := r₁ + 1 + t₁) (t := t) s hF hΨ₂)
  obtain ⟨X, m₁, m₂, k, hk, rfl⟩ := exists_eq_upper_mul_blockSum_mul (r := r₁ + 1 + t₁) (t := t) hϖ g
  refine ⟨m₁, if detExponent hϖ m₁ = D then
      ((twoBlockModulus K m₁ m₂ : ℝ) : ℂ) ^ ((1 : ℂ) / 2 + s / ((r₁ + 1 + t₁ + t + 2 : ℕ) : ℂ)) *
        Ψ₂ m₂ else 0, (liftDegree_law hϖ X m₁ m₂ k hk).symm,
    fun h => ite_eq_right_iff.2 fun h' => absurd h' h, fun z => ?_⟩
  have hl : liftFunction hϖ (degreePiece hϖ D (prodΦ (r := r₁ + 1 + t₁) (t := t) s
        (liftFunction hϖ Φ₁) Ψ₂))
        (GeneralLinear.blockSum (blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
            intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier z, 1) *
          (upper _ (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k)) =
      degreePiece hϖ D (prodΦ (r := r₁ + 1 + t₁) (t := t) s (liftFunction hϖ Φ₁) Ψ₂)
        (blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
          intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier z * m₁) m₂ := by
    rw [← mul_assoc, ← mul_assoc]
    erw [blockSum_mul_upper]
    rw [mul_assoc (upper _ _ _ _), ← map_mul, Prod.mk_mul_mk, one_mul]
    exact liftFunction_law hϖ hR _ _ _ k hk
  rw [hl, jacquetIntegrandAt_apply]
  simp only [degreePiece, prodΦ]
  rw [detExponent_mul_of_determinantNorm hϖ
      (determinantNorm_blockWeyl_mul_intertwiningUnipotent_real hϖ z) m₁,
    twoBlockModulus_mul_first (determinantNorm_blockWeyl_mul_intertwiningUnipotent hϖ z)]
  split_ifs <;> ring

end General

section Transitivity

variable (d t : ℕ) (a₁ : Fin (0 + 1) → ℂˣ) (a' : Fin (d + 1) → ℂˣ) (c : Fin (t + 1) → ℂˣ)
  (D e₁ : ℤ)

theorem kernel_headColumns (Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier) :
    intertwiningJacquetKernel (0 + 1 + d) t ψ Y = intertwiningJacquetKernel d t ψ (headColumns d t Y) := by
  rw [intertwiningJacquetKernel_eq_conj, intertwiningJacquetKernel_eq_conj]
  unfold headColumns
  congr 3

theorem kernel_shearColumn (Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier)
    (z : Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier) :
    intertwiningJacquetKernel 0 d ψ z =
      intertwiningJacquetKernel 0 (d + 1 + t) ψ (shearColumn d t Y z) := by
  rw [intertwiningJacquetKernel_eq_conj, intertwiningJacquetKernel_eq_conj]
  have h : ¬ ((Fin.last (d + 1 + t) : Fin (d + 1 + t + 1)) : ℕ) < t + 1 := by
    simp only [Fin.val_last]
    omega
  unfold shearColumn
  simp only [h, dite_false]
  congr 3
  exact congrArg (fun b => z b 0) (Fin.ext (by simp; omega))

/-- **Transitivity of the open-cell integrals of degree pieces**, for `ψ` of conductor `𝒪`. -/
theorem jacquetFunction_threeBlock (hψ : K.canonicalTopologicalData.additiveConductor ψ = 0) :
    jacquetFunction ψ hϖ (degreePiece hϖ D (prodΦ (r := 0 + 1 + d) (t := t) 0
        (jacquetFunction ψ hϖ (degreePiece hϖ e₁ (Base.fullΦ ψ hϖ a₁ a' 0)))
        (GeneralLinear.Spherical.sphericalWhittaker (n := t) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ t)
          K.canonicalTopologicalData.residueCardinality c))) 1 =
      jacquetFunction ψ hϖ (degreePiece hϖ e₁ (prodΦ (r := 0) (t := d + 1 + t) 0
        (GeneralLinear.Spherical.sphericalWhittaker (n := 0) hϖ
          (@Whittaker.standardCharacter _ _ K.canonicalTopologicalData.topology ψ 0)
          K.canonicalTopologicalData.residueCardinality a₁)
        (jacquetFunction ψ hϖ (degreePiece hϖ (D - e₁) (Base.fullΦ ψ hϖ a' c 0))))) 1 := by
  have hΦ₁ := Base.isLeviInvariant_fullΦ hϖ hψ a₁ a' 0
  have hΦ₂ := Base.isLeviInvariant_fullΦ hϖ hψ a' c 0
  have hθ₁ := isLeviEquivariant_fullΦ hϖ hψ a₁ a' 0
  have hWc := whittaker_mul_integral' hϖ hψ c
  have hWa := whittaker_mul_integral' hϖ hψ a₁
  set H' : Matrix (Fin (t + 1)) (Fin (d + 1)) K.Carrier ×
      Matrix (Fin ((d + 1) + (t + 1))) (Fin (0 + 1)) K.Carrier → ℂ := fun q =>
    intertwiningJacquetKernel 0 (d + 1 + t) ψ q.2 * (intertwiningJacquetKernel d t ψ q.1 *
      rightSection ψ hϖ d t a₁ a' c D e₁
        (GeneralLinear.blockSum (1, blockWeyl (d + 1) (t + 1) K.Carrier *
          intertwiningUnipotent (d + 1) (t + 1) K.Carrier q.1) *
          (blockWeyl (0 + 1) ((d + 1) + (t + 1)) K.Carrier *
            intertwiningUnipotent (0 + 1) ((d + 1) + (t + 1)) K.Carrier q.2))) with hH'
  set H : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier ×
      Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier → ℂ := fun p =>
    intertwiningJacquetKernel (0 + 1 + d) t ψ p.1 * (intertwiningJacquetKernel 0 d ψ p.2 *
      leftSection ψ hϖ d t a₁ a' c D e₁
        (GeneralLinear.blockSum (blockWeyl (0 + 1) (d + 1) K.Carrier *
          intertwiningUnipotent (0 + 1) (d + 1) K.Carrier p.2, 1) *
          (blockWeyl ((0 + 1) + (d + 1)) (t + 1) K.Carrier *
            intertwiningUnipotent ((0 + 1) + (d + 1)) (t + 1) K.Carrier p.1))) with hH
  have hHH : ∀ p, H p = H' (threeBlockChange K d t p) := by
    rintro ⟨Y, z⟩
    rw [threeBlockChange_apply, hH, hH']
    simp only
    rw [leftSection_eq_rightSection hϖ d t a₁ a' c D e₁ hψ]
    erw [reindex_threeBlock d t Y z]
    rw [kernel_headColumns ψ d t Y, kernel_shearColumn ψ d t Y z]
    ring
  have hcont : Continuous H := by
    have hk1 : Continuous (intertwiningJacquetKernel (0 + 1 + d) t ψ) :=
      continuous_intertwiningJacquetKernel ψ
    have hk2 : Continuous (intertwiningJacquetKernel 0 d ψ) := continuous_intertwiningJacquetKernel ψ
    have hsec : Continuous (leftSection ψ hϖ d t a₁ a' c D e₁) :=
      continuous_of_mul_integral (n := (0 + 1) + (d + 1) + t)
        (fun g k hk => leftSection_mul_integral hϖ d t a₁ a' c D e₁ hψ g k hk)
    have hmap : Continuous (fun q : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier ×
        Matrix (Fin (d + 1)) (Fin (0 + 1)) K.Carrier =>
          GeneralLinear.blockSum (blockWeyl (0 + 1) (d + 1) K.Carrier *
            intertwiningUnipotent (0 + 1) (d + 1) K.Carrier q.2, 1) *
          (blockWeyl ((0 + 1) + (d + 1)) (t + 1) K.Carrier *
            intertwiningUnipotent ((0 + 1) + (d + 1)) (t + 1) K.Carrier q.1)) :=
      ((GeneralLinear.blockSumContinuous).continuous.comp ((continuous_const.mul
        ((continuous_intertwiningUnipotent _ _ _).comp continuous_snd)).prodMk continuous_const)).mul
        (continuous_const.mul ((continuous_intertwiningUnipotent _ _ _).comp continuous_fst))
    exact (hk1.comp continuous_fst).mul ((hk2.comp continuous_snd).mul (hsec.comp hmap))
  have hinner : ∀ Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier,
      Integrable (fun z => H (Y, z)) (matrixHaar K (d + 1) (0 + 1)) := by
    intro Y
    obtain ⟨m₁, C, -, -, hz⟩ := exists_kernel_mul_liftFunction_eq ψ hϖ
      (isLeviInvariant_degreePiece hϖ e₁ hΦ₁) hWc 0 D
      (blockWeyl ((0 + 1) + (d + 1)) (t + 1) K.Carrier *
        intertwiningUnipotent ((0 + 1) + (d + 1)) (t + 1) K.Carrier Y)
    have hi := ((integrable_jacquetIntegrandAt_degreePiece ψ hϖ hΦ₁ hθ₁ e₁ m₁).const_mul C).const_mul
      (intertwiningJacquetKernel (0 + 1 + d) t ψ Y)
    refine hi.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only
    rw [← hz z]
    rfl
  have hzeroH : ∀ Y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier,
      openCellDepth hϖ Y ≠ D → ∀ z, H (Y, z) = 0 := by
    intro Y hY z
    obtain ⟨m₁, C, hdeg, hC, hz⟩ := exists_kernel_mul_liftFunction_eq ψ hϖ
      (isLeviInvariant_degreePiece hϖ e₁ hΦ₁) hWc 0 D
      (blockWeyl ((0 + 1) + (d + 1)) (t + 1) K.Carrier *
        intertwiningUnipotent ((0 + 1) + (d + 1)) (t + 1) K.Carrier Y)
    have hC0 : C = 0 := hC (by rw [hdeg]; erw [liftDegree_open]; exact hY)
    have h := hz z
    rw [hC0, zero_mul] at h
    change intertwiningJacquetKernel (0 + 1 + d) t ψ Y * (_ * _) = 0
    erw [h, mul_zero]
  have hper : ∀ (Y Z : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier),
      Z ∈ integralMatrices K (t + 1) ((0 + 1) + (d + 1)) → ∀ z, H (Y + Z, z) = H (Y, z) := by
    intro Y Z hZ z
    simp only [hH]
    congr 1
    · exact intertwiningJacquetKernel_add_integral ψ hψ Y Z hZ
    · congr 1
      rw [intertwiningUnipotent_add, ← mul_assoc (blockWeyl _ _ _), ← mul_assoc]
      exact leftSection_mul_integral hϖ d t a₁ a' c D e₁ hψ _ _
        (intertwiningUnipotent_mem_integralSubgroup Z hZ)
  have houter : Integrable (fun Y => ∫ z, ‖H (Y, z)‖ ∂matrixHaar K (d + 1) (0 + 1))
      (matrixHaar K (t + 1) ((0 + 1) + (d + 1))) := by
    set G : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier → ℝ :=
      fun Y => ∫ z, ‖H (Y, z)‖ ∂matrixHaar K (d + 1) (0 + 1) with hG
    have hGper : IsLatticePeriodic K (fun Y => (G Y : ℂ)) := by
      intro Y Z hZ
      simp only [hG, hper Y Z hZ]
    have hs : Summable fun y : Matrix (Fin (t + 1)) (Fin ((0 + 1) + (d + 1))) K.Carrier ⧸
        integralMatrices K (t + 1) ((0 + 1) + (d + 1)) => ‖((G (Quotient.out y) : ℝ) : ℂ)‖ := by
      refine summable_of_ne_finset_zero (s := shellFinset (r := 0 + 1 + d) (t := t) hϖ D) fun y hy => ?_
      rw [mem_shellFinset] at hy
      simp only [hG, hzeroH _ hy, norm_zero, integral_zero, Complex.ofReal_zero]
    obtain ⟨hint, -⟩ := integrable_and_hasSum_of_isLatticePeriodic K hGper hs
    refine hint.norm.congr (Filter.Eventually.of_forall fun Y => ?_)
    simp only
    rw [Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun z => norm_nonneg _)]
  have hint : Integrable H ((matrixHaar K (t + 1) ((0 + 1) + (d + 1))).prod
      (matrixHaar K (d + 1) (0 + 1))) :=
    (integrable_prod_iff hcont.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hinner, houter⟩
  have hint' : Integrable H' ((matrixHaar K (t + 1) (d + 1)).prod
      (matrixHaar K ((d + 1) + (t + 1)) (0 + 1))) :=
    ((measurePreserving_threeBlockChange K d t).integrable_comp_emb
      (threeBlockChange K d t).measurableEmbedding).1
      (hint.congr (Filter.Eventually.of_forall hHH))
  calc _ = ∫ Y, ∫ z, H (Y, z) ∂matrixHaar K (d + 1) (0 + 1)
          ∂matrixHaar K (t + 1) ((0 + 1) + (d + 1)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
        rw [jacquetIntegrandAt_apply, mul_one]
        erw [liftFunction_degreePiece_prodΦ_jacquet_first ψ hϖ (isLeviInvariant_degreePiece hϖ e₁ hΦ₁)
          hWc 0 D]
        rw [← integral_const_mul]
        rfl
    _ = ∫ q, H q ∂((matrixHaar K (t + 1) ((0 + 1) + (d + 1))).prod
          (matrixHaar K (d + 1) (0 + 1))) := (integral_prod H hint).symm
    _ = ∫ q, H' (threeBlockChange K d t q) ∂((matrixHaar K (t + 1) ((0 + 1) + (d + 1))).prod
          (matrixHaar K (d + 1) (0 + 1))) := integral_congr_ae (Filter.Eventually.of_forall hHH)
    _ = ∫ q, H' q ∂((matrixHaar K (t + 1) (d + 1)).prod
          (matrixHaar K ((d + 1) + (t + 1)) (0 + 1))) :=
        (measurePreserving_threeBlockChange K d t).integral_comp' H'
    _ = ∫ y, ∫ Y, H' (Y, y) ∂matrixHaar K (t + 1) (d + 1)
          ∂matrixHaar K ((d + 1) + (t + 1)) (0 + 1) := integral_prod_symm H' hint'
    _ = _ := by
        refine (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)).symm
        rw [jacquetIntegrandAt_apply, mul_one]
        erw [liftFunction_degreePiece_prodΦ_jacquet_second ψ hϖ hWa
          (isLeviInvariant_degreePiece hϖ (D - e₁) hΦ₂) 0 e₁]
        rw [← integral_const_mul]
        rfl

end Transitivity

end Langlands.Shahidi.OpenCell
