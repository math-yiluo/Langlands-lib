import Langlands.Representation.Shahidi.OpenCellGraded

/-! # Unfolding inner Jacquet integrals in lifted product functions

Let `Φ₁` be a Levi-invariant Levi function on a block of type `(r₁ + 1, t₁ + 1)` and `Ψ₂` a
function on `GL_(t+1)(K)` right invariant under `GL_(t+1)(𝒪)`. The lift of the degree-`D` piece of
`δ^(1/2 + s/N) J[Φ₁] ⊗ Ψ₂`, where `J[Φ₁]` is the Jacquet function of `Φ₁`, is at every point the
(Bochner) integral over the inner variable of the corresponding lift with `J[Φ₁]` replaced by the
lift of `Φ₁`; likewise in the second block, for `Ψ₁` right invariant and `Φ₂` Levi-invariant.
These unfolding lemmas are used for the block sizes `(1, d + 1, t + 1)`, where the two sections
induced in stages are compared in `Langlands.Representation.Shahidi.OpenCellThreeBlockSection`
(`leftSection_eq_rightSection`, for `ψ` of conductor `𝒪`). -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Shahidi.OpenCell

open Langlands.GeneralLinear Langlands.Conductor Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa MeasureTheory
open scoped ENNReal NNReal

universe u

variable {p : ℕ} [Fact p.Prime] {K : PadicField.{u} p}

local instance ocThreeTopologicalSpace : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology
local instance ocThreeValuativeRel : ValuativeRel K.Carrier :=
  K.canonicalTopologicalData.valuativeRel
local instance ocThreeLocalField : IsNonarchimedeanLocalField K.Carrier :=
  K.canonicalTopologicalData.localField
local instance ocThreeT2Space : T2Space K.Carrier := K.canonicalTopologicalData.fieldT2
local instance ocThreeSecondCountableTopology : SecondCountableTopology K.Carrier :=
  K.canonicalTopologicalData.secondCountableTopology
local instance ocThreeMeasurableSpace : MeasurableSpace K.Carrier := borel K.Carrier
local instance ocThreeBorelSpace : BorelSpace K.Carrier := ⟨rfl⟩

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter K.Carrier _
  K.canonicalTopologicalData.topology)
variable {ϖ : K.Carrierˣ} (hϖ : Iwasawa.IsUniformizingElement
    (@ValuativeRel.valuation _ _ K.canonicalTopologicalData.valuativeRel) ϖ)

section General

variable {r t : ℕ}
variable {Φ : Langlands.GeneralLinear (r + 1) K.Carrier → Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}

/-- The lift of a Levi-invariant `Φ` at an upper triangular point is `Φ` at its diagonal
blocks. -/
theorem liftFunction_unipotent_mul_torus (hΦ : IsLeviInvariant Φ)
    {u : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier}
    (hu : u ∈ upperUnipotent ((r + 1) + (t + 1)) K.Carrier) (ν : Fin ((r + 1) + (t + 1)) → ℤ) :
    liftFunction hϖ Φ (u * Iwasawa.torus ϖ ν) =
      Φ (topLeft u hu.1 * Iwasawa.torus ϖ fun i => ν (i.castAdd (t + 1)))
        (botRight u hu.1 * Iwasawa.torus ϖ fun j => ν (j.natAdd (r + 1))) := by
  have hb := isUpperTriangular_mul_torus hu ϖ ν
  have h := eq_upper_mul_blockSum (u * Iwasawa.torus ϖ ν) hb
  rw [topLeft_mul_torus hu, botRight_mul_torus hu] at h
  have h1 := liftFunction_law hϖ hΦ (radicalCoordinate (u * Iwasawa.torus ϖ ν) hb)
    (topLeft u hu.1 * Iwasawa.torus ϖ fun i => ν (i.castAdd (t + 1)))
    (botRight u hu.1 * Iwasawa.torus ϖ fun j => ν (j.natAdd (r + 1))) 1 (one_mem _)
  rw [mul_one, ← h] at h1
  exact h1

include hϖ in
theorem determinantNorm_blockWeyl_mul_intertwiningUnipotent
    (z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    K.canonicalTopologicalData.determinantNorm ((r + 1) + (t + 1))
      (blockWeyl (r + 1) (t + 1) K.Carrier * intertwiningUnipotent (r + 1) (t + 1) K.Carrier z) = 1 := by
  have hu : K.canonicalTopologicalData.determinantNorm ((r + 1) + (t + 1))
      (intertwiningUnipotent (r + 1) (t + 1) K.Carrier z) = 1 :=
    determinantNorm_upperUnipotent hϖ
      ⟨_, intertwiningUnipotent_mem_upperUnipotent (r + 1) (t + 1) K.Carrier z⟩
  have hw : K.canonicalTopologicalData.determinantNorm ((r + 1) + (t + 1))
      (blockWeyl (r + 1) (t + 1) K.Carrier) = 1 := by
    have h := Base.determinantNorm_mul_integral' 1 (blockWeyl (r + 1) (t + 1) K.Carrier)
      (blockWeyl_mem_integralSubgroup K r t)
    rw [one_mul, map_one] at h
    exact h
  rw [map_mul, hw, hu, one_mul]

include hϖ in
theorem determinantNorm_blockWeyl_mul_intertwiningUnipotent_real
    (z : Matrix (Fin (t + 1)) (Fin (r + 1)) K.Carrier) :
    ((K.canonicalTopologicalData.determinantNorm ((r + 1) + (t + 1))
      (blockWeyl (r + 1) (t + 1) K.Carrier * intertwiningUnipotent (r + 1) (t + 1) K.Carrier z) :
        NNReal) : ℝ) = 1 := by
  rw [determinantNorm_blockWeyl_mul_intertwiningUnipotent hϖ z]
  simp

theorem twoBlockModulus_mul_first {h m₁ : Langlands.GeneralLinear (r + 1) K.Carrier}
    (hh : K.canonicalTopologicalData.determinantNorm (r + 1) h = 1)
    (m₂ : Langlands.GeneralLinear (t + 1) K.Carrier) :
    twoBlockModulus K (h * m₁) m₂ = twoBlockModulus K m₁ m₂ := by
  rw [twoBlockModulus, twoBlockModulus, map_mul, hh, one_mul]

theorem twoBlockModulus_mul_second (m₁ : Langlands.GeneralLinear (r + 1) K.Carrier)
    {h m₂ : Langlands.GeneralLinear (t + 1) K.Carrier}
    (hh : K.canonicalTopologicalData.determinantNorm (t + 1) h = 1) :
    twoBlockModulus K m₁ (h * m₂) = twoBlockModulus K m₁ m₂ := by
  rw [twoBlockModulus, twoBlockModulus, map_mul, hh, one_mul]

include hϖ in
theorem exists_eq_upper_mul_blockSum_mul (g : Langlands.GeneralLinear ((r + 1) + (t + 1)) K.Carrier) :
    ∃ X : Matrix (Fin (r + 1)) (Fin (t + 1)) K.Carrier,
    ∃ m₁ : Langlands.GeneralLinear (r + 1) K.Carrier, ∃ m₂ : Langlands.GeneralLinear (t + 1) K.Carrier,
    ∃ k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r + 1 + t),
      g = upper (r + 1) (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k := by
  obtain ⟨q, hq, k, hk, rfl⟩ := exists_liftShape_parabolic_mul r t hϖ g
  obtain ⟨X, hX⟩ := exists_eq_upper_mul_blockSum K r t ⟨q, hq⟩
  exact ⟨X, _, _, k, hk, by rw [show q = _ from hX]⟩

end General

section Unfolding

variable {r₁ t₁ t : ℕ}

/-- **Unfolding an inner Jacquet integral in the first block**, for a Levi-invariant `Φ₁` and
`Ψ₂` right invariant under `GL_(t+1)(𝒪)`. -/
theorem liftFunction_degreePiece_prodΦ_jacquet_first
    {Φ₁ : Langlands.GeneralLinear (r₁ + 1) K.Carrier → Langlands.GeneralLinear (t₁ + 1) K.Carrier → ℂ}
    (hΦ₁ : IsLeviInvariant Φ₁) {Ψ₂ : Langlands.GeneralLinear (t + 1) K.Carrier → ℂ}
    (hΨ₂ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers t, Ψ₂ (g * k) = Ψ₂ g)
    (s : ℂ) (D : ℤ) (g : Langlands.GeneralLinear (((r₁ + 1) + (t₁ + 1)) + (t + 1)) K.Carrier) :
    liftFunction hϖ (degreePiece hϖ D (prodΦ (r := r₁ + 1 + t₁) s (jacquetFunction ψ hϖ Φ₁) Ψ₂)) g =
      ∫ z, intertwiningJacquetKernel r₁ t₁ ψ z *
        liftFunction hϖ (degreePiece hϖ D (prodΦ (r := r₁ + 1 + t₁) s (liftFunction hϖ Φ₁) Ψ₂))
          (GeneralLinear.blockSum (blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
            intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier z, 1) * g)
        ∂matrixHaar K (t₁ + 1) (r₁ + 1) := by
  have hJ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r₁ + 1 + t₁),
      jacquetFunction ψ hϖ Φ₁ (g * k) = jacquetFunction ψ hϖ Φ₁ g :=
    fun g k hk => jacquetFunction_mul_integral ψ hϖ hΦ₁ g k hk
  have hF : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r₁ + 1 + t₁),
      liftFunction hϖ Φ₁ (g * k) = liftFunction hϖ Φ₁ g :=
    fun g k hk => liftFunction_mul_integral hϖ hΦ₁ g k hk
  have hL := isLeviInvariant_degreePiece hϖ D
    (isLeviInvariant_prodΦ (r := r₁ + 1 + t₁) (t := t) s hJ hΨ₂)
  have hR := isLeviInvariant_degreePiece hϖ D
    (isLeviInvariant_prodΦ (r := r₁ + 1 + t₁) (t := t) s hF hΨ₂)
  obtain ⟨X, m₁, m₂, k, hk, rfl⟩ := exists_eq_upper_mul_blockSum_mul (r := r₁ + 1 + t₁) (t := t) hϖ g
  refine (liftFunction_law hϖ hL X m₁ m₂ k hk).trans ?_
  have hint : ∀ z : Matrix (Fin (t₁ + 1)) (Fin (r₁ + 1)) K.Carrier,
      intertwiningJacquetKernel r₁ t₁ ψ z *
        liftFunction hϖ (degreePiece hϖ D (prodΦ (r := r₁ + 1 + t₁) s (liftFunction hϖ Φ₁) Ψ₂))
          (GeneralLinear.blockSum (blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
            intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier z, 1) *
            (upper _ (t + 1) K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k)) =
      intertwiningJacquetKernel r₁ t₁ ψ z *
        degreePiece hϖ D (prodΦ (r := r₁ + 1 + t₁) (t := t) s
          (fun m => liftFunction hϖ Φ₁ (blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
            intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier z * m)) Ψ₂) m₁ m₂ := by
    intro z
    congr 1
    rw [← mul_assoc, ← mul_assoc]
    erw [blockSum_mul_upper]
    rw [mul_assoc (upper _ _ _ _), ← map_mul, Prod.mk_mul_mk, one_mul]
    refine (liftFunction_law hϖ hR _ _ _ k hk).trans ?_
    simp only [degreePiece, prodΦ]
    rw [detExponent_mul_of_determinantNorm hϖ
        (determinantNorm_blockWeyl_mul_intertwiningUnipotent_real hϖ z) m₁,
      twoBlockModulus_mul_first (determinantNorm_blockWeyl_mul_intertwiningUnipotent hϖ z)]
  refine Eq.trans ?_ (integral_congr_ae (Filter.Eventually.of_forall hint)).symm
  simp only [degreePiece, prodΦ]
  split_ifs
  · rw [jacquetFunction, ← integral_const_mul, ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [jacquetIntegrandAt_apply]
    ring
  · simp

/-- **Unfolding an inner Jacquet integral in the second block**, for `Ψ₁` right invariant under
`GL_(r₂+1)(𝒪)` and a Levi-invariant `Φ₂`. -/
theorem liftFunction_degreePiece_prodΦ_jacquet_second {r₂ : ℕ}
    {Ψ₁ : Langlands.GeneralLinear (r₂ + 1) K.Carrier → ℂ}
    (hΨ₁ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers r₂, Ψ₁ (g * k) = Ψ₁ g)
    {Φ₂ : Langlands.GeneralLinear (r₁ + 1) K.Carrier → Langlands.GeneralLinear (t₁ + 1) K.Carrier → ℂ}
    (hΦ₂ : IsLeviInvariant Φ₂) (s : ℂ) (e : ℤ)
    (g : Langlands.GeneralLinear ((r₂ + 1) + ((r₁ + 1) + (t₁ + 1))) K.Carrier) :
    liftFunction hϖ (degreePiece hϖ e (prodΦ (t := r₁ + 1 + t₁) s Ψ₁ (jacquetFunction ψ hϖ Φ₂))) g =
      ∫ Y, intertwiningJacquetKernel r₁ t₁ ψ Y *
        liftFunction hϖ (degreePiece hϖ e (prodΦ (t := r₁ + 1 + t₁) s Ψ₁ (liftFunction hϖ Φ₂)))
          (GeneralLinear.blockSum (1, blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
            intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier Y) * g)
        ∂matrixHaar K (t₁ + 1) (r₁ + 1) := by
  have hJ : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r₁ + 1 + t₁),
      jacquetFunction ψ hϖ Φ₂ (g * k) = jacquetFunction ψ hϖ Φ₂ g :=
    fun g k hk => jacquetFunction_mul_integral ψ hϖ hΦ₂ g k hk
  have hF : ∀ g, ∀ k ∈ integralSubgroup K.canonicalTopologicalData.Integers (r₁ + 1 + t₁),
      liftFunction hϖ Φ₂ (g * k) = liftFunction hϖ Φ₂ g :=
    fun g k hk => liftFunction_mul_integral hϖ hΦ₂ g k hk
  have hL := isLeviInvariant_degreePiece hϖ e
    (isLeviInvariant_prodΦ (r := r₂) (t := r₁ + 1 + t₁) s hΨ₁ hJ)
  have hR := isLeviInvariant_degreePiece hϖ e
    (isLeviInvariant_prodΦ (r := r₂) (t := r₁ + 1 + t₁) s hΨ₁ hF)
  obtain ⟨X, m₁, m₂, k, hk, rfl⟩ := exists_eq_upper_mul_blockSum_mul (r := r₂) (t := r₁ + 1 + t₁) hϖ g
  refine (liftFunction_law hϖ hL X m₁ m₂ k hk).trans ?_
  have hint : ∀ Y : Matrix (Fin (t₁ + 1)) (Fin (r₁ + 1)) K.Carrier,
      intertwiningJacquetKernel r₁ t₁ ψ Y *
        liftFunction hϖ (degreePiece hϖ e (prodΦ (t := r₁ + 1 + t₁) s Ψ₁ (liftFunction hϖ Φ₂)))
          (GeneralLinear.blockSum (1, blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
            intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier Y) *
            (upper (r₂ + 1) _ K.Carrier X * GeneralLinear.blockSum (m₁, m₂) * k)) =
      intertwiningJacquetKernel r₁ t₁ ψ Y *
        degreePiece hϖ e (prodΦ (r := r₂) (t := r₁ + 1 + t₁) s Ψ₁
          (fun m => liftFunction hϖ Φ₂ (blockWeyl (r₁ + 1) (t₁ + 1) K.Carrier *
            intertwiningUnipotent (r₁ + 1) (t₁ + 1) K.Carrier Y * m))) m₁ m₂ := by
    intro Y
    congr 1
    rw [← mul_assoc, ← mul_assoc]
    erw [blockSum_mul_upper]
    rw [mul_assoc (upper _ _ _ _), ← map_mul, Prod.mk_mul_mk, one_mul]
    refine (liftFunction_law hϖ hR _ _ _ k hk).trans ?_
    simp only [degreePiece, prodΦ]
    rw [twoBlockModulus_mul_second _ (determinantNorm_blockWeyl_mul_intertwiningUnipotent hϖ Y)]
  refine Eq.trans ?_ (integral_congr_ae (Filter.Eventually.of_forall hint)).symm
  simp only [degreePiece, prodΦ]
  split_ifs
  · rw [jacquetFunction, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
    simp only [jacquetIntegrandAt_apply]
    ring
  · simp

end Unfolding

end Langlands.Shahidi.OpenCell
