import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Unitary.HermitianDual
import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.Smooth.Contragredient.WeakIntertwiner
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.Integral

/-!
# Coefficient pairings between two representations with one central character

For representations `ρ` on `V` and `σ` on `W` whose prescribed unitary central
characters agree, the product `ℓ(σ(g⁻¹)w) · η(ρ(g)v)` descends to the central
quotient. When every such product with smooth entries is integrable, the
integral is a four-linear form whose translation laws produce intertwiners
`ρ → σ` and `σ → ρ`. Hölder's inequality gives integrability from an `L^r`
bound on the `σ`-coefficients and the conjugate `L^(r/(r-1))` bound on the
`ρ`-coefficients.
-/

noncomputable section

namespace Langlands

open MeasureTheory

universe uG uV uW

namespace UnitaryCentralCharacter

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
variable (cρ : UnitaryCentralCharacter ρ) (cσ : UnitaryCentralCharacter σ)
variable (hχ : cρ.character = cσ.character)

include hχ in
/-- With equal central characters, the coefficient product
`ℓ(σ(g⁻¹)w) · η(ρ(g)v)` is invariant under right translation by the center. -/
theorem pairingKernel_mul_center (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (g : G) (z : Subgroup.center G) :
    matrixCoefficient σ ℓ w (g * z)⁻¹ * matrixCoefficient ρ η v (g * z) =
      matrixCoefficient σ ℓ w g⁻¹ * matrixCoefficient ρ η v g := by
  have hinv : (g * z)⁻¹ = g⁻¹ * ((z⁻¹ : Subgroup.center G) : G) := by
    rw [mul_inv_rev, Subgroup.coe_inv]
    exact (Subgroup.mem_center_iff.mp (inv_mem z.2) g⁻¹).symm
  rw [hinv, cσ.matrixCoefficient_mul_center, cρ.matrixCoefficient_mul_center, hχ,
    map_inv]
  calc
    _ = ((((cσ.character z)⁻¹ : ℂˣ) : ℂ) * (cσ.character z : ℂ)) *
        (matrixCoefficient σ ℓ w g⁻¹ * matrixCoefficient ρ η v g) := by ring
    _ = _ := by rw [Units.inv_mul, one_mul]

/-- The coefficient product `ℓ(σ(g⁻¹)w) · η(ρ(g)v)` on the actual quotient by
the center. -/
def pairingKernel (ℓ : Module.Dual ℂ W) (w : W) (η : Module.Dual ℂ V) (v : V) :
    G ⧸ Subgroup.center G → ℂ :=
  Quotient.lift
    (fun g => matrixCoefficient σ ℓ w g⁻¹ * matrixCoefficient ρ η v g) (by
      intro a b hab
      have hz : a⁻¹ * b ∈ Subgroup.center G := QuotientGroup.leftRel_apply.mp hab
      have h := cρ.pairingKernel_mul_center cσ hχ ℓ w η v a ⟨a⁻¹ * b, hz⟩
      simpa using h.symm)

@[simp] theorem pairingKernel_mk (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (g : G) :
    cρ.pairingKernel cσ hχ ℓ w η v (QuotientGroup.mk g) =
      ℓ (σ g⁻¹ w) * η (ρ g v) := rfl

theorem norm_pairingKernel (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (q : G ⧸ Subgroup.center G) :
    ‖cρ.pairingKernel cσ hχ ℓ w η v q‖ =
      cσ.coefficientNorm ℓ w q⁻¹ * cρ.coefficientNorm η v q := by
  induction q using Quotient.inductionOn with
  | h g => exact norm_mul _ _

theorem pairingKernel_add_left (ℓ₁ ℓ₂ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ (ℓ₁ + ℓ₂) w η v q =
      cρ.pairingKernel cσ hχ ℓ₁ w η v q + cρ.pairingKernel cσ hχ ℓ₂ w η v q := by
  induction q using Quotient.inductionOn with
  | h g => exact add_mul _ _ _

theorem pairingKernel_smul_left (a : ℂ) (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ (a • ℓ) w η v q =
      a * cρ.pairingKernel cσ hχ ℓ w η v q := by
  induction q using Quotient.inductionOn with
  | h g => exact mul_assoc _ _ _

theorem pairingKernel_add_vector_left (ℓ : Module.Dual ℂ W) (w₁ w₂ : W)
    (η : Module.Dual ℂ V) (v : V) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ ℓ (w₁ + w₂) η v q =
      cρ.pairingKernel cσ hχ ℓ w₁ η v q + cρ.pairingKernel cσ hχ ℓ w₂ η v q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change ℓ (σ g⁻¹ (w₁ + w₂)) * η (ρ g v) =
      ℓ (σ g⁻¹ w₁) * η (ρ g v) + ℓ (σ g⁻¹ w₂) * η (ρ g v)
    rw [map_add, map_add, add_mul]

theorem pairingKernel_smul_vector_left (a : ℂ) (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ ℓ (a • w) η v q =
      a * cρ.pairingKernel cσ hχ ℓ w η v q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change ℓ (σ g⁻¹ (a • w)) * η (ρ g v) = a * (ℓ (σ g⁻¹ w) * η (ρ g v))
    rw [map_smul, map_smul, smul_eq_mul, mul_assoc]

theorem pairingKernel_add_right (ℓ : Module.Dual ℂ W) (w : W)
    (η₁ η₂ : Module.Dual ℂ V) (v : V) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ ℓ w (η₁ + η₂) v q =
      cρ.pairingKernel cσ hχ ℓ w η₁ v q + cρ.pairingKernel cσ hχ ℓ w η₂ v q := by
  induction q using Quotient.inductionOn with
  | h g => exact mul_add _ _ _

theorem pairingKernel_smul_right (a : ℂ) (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ ℓ w (a • η) v q =
      a * cρ.pairingKernel cσ hχ ℓ w η v q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change ℓ (σ g⁻¹ w) * (a * η (ρ g v)) = a * (ℓ (σ g⁻¹ w) * η (ρ g v))
    ring

theorem pairingKernel_add_vector_right (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v₁ v₂ : V) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ ℓ w η (v₁ + v₂) q =
      cρ.pairingKernel cσ hχ ℓ w η v₁ q + cρ.pairingKernel cσ hχ ℓ w η v₂ q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change ℓ (σ g⁻¹ w) * η (ρ g (v₁ + v₂)) =
      ℓ (σ g⁻¹ w) * η (ρ g v₁) + ℓ (σ g⁻¹ w) * η (ρ g v₂)
    rw [map_add, map_add, mul_add]

theorem pairingKernel_smul_vector_right (a : ℂ) (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ ℓ w η (a • v) q =
      a * cρ.pairingKernel cσ hχ ℓ w η v q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change ℓ (σ g⁻¹ w) * η (ρ g (a • v)) = a * (ℓ (σ g⁻¹ w) * η (ρ g v))
    rw [map_smul, map_smul, smul_eq_mul]
    ring

/-- Translating the `ρ`-vector moves the `σ`-functional by the contragredient
and translates the kernel on the right. -/
theorem pairingKernel_translate_right [IsTopologicalGroup G] (ℓ : SmoothDual σ) (w : W)
    (η : Module.Dual ℂ V) (v : V) (h : G) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ ℓ w η (ρ h v) q =
      cρ.pairingKernel cσ hχ (smoothContragredient σ h⁻¹ ℓ) w η v
        (q * QuotientGroup.mk h) := by
  induction q using Quotient.inductionOn with
  | h g =>
    change ℓ.1 (σ g⁻¹ w) * η (ρ g (ρ h v)) =
      ℓ.1 (σ h⁻¹⁻¹ (σ (g * h)⁻¹ w)) * η (ρ (g * h) v)
    have h₁ : σ h (σ (g * h)⁻¹ w) = σ g⁻¹ w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, mul_inv_cancel_left]
    have h₂ : ρ (g * h) v = ρ g (ρ h v) := by
      rw [map_mul, Module.End.mul_apply]
    rw [inv_inv, h₁, h₂]

/-- Translating the `σ`-vector moves the `ρ`-functional by the contragredient
and translates the kernel on the left. -/
theorem pairingKernel_translate_left [IsTopologicalGroup G] (ℓ : Module.Dual ℂ W) (w : W)
    (η : SmoothDual ρ) (v : V) (h : G) (q : G ⧸ Subgroup.center G) :
    cρ.pairingKernel cσ hχ ℓ (σ h w) η v (QuotientGroup.mk h * q) =
      cρ.pairingKernel cσ hχ ℓ w (smoothContragredient ρ h⁻¹ η) v q := by
  induction q using Quotient.inductionOn with
  | h g =>
    change ℓ (σ (h * g)⁻¹ (σ h w)) * η.1 (ρ (h * g) v) =
      ℓ (σ g⁻¹ w) * η.1 (ρ h⁻¹⁻¹ (ρ g v))
    have h₁ : σ (h * g)⁻¹ (σ h w) = σ g⁻¹ w := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
    have h₂ : ρ (h * g) v = ρ h (ρ g v) := by
      rw [map_mul, Module.End.mul_apply]
    rw [inv_inv, h₁, h₂]

variable [IsTopologicalGroup G]

theorem continuous_pairingKernel (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (hw : IsSmoothVector σ w) (hv : IsSmoothVector ρ v) :
    Continuous (cρ.pairingKernel cσ hχ ℓ w η v) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center G)).continuous_iff.mpr
  exact ((matrixCoefficient_isLocallyConstant σ ℓ w hw).continuous.comp continuous_inv).mul
    (matrixCoefficient_isLocallyConstant ρ η v hv).continuous

variable [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]

/-- Hölder's inequality: an `L^r` bound on the `σ`-coefficient, `1 < r`, and an
`L^(r/(r-1))` bound on the `ρ`-coefficient make the kernel integrable for an
inversion-invariant measure. -/
theorem integrable_pairingKernel (ℓ : Module.Dual ℂ W) (w : W)
    (η : Module.Dual ℂ V) (v : V) (μ : Measure (G ⧸ Subgroup.center G))
    [μ.IsInvInvariant] (hw : IsSmoothVector σ w) (hv : IsSmoothVector ρ v)
    {r : ℝ} (hr : 1 < r)
    (hσr : MemLp (cσ.coefficientNorm ℓ w) (ENNReal.ofReal r) μ)
    (hρr : MemLp (cρ.coefficientNorm η v) (ENNReal.ofReal r.conjExponent) μ) :
    Integrable (cρ.pairingKernel cσ hχ ℓ w η v) μ := by
  have hinv : MemLp (fun q => cσ.coefficientNorm ℓ w q⁻¹) (ENNReal.ofReal r) μ :=
    hσr.comp_measurePreserving (Measure.measurePreserving_inv μ)
  have : ENNReal.HolderConjugate (ENNReal.ofReal r) (ENNReal.ofReal r.conjExponent) :=
    ENNReal.holderConjugate_iff.mpr (Real.HolderConjugate.conjExponent hr).inv_add_inv_ennreal
  exact (hinv.integrable_mul hρr).mono'
    (cρ.continuous_pairingKernel cσ hχ ℓ w η v hw hv).aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => (cρ.norm_pairingKernel cσ hχ ℓ w η v q).le)

variable (μ : Measure (G ⧸ Subgroup.center G))

/-- The integrated coefficient pairing `∫ ℓ(σ(g⁻¹)w) · η(ρ(g)v) dġ` of smooth
functionals and vectors. -/
def coefficientPairing (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V) : ℂ :=
  ∫ q, cρ.pairingKernel cσ hχ ℓ w η v q ∂μ

/-- Integrability of every coefficient product with smooth functionals. -/
def PairingIntegrable : Prop :=
  ∀ (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V),
    Integrable (cρ.pairingKernel cσ hχ ℓ w η v) μ

variable {cρ cσ hχ μ}

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientPairing_add_left (hint : PairingIntegrable cρ cσ hχ μ)
    (ℓ₁ ℓ₂ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V) :
    cρ.coefficientPairing cσ hχ μ (ℓ₁ + ℓ₂) w η v =
      cρ.coefficientPairing cσ hχ μ ℓ₁ w η v + cρ.coefficientPairing cσ hχ μ ℓ₂ w η v := by
  unfold coefficientPairing
  simp_rw [Submodule.coe_add, pairingKernel_add_left]
  exact integral_add (hint ℓ₁ w η v) (hint ℓ₂ w η v)

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientPairing_smul_left (a : ℂ)
    (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V) :
    cρ.coefficientPairing cσ hχ μ (a • ℓ) w η v =
      a * cρ.coefficientPairing cσ hχ μ ℓ w η v := by
  unfold coefficientPairing
  simp_rw [Submodule.coe_smul, pairingKernel_smul_left]
  exact integral_const_mul _ _

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientPairing_add_vector_left (hint : PairingIntegrable cρ cσ hχ μ)
    (ℓ : SmoothDual σ) (w₁ w₂ : W) (η : SmoothDual ρ) (v : V) :
    cρ.coefficientPairing cσ hχ μ ℓ (w₁ + w₂) η v =
      cρ.coefficientPairing cσ hχ μ ℓ w₁ η v + cρ.coefficientPairing cσ hχ μ ℓ w₂ η v := by
  unfold coefficientPairing
  simp_rw [pairingKernel_add_vector_left]
  exact integral_add (hint ℓ w₁ η v) (hint ℓ w₂ η v)

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientPairing_smul_vector_left (a : ℂ)
    (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V) :
    cρ.coefficientPairing cσ hχ μ ℓ (a • w) η v =
      a * cρ.coefficientPairing cσ hχ μ ℓ w η v := by
  unfold coefficientPairing
  simp_rw [pairingKernel_smul_vector_left]
  exact integral_const_mul _ _

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientPairing_add_right (hint : PairingIntegrable cρ cσ hχ μ)
    (ℓ : SmoothDual σ) (w : W) (η₁ η₂ : SmoothDual ρ) (v : V) :
    cρ.coefficientPairing cσ hχ μ ℓ w (η₁ + η₂) v =
      cρ.coefficientPairing cσ hχ μ ℓ w η₁ v + cρ.coefficientPairing cσ hχ μ ℓ w η₂ v := by
  unfold coefficientPairing
  simp_rw [Submodule.coe_add, pairingKernel_add_right]
  exact integral_add (hint ℓ w η₁ v) (hint ℓ w η₂ v)

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientPairing_smul_right (a : ℂ)
    (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V) :
    cρ.coefficientPairing cσ hχ μ ℓ w (a • η) v =
      a * cρ.coefficientPairing cσ hχ μ ℓ w η v := by
  unfold coefficientPairing
  simp_rw [Submodule.coe_smul, pairingKernel_smul_right]
  exact integral_const_mul _ _

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientPairing_add_vector_right (hint : PairingIntegrable cρ cσ hχ μ)
    (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v₁ v₂ : V) :
    cρ.coefficientPairing cσ hχ μ ℓ w η (v₁ + v₂) =
      cρ.coefficientPairing cσ hχ μ ℓ w η v₁ + cρ.coefficientPairing cσ hχ μ ℓ w η v₂ := by
  unfold coefficientPairing
  simp_rw [pairingKernel_add_vector_right]
  exact integral_add (hint ℓ w η v₁) (hint ℓ w η v₂)

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientPairing_smul_vector_right (a : ℂ)
    (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V) :
    cρ.coefficientPairing cσ hχ μ ℓ w η (a • v) =
      a * cρ.coefficientPairing cσ hχ μ ℓ w η v := by
  unfold coefficientPairing
  simp_rw [pairingKernel_smul_vector_right]
  exact integral_const_mul _ _

/-- Right invariance of the measure moves a translation of the `ρ`-vector to
the contragredient translation of the `σ`-functional. -/
theorem coefficientPairing_translate_right [μ.IsMulRightInvariant]
    (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V) (h : G) :
    cρ.coefficientPairing cσ hχ μ ℓ w η (ρ h v) =
      cρ.coefficientPairing cσ hχ μ (smoothContragredient σ h⁻¹ ℓ) w η v := by
  unfold coefficientPairing
  simp_rw [pairingKernel_translate_right]
  exact integral_mul_right_eq_self _ (QuotientGroup.mk h)

/-- Left invariance of the measure moves a translation of the `σ`-vector to
the contragredient translation of the `ρ`-functional. -/
theorem coefficientPairing_translate_left [μ.IsMulLeftInvariant]
    (ℓ : SmoothDual σ) (w : W) (η : SmoothDual ρ) (v : V) (h : G) :
    cρ.coefficientPairing cσ hχ μ ℓ (σ h w) η v =
      cρ.coefficientPairing cσ hχ μ ℓ w (smoothContragredient ρ h⁻¹ η) v := by
  unfold coefficientPairing
  rw [← integral_mul_left_eq_self _ (QuotientGroup.mk h : G ⧸ Subgroup.center G)]
  simp_rw [pairingKernel_translate_left]

/-- The pairing with fixed `σ`-vector `w` and `ρ`-functional `η` is the weak form
of an intertwiner `ρ → σ`. -/
theorem exists_intertwiningMap_of_coefficientPairing_right
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hρ : IsSmooth ρ) (hσ : IsAdmissible σ) [μ.IsMulRightInvariant]
    (hint : PairingIntegrable cρ cσ hχ μ) (w : W) (η : SmoothDual ρ) :
    ∃ S : ρ.IntertwiningMap σ, ∀ (ℓ : SmoothDual σ) (v : V),
      smoothDualPairing σ ℓ (S v) = cρ.coefficientPairing cσ hχ μ ℓ w η v := by
  let Λ : V →ₗ[ℂ] SmoothDual σ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun v ℓ => cρ.coefficientPairing cσ hχ μ ℓ w η v)
      (fun v₁ v₂ ℓ => coefficientPairing_add_vector_right hint ℓ w η v₁ v₂)
      (fun a v ℓ => coefficientPairing_smul_vector_right a ℓ w η v)
      (fun v ℓ₁ ℓ₂ => coefficientPairing_add_left hint ℓ₁ ℓ₂ w η v)
      (fun a v ℓ => coefficientPairing_smul_left a ℓ w η v)
  obtain ⟨S, hS⟩ := exists_intertwiningMap_of_weakForm_of_compact_cofinal hcof hρ hσ Λ
    (fun h v ℓ => coefficientPairing_translate_right ℓ w η v h)
  exact ⟨S, fun ℓ v => hS v ℓ⟩

/-- The pairing with fixed `σ`-functional `ℓ` and `ρ`-vector `v` is the weak form
of an intertwiner `σ → ρ`. -/
theorem exists_intertwiningMap_of_coefficientPairing_left
    (hcof : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G, IsCompact (L : Set G) ∧ L ≤ K)
    (hσ : IsSmooth σ) (hρ : IsAdmissible ρ) [μ.IsMulLeftInvariant]
    (hint : PairingIntegrable cρ cσ hχ μ) (ℓ : SmoothDual σ) (v : V) :
    ∃ R : σ.IntertwiningMap ρ, ∀ (η : SmoothDual ρ) (w : W),
      smoothDualPairing ρ η (R w) = cρ.coefficientPairing cσ hχ μ ℓ w η v := by
  let Λ : W →ₗ[ℂ] SmoothDual ρ →ₗ[ℂ] ℂ :=
    LinearMap.mk₂ ℂ (fun w η => cρ.coefficientPairing cσ hχ μ ℓ w η v)
      (fun w₁ w₂ η => coefficientPairing_add_vector_left hint ℓ w₁ w₂ η v)
      (fun a w η => coefficientPairing_smul_vector_left a ℓ w η v)
      (fun w η₁ η₂ => coefficientPairing_add_right hint ℓ w η₁ η₂ v)
      (fun a w η => coefficientPairing_smul_right a ℓ w η v)
  obtain ⟨R, hR⟩ := exists_intertwiningMap_of_weakForm_of_compact_cofinal hcof hσ hρ Λ
    (fun h w η => coefficientPairing_translate_left ℓ w η v h)
  exact ⟨R, fun η w => hR w η⟩

omit [BorelSpace (G ⧸ Subgroup.center G)] in
/-- Positivity: if `η(ρ(g)x) = b(u, σ(g)u)` for an invariant positive form `b`,
then the pairing of `b(u, -)`, `u`, `η`, `x` is `∫ |b(u, σ(g)u)|² dġ`, which is
nonzero for `u ≠ 0`. -/
theorem coefficientPairing_ne_zero [μ.IsOpenPosMeasure] (hσ : IsSmooth σ)
    (hirr : Representation.IsIrreducible σ) (b : InvariantPositiveForm σ)
    {u : W} (hu : u ≠ 0) (hL2 : MemLp (cσ.coefficientNorm (b.rightFunctional u) u) 2 μ)
    (η : SmoothDual ρ) (x : V) (hx : ∀ g : G, η.1 (ρ g x) = b.inner u (σ g u)) :
    cρ.coefficientPairing cσ hχ μ (b.toSmoothDual hσ u) u η x ≠ 0 := by
  have hk : cρ.pairingKernel cσ hχ (b.toSmoothDual hσ u : Module.Dual ℂ W) u η x =
      fun q => (((cσ.coefficientNorm (b.rightFunctional u) u q) ^ 2 : ℝ) : ℂ) := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      change b.inner u (σ g⁻¹ u) * η.1 (ρ g x) = ((‖b.inner u (σ g u)‖ ^ 2 : ℝ) : ℂ)
      have hinv : b.inner u (σ g⁻¹ u) = (starRingEnd ℂ) (b.inner u (σ g u)) := by
        rw [← b.invariant g u (σ g⁻¹ u), Representation.self_inv_apply]
        exact (b.conj_inner_symm _ _).symm
      rw [hinv, hx, Complex.conj_mul', Complex.ofReal_pow]
  have hne : b.rightFunctional u ≠ 0 := by
    intro h
    apply hu
    apply b.definite u
    have h' := congrArg (fun f : Module.Dual ℂ W => f u) h
    simpa using h'
  intro hz
  unfold coefficientPairing at hz
  rw [hk, integral_complex_ofReal, Complex.ofReal_eq_zero] at hz
  exact hu (cσ.eq_zero_of_integral_coefficientNorm_sq_eq_zero hσ hirr _ hne μ hL2 hz)

end UnitaryCentralCharacter

end Langlands
