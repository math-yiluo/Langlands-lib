import Langlands.Representation.Unitary.SquareIntegrableStatement
import Langlands.Representation.MatrixCoefficient.HermitianProduct
import Langlands.Representation.MatrixCoefficient.NormRegularityProof
import Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Unitarizability from square-integrable coefficients on a central quotient

A nonzero smooth functional is obtained from compact-open smooth duality. The
invariant positive form integrates the conjugate-first product of its matrix
coefficients over the actual quotient by the center.
-/

noncomputable section

namespace Langlands

open MeasureTheory

universe uG uV

section Separation

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compact-open smooth duality supplies a smooth functional detecting any
nonzero vector of a smooth representation. -/
theorem exists_smoothDual_apply_ne_zero_of_compact_cofinal
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) {v : V} (hv : v ≠ 0) :
    ∃ ℓ : SmoothDual ρ, ℓ.1 v ≠ 0 := by
  by_contra hn
  push Not at hn
  apply hv
  apply smoothBidual_injective_of_compact_cofinal hcofinal ρ hρ
  apply Subtype.ext
  apply LinearMap.ext
  intro ℓ
  change ℓ.1 v = ℓ.1 0
  simpa only [map_zero] using hn ℓ

/-- An irreducible smooth representation has a nonzero smooth functional. -/
theorem exists_nonzero_smoothDual_of_irreducible_compact_cofinal
    (hcofinal : ∀ K : OpenSubgroup G, ∃ L : OpenSubgroup G,
      IsCompact (L : Set G) ∧ L ≤ K)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hirr : Representation.IsIrreducible ρ) :
    ∃ ℓ : SmoothDual ρ, ℓ.1 ≠ 0 := by
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  obtain ⟨ℓ, hℓ⟩ :=
    exists_smoothDual_apply_ne_zero_of_compact_cofinal hcofinal ρ hρ hv
  refine ⟨ℓ, fun hz => hℓ ?_⟩
  rw [hz, LinearMap.zero_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The vectors whose coefficient against an algebraic functional vanishes
identically form an invariant subrepresentation. -/
def matrixCoefficientKernel (ρ : Representation ℂ G V) (ℓ : Module.Dual ℂ V) :
    Subrepresentation ρ where
  toSubmodule :=
    { carrier := {v | ∀ g : G, matrixCoefficient ρ ℓ v g = 0}
      zero_mem' := by intro g; simp [matrixCoefficient]
      add_mem' := by
        intro v w hv hw g
        calc
          matrixCoefficient ρ ℓ (v + w) g =
              matrixCoefficient ρ ℓ v g + matrixCoefficient ρ ℓ w g := by
            simp [matrixCoefficient]
          _ = 0 := by rw [hv g, hw g, add_zero]
      smul_mem' := by
        intro a v hv g
        calc
          matrixCoefficient ρ ℓ (a • v) g = a * matrixCoefficient ρ ℓ v g := by
            simp [matrixCoefficient]
          _ = 0 := by rw [hv g, mul_zero] }
  apply_mem_toSubmodule := by
    intro h v hv g
    change ℓ (ρ g (ρ h v)) = 0
    change ℓ ((ρ g * ρ h) v) = 0
    rw [← map_mul]
    exact hv (g * h)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- In an irreducible representation, the coefficients of one nonzero
functional detect every nonzero vector. -/
theorem eq_zero_of_matrixCoefficient_vanishes
    (ρ : Representation ℂ G V) (hirr : Representation.IsIrreducible ρ)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0) {v : V}
    (hv : ∀ g : G, matrixCoefficient ρ ℓ v g = 0) : v = 0 := by
  let W := matrixCoefficientKernel ρ ℓ
  have hW : W ≠ ⊤ := by
    intro ht
    apply hℓ
    apply LinearMap.ext
    intro w
    have hw : w ∈ W := ht.symm ▸ (show w ∈ (⊤ : Subrepresentation ρ) from trivial)
    have he := hw (1 : G)
    simpa [matrixCoefficient] using he
  have hb : W = ⊥ := (eq_bot_or_eq_top W).resolve_right hW
  have hvW : v ∈ W := hv
  rw [hb] at hvW
  exact hvW

end Separation

namespace UnitaryCentralCharacter

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {ρ : Representation ℂ G V} (c : UnitaryCentralCharacter ρ)
variable [MeasurableSpace (G ⧸ Subgroup.center G)]

/-- A zero integral of a square-integrable squared coefficient norm forces the
vector to vanish, for a measure positive on nonempty open sets. -/
theorem eq_zero_of_integral_coefficientNorm_sq_eq_zero
    (hρ : IsSmooth ρ) (hirr : Representation.IsIrreducible ρ)
    (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0)
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsOpenPosMeasure]
    {v : V} (hv : MemLp (c.coefficientNorm ℓ v) 2 μ)
    (hz : ∫ q, (c.coefficientNorm ℓ v q) ^ 2 ∂μ = 0) : v = 0 := by
  have hae : (fun q => (c.coefficientNorm ℓ v q) ^ 2) =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hv.integrable_sq).mp hz
  have heq : (fun q => (c.coefficientNorm ℓ v q) ^ 2) = 0 :=
    (((c.continuous_coefficientNorm ℓ v (hρ v)).pow 2).ae_eq_iff_eq μ
      continuous_const).mp hae
  apply eq_zero_of_matrixCoefficient_vanishes ρ hirr ℓ hℓ
  intro g
  apply norm_eq_zero.mp
  have hg := congrFun heq (QuotientGroup.mk g)
  change ‖matrixCoefficient ρ ℓ v g‖ ^ 2 = 0 at hg
  exact sq_eq_zero_iff.mp hg

variable [BorelSpace (G ⧸ Subgroup.center G)]

/-- Two square-integrable coefficient norms make the coefficient product
integrable. -/
theorem integrable_coefficientProduct (ℓ : Module.Dual ℂ V)
    (μ : Measure (G ⧸ Subgroup.center G)) {u v : V}
    (hu : IsSmoothVector ρ u) (hv : IsSmoothVector ρ v)
    (hu2 : MemLp (c.coefficientNorm ℓ u) 2 μ)
    (hv2 : MemLp (c.coefficientNorm ℓ v) 2 μ) :
    Integrable (c.coefficientProduct ℓ u v) μ :=
  (hu2.integrable_mul hv2).mono'
    (c.aestronglyMeasurable_coefficientProduct ℓ u v hu hv μ)
    (Filter.Eventually.of_forall fun q => (c.norm_coefficientProduct ℓ u v q).le)

/-- The integral of the conjugate-first coefficient product. -/
def coefficientProductIntegral (ℓ : Module.Dual ℂ V)
    (μ : Measure (G ⧸ Subgroup.center G)) (u v : V) : ℂ :=
  ∫ q, c.coefficientProduct ℓ u v q ∂μ

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientProductIntegral_conj (ℓ : Module.Dual ℂ V)
    (μ : Measure (G ⧸ Subgroup.center G)) (u v : V) :
    (starRingEnd ℂ) (c.coefficientProductIntegral ℓ μ v u) =
      c.coefficientProductIntegral ℓ μ u v := by
  rw [coefficientProductIntegral, ← integral_conj]
  simp_rw [c.coefficientProduct_conj]
  rfl

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientProductIntegral_self (ℓ : Module.Dual ℂ V)
    (μ : Measure (G ⧸ Subgroup.center G)) (v : V) :
    c.coefficientProductIntegral ℓ μ v v =
      ((∫ q, (c.coefficientNorm ℓ v q) ^ 2 ∂μ : ℝ) : ℂ) := by
  rw [coefficientProductIntegral]
  simp_rw [c.coefficientProduct_self]
  exact integral_ofReal

theorem coefficientProductIntegral_add_left (hρ : IsSmooth ρ)
    (ℓ : Module.Dual ℂ V) (μ : Measure (G ⧸ Subgroup.center G))
    (hL2 : ∀ v, MemLp (c.coefficientNorm ℓ v) 2 μ) (u₁ u₂ v : V) :
    c.coefficientProductIntegral ℓ μ (u₁ + u₂) v =
      c.coefficientProductIntegral ℓ μ u₁ v +
        c.coefficientProductIntegral ℓ μ u₂ v := by
  simp_rw [coefficientProductIntegral, c.coefficientProduct_add_left]
  exact integral_add
    (c.integrable_coefficientProduct ℓ μ (hρ u₁) (hρ v) (hL2 u₁) (hL2 v))
    (c.integrable_coefficientProduct ℓ μ (hρ u₂) (hρ v) (hL2 u₂) (hL2 v))

omit [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)] in
theorem coefficientProductIntegral_smul_left (ℓ : Module.Dual ℂ V)
    (μ : Measure (G ⧸ Subgroup.center G)) (a : ℂ) (u v : V) :
    c.coefficientProductIntegral ℓ μ (a • u) v =
      (starRingEnd ℂ) a * c.coefficientProductIntegral ℓ μ u v := by
  simp_rw [coefficientProductIntegral, c.coefficientProduct_smul_left]
  exact integral_const_mul _ _

theorem coefficientProductIntegral_translate (ℓ : Module.Dual ℂ V)
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsMulRightInvariant]
    (g : G) (u v : V) :
    c.coefficientProductIntegral ℓ μ (ρ g u) (ρ g v) =
      c.coefficientProductIntegral ℓ μ u v := by
  simp_rw [coefficientProductIntegral, c.coefficientProduct_translate]
  exact integral_mul_right_eq_self (c.coefficientProduct ℓ u v) (QuotientGroup.mk g)

/-- The actual invariant positive form given by integrating coefficient
products of a nonzero functional over the central quotient. -/
def coefficientProductForm (hρ : IsSmooth ρ)
    (hirr : Representation.IsIrreducible ρ) (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0)
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsOpenPosMeasure]
    [μ.IsMulRightInvariant] (hL2 : ∀ v, MemLp (c.coefficientNorm ℓ v) 2 μ) :
    InvariantPositiveForm ρ where
  inner u v := c.coefficientProductIntegral ℓ μ u v
  conj_inner_symm u v := c.coefficientProductIntegral_conj ℓ μ u v
  re_inner_nonneg v := by
    change 0 ≤ (c.coefficientProductIntegral ℓ μ v v).re
    rw [c.coefficientProductIntegral_self, Complex.ofReal_re]
    exact integral_nonneg fun q => sq_nonneg _
  add_left u₁ u₂ v := c.coefficientProductIntegral_add_left hρ ℓ μ hL2 u₁ u₂ v
  smul_left u v a := c.coefficientProductIntegral_smul_left ℓ μ a u v
  definite v hv := by
    change c.coefficientProductIntegral ℓ μ v v = 0 at hv
    rw [c.coefficientProductIntegral_self, Complex.ofReal_eq_zero] at hv
    exact c.eq_zero_of_integral_coefficientNorm_sq_eq_zero hρ hirr ℓ hℓ μ (hL2 v) hv
  invariant g u v := c.coefficientProductIntegral_translate ℓ μ g u v

@[simp]
theorem coefficientProductForm_inner (hρ : IsSmooth ρ)
    (hirr : Representation.IsIrreducible ρ) (ℓ : Module.Dual ℂ V) (hℓ : ℓ ≠ 0)
    (μ : Measure (G ⧸ Subgroup.center G)) [μ.IsOpenPosMeasure]
    [μ.IsMulRightInvariant] (hL2 : ∀ v, MemLp (c.coefficientNorm ℓ v) 2 μ)
    (u v : V) :
    (c.coefficientProductForm hρ hirr ℓ hℓ μ hL2).inner u v =
      ∫ q, c.coefficientProduct ℓ u v q ∂μ := rfl

end UnitaryCentralCharacter

/-- An irreducible representation with square-integrable coefficients modulo the
center is unitarizable when compact open subgroups are cofinal and the quotient
Haar measure is right invariant. -/
theorem squareIntegrableUnimodularUnitarity :
    SquareIntegrableUnimodularUnitarityStatement.{uG, uV} := by
  intro G _ _ _ _ _ _ hcofinal V _ _ ρ _ _ μ _ _ hirr hsq
  obtain ⟨hadm, c, hL2⟩ := hsq
  obtain ⟨ℓ, hℓ⟩ :=
    exists_nonzero_smoothDual_of_irreducible_compact_cofinal hcofinal ρ hadm.1 hirr
  exact ⟨c.coefficientProductForm hadm.1 hirr ℓ.1 hℓ μ (hL2 ℓ)⟩

end Langlands
