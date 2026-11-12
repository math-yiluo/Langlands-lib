import Langlands.Representation.Smooth.RenardSchurStatements
import Langlands.Representation.Hecke.Corner
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Cohomology.SupercuspidalExtCharZero.CosetSum
import Langlands.Topology.RenardGroupFinitenessProof
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Nilpotent.Lemmas

/-! # Compact-open corner countability and positive Hecke elements -/

noncomputable section

universe u

open MeasureTheory MeasureTheory.Measure ComplexConjugate

namespace Langlands.Renard.Smooth

open HarmonicAnalysis (SchwartzBruhat)
open Hecke

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

/-- Conjugation after inversion on the actual Hecke carrier, without a modular factor. -/
def heckeAdjoint (μ : Measure G) (f : HeckeAlgebra μ) : HeckeAlgebra μ :=
  ⟨fun g => conj (f g⁻¹),
    ((show SchwartzBruhat G from f).locallyConstant.comp_continuous continuous_inv).comp conj,
    ((show SchwartzBruhat G from f).hasCompactSupport.comp_homeomorph
      (Homeomorph.inv G)).comp_left (map_zero conj)⟩

omit [BorelSpace G] in
@[simp] theorem heckeAdjoint_apply (μ : Measure G) (f : HeckeAlgebra μ) (g : G) :
    heckeAdjoint μ f g = conj (f g⁻¹) := rfl

omit [BorelSpace G] in
@[simp] theorem heckeAdjoint_involutive (μ : Measure G) (f : HeckeAlgebra μ) :
    heckeAdjoint μ (heckeAdjoint μ f) = f := by
  ext g
  simp

/-- Left-Haar substitution alone reverses convolution under this involution. -/
theorem heckeAdjoint_mul (μ : Measure G) [μ.IsHaarMeasure] (f g : HeckeAlgebra μ) :
    heckeAdjoint μ (f * g) = heckeAdjoint μ g * heckeAdjoint μ f := by
  ext x
  change conj (∫ y, f y * g (y⁻¹ * x⁻¹) ∂μ) =
    ∫ y, conj (g y⁻¹) * conj (f (y⁻¹ * x)⁻¹) ∂μ
  rw [← integral_conj]
  rw [← integral_mul_left_eq_self (fun y => conj (f y * g (y⁻¹ * x⁻¹))) x⁻¹]
  congr 1
  ext y
  simp only [mul_inv_rev, inv_inv, mul_assoc, mul_inv_cancel, mul_one, map_mul]
  exact mul_comm _ _

/-- The positive self-product of a nonzero test function does not vanish. -/
theorem heckeAdjoint_mul_self_ne_zero (μ : Measure G) [μ.IsHaarMeasure]
    (f : HeckeAlgebra μ) (hf : f ≠ 0) : heckeAdjoint μ f * f ≠ 0 := by
  let φ : G → ℝ := fun y => Complex.normSq (f y⁻¹)
  have hc : Continuous φ := Complex.continuous_normSq.comp
    ((show SchwartzBruhat G from f).continuous.comp continuous_inv)
  have hs : HasCompactSupport φ :=
    ((show SchwartzBruhat G from f).hasCompactSupport.comp_homeomorph
      (Homeomorph.inv G)).comp_left (by simp)
  have hnonempty : (Function.support φ).Nonempty := by
    have hex : ∃ y, f y ≠ 0 := by
      by_contra! h
      exact hf (HeckeAlgebra.ext μ h)
    obtain ⟨y, hy⟩ := hex
    exact ⟨y⁻¹, by simpa [φ] using hy⟩
  have hopen : IsOpen (Function.support φ) := hc.isOpen_support
  have hpos : 0 < ∫ y, φ y ∂μ :=
    (integral_pos_iff_support_of_nonneg (fun y => Complex.normSq_nonneg _)
      (hc.integrable_of_hasCompactSupport hs)).2
      (hopen.measure_pos μ hnonempty)
  intro hzero
  have h := congrArg (fun q : HeckeAlgebra μ => (q 1).re) hzero
  have heq : ((heckeAdjoint μ f * f) 1).re = ∫ y, φ y ∂μ := by
    change (∫ y, conj (f y⁻¹) * f (y⁻¹ * 1) ∂μ).re = _
    simp only [mul_one, ← Complex.normSq_eq_conj_mul_self]
    change (∫ y, (φ y : ℂ) ∂μ).re = _
    rw [integral_complex_ofReal]
    rfl
  rw [heq] at h
  exact (ne_of_gt hpos) h

/-- The same inversion-conjugation preserves every compact-open corner. -/
def heckeCornerAdjoint (μ : Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : HeckeAlgebra.Corner μ K hK) : HeckeAlgebra.Corner μ K hK :=
  ⟨heckeAdjoint μ f.val, by
    constructor
    · intro k x
      change conj (f ((k : G) * x)⁻¹) = conj (f x⁻¹)
      simp only [mul_inv_rev]
      exact congrArg conj (HeckeAlgebra.Corner.rightInvariant μ K hK f k⁻¹ x⁻¹)
    · intro k x
      change conj (f (x * (k : G))⁻¹) = conj (f x⁻¹)
      simp only [mul_inv_rev]
      exact congrArg conj (HeckeAlgebra.Corner.leftInvariant μ K hK f k⁻¹ x⁻¹)⟩

/-- The corner involution reverses multiplication. -/
theorem heckeCornerAdjoint_mul (μ : Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f g : HeckeAlgebra.Corner μ K hK) :
    heckeCornerAdjoint μ K hK (f * g) =
      heckeCornerAdjoint μ K hK g * heckeCornerAdjoint μ K hK f :=
  Subtype.ext (heckeAdjoint_mul μ f.val g.val)

@[simp] theorem heckeCornerAdjoint_involutive (μ : Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : HeckeAlgebra.Corner μ K hK) :
    heckeCornerAdjoint μ K hK (heckeCornerAdjoint μ K hK f) = f :=
  Subtype.ext (heckeAdjoint_involutive μ f.val)

/-- Nonzero corner elements have nonzero positive self-product. -/
theorem heckeCornerAdjoint_mul_self_ne_zero (μ : Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : HeckeAlgebra.Corner μ K hK) (hf : f ≠ 0) :
    heckeCornerAdjoint μ K hK f * f ≠ 0 := by
  intro h
  exact heckeAdjoint_mul_self_ne_zero μ f.val
    (fun hzero => hf (Subtype.ext hzero)) (congrArg Subtype.val h)

/-- Repeated squaring makes every nonzero self-adjoint corner element nonnilpotent. -/
theorem heckeCorner_selfAdjoint_not_isNilpotent (μ : Measure G) [μ.IsHaarMeasure]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : HeckeAlgebra.Corner μ K hK) (hself : heckeCornerAdjoint μ K hK f = f)
    (hf : f ≠ 0) : ¬ IsNilpotent f := by
  have hp (n : ℕ) : heckeCornerAdjoint μ K hK (f ^ (2 ^ n)) = f ^ (2 ^ n) ∧
      f ^ (2 ^ n) ≠ 0 := by
    induction n with
    | zero => simpa using And.intro hself hf
    | succ n ih =>
      rw [show 2 ^ (n + 1) = 2 ^ n * 2 from pow_succ _ _, pow_mul, pow_two]
      constructor
      · rw [heckeCornerAdjoint_mul, ih.1]
      · simpa only [ih.1] using
          heckeCornerAdjoint_mul_self_ne_zero μ K hK (f ^ (2 ^ n)) ih.2
  rintro ⟨n, hn⟩
  exact (hp n).2 (pow_eq_zero_of_le n.lt_two_pow_self.le hn)

/-- A compact-open corner of a sigma-compact group has at most countable dimension. -/
theorem heckeCorner_rank_le_aleph0 [SigmaCompactSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) :
    Module.rank ℂ (HeckeAlgebra.Corner μ K hK) ≤ Cardinal.aleph0 := by
  classical
  let : DiscreteTopology (G ⧸ K.toSubgroup) := QuotientGroup.discreteTopology K.isOpen
  let : LindelofSpace (G ⧸ K.toSubgroup) := Quotient.lindelofSpace
  let : Countable (G ⧸ K.toSubgroup) := countable_of_Lindelof_of_discrete
  let F : HeckeAlgebra.Corner μ K hK →ₗ[ℂ] (G ⧸ K.toSubgroup) →₀ ℂ :=
    { toFun := fun f => Finsupp.ofSupportFinite (fun q => f q.out)
        (Cohomology.SupercuspidalExtCharZero.hasFiniteSupport_out_of_hasCompactSupport
          K.isOpen (show SchwartzBruhat G from f.val).hasCompactSupport)
      map_add' := fun f g => by ext q; rfl
      map_smul' := fun c f => by ext q; rfl }
  have hF : Function.Injective F := by
    intro f g h
    apply Subtype.ext
    apply HeckeAlgebra.ext
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K.toSubgroup x
    have he := congrArg (fun z : (G ⧸ K.toSubgroup) →₀ ℂ => z (QuotientGroup.mk x)) h
    change f (QuotientGroup.mk x : G ⧸ K.toSubgroup).out =
      g (QuotientGroup.mk x : G ⧸ K.toSubgroup).out at he
    rw [hk, HeckeAlgebra.Corner.rightInvariant μ K hK f k x,
      HeckeAlgebra.Corner.rightInvariant μ K hK g k x] at he
    exact he
  calc
    Module.rank ℂ (HeckeAlgebra.Corner μ K hK) ≤
        Module.rank ℂ ((G ⧸ K.toSubgroup) →₀ ℂ) := LinearMap.rank_le_of_injective F hF
    _ ≤ Cardinal.aleph0 := by
      rw [rank_finsupp_self]
      exact Cardinal.lift_le_aleph0.mpr Cardinal.mk_le_aleph0

end Langlands.Renard.Smooth
