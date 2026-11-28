import Langlands.Representation.Compact.CompactGroupSmoothRepresentationProof
import Mathlib.RepresentationTheory.Character
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Algebra.Group.Compact

/-! # Character pairings for smooth representations of compact groups -/

noncomputable section

namespace Langlands.Representation.Character

open Function MeasureTheory Set

universe u v w

variable {K : Type u} [Group K] [TopologicalSpace K] [MeasurableSpace K]
  {X : Type v} [AddCommGroup X] [Module ℂ X]
  {Y : Type w} [AddCommGroup Y] [Module ℂ Y]

/-- Integrating the trace pairing of two finite-dimensional smooth
representations of a compact group counts intertwining maps, up to Haar volume. -/
def CompactCharacterInnerProductStatement [IsTopologicalGroup K] [CompactSpace K] [BorelSpace K]
    [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y] (μ : Measure K) [μ.IsHaarMeasure]
    (ρ : Representation ℂ K X) (σ : Representation ℂ K Y) : Prop :=
  IsSmooth ρ → IsSmooth σ →
  (∫ k, σ.character k * ρ.character k⁻¹ ∂μ) =
    (μ.real univ : ℂ) * (Module.finrank ℂ (Representation.IntertwiningMap ρ σ) : ℂ)

variable [CompactSpace K]

private theorem integral_surjective_finite_group [MeasurableMul K] {Q : Type*} [Group Q] [Fintype Q]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] (q : K →* Q)
    (hq : Surjective q) (hm : Measurable q) (μ : Measure K) [μ.IsHaarMeasure] (f : Q → ℂ) :
    (∫ k, f (q k) ∂μ) = (μ.real univ : ℂ) * ((Fintype.card Q : ℂ)⁻¹ * ∑ g, f g) := by
  let ν := μ.map q
  let : IsFiniteMeasure ν := Measure.isFiniteMeasure_map μ q
  let : ν.IsMulLeftInvariant := isMulLeftInvariant_map q.toMulHom hm hq
  have hmass (g : Q) : ν.real {g} = ν.real {1} := by
    rw [measureReal_def, measureReal_def]
    congr 1
    calc
      ν {g} = (ν.map (g * ·)) {g} := congrArg (fun m : Measure Q => m {g})
        (map_mul_left_eq_self ν g).symm
      _ = ν {1} := by
        rw [Measure.map_apply (measurable_const_mul g) (measurableSet_singleton g)]
        congr 1
        ext x
        simp
  have hconst (h : Q → ℂ) : (∫ k, h (q k) ∂μ) = (ν.real {1} : ℂ) * ∑ g, h g := by
    rw [← integral_map hm.aemeasurable (Integrable.of_finite (f := h) (μ := ν)).aestronglyMeasurable,
      integral_fintype (Integrable.of_finite (f := h) (μ := ν))]
    simp [hmass, Complex.real_smul, Finset.mul_sum]
  have hvol : (ν.real {1} : ℂ) * (Fintype.card Q : ℂ) = (μ.real univ : ℂ) := by
    simpa using (hconst (fun _ => 1)).symm
  have hn : (Fintype.card Q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hconst f, ← hvol]
  field_simp

variable [IsTopologicalGroup K] [BorelSpace K] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]

theorem compactCharacterInnerProduct (μ : Measure K) [μ.IsHaarMeasure]
    (ρ : Representation ℂ K X) (σ : Representation ℂ K Y) :
    CompactCharacterInnerProductStatement μ ρ σ := by
  intro hρ hσ
  obtain ⟨Nρ, hNρ, hρ₀⟩ := Renard.CompactRepresentation.exists_openNormal_trivial_of_finiteDimensional ρ hρ
  obtain ⟨Nσ, hNσ, hσ₀⟩ := Renard.CompactRepresentation.exists_openNormal_trivial_of_finiteDimensional σ hσ
  let : Nρ.toSubgroup.Normal := hNρ
  let : Nσ.toSubgroup.Normal := hNσ
  let N := Nρ ⊓ Nσ
  let : N.toSubgroup.Normal := inferInstanceAs (Nρ.toSubgroup ⊓ Nσ.toSubgroup).Normal
  let Q := K ⧸ N.toSubgroup
  let q := QuotientGroup.mk' N.toSubgroup
  have hq : Surjective q := QuotientGroup.mk'_surjective _
  let : Finite Q := Subgroup.quotient_finite_of_isOpen _ N.isOpen
  let : Fintype Q := Fintype.ofFinite Q
  let : DiscreteTopology Q := QuotientGroup.discreteTopology_iff.mpr N.isOpen
  let : MeasurableSpace Q := borel Q
  let : BorelSpace Q := ⟨rfl⟩
  have hm : Measurable q := QuotientGroup.continuous_mk.measurable
  let ρQ : Representation ℂ Q X := QuotientGroup.lift N.toSubgroup ρ
    (fun g hg => LinearMap.ext fun x => hρ₀ g hg.1 x)
  let σQ : Representation ℂ Q Y := QuotientGroup.lift N.toSubgroup σ
    (fun g hg => LinearMap.ext fun x => hσ₀ g hg.2 x)
  let e : Representation.IntertwiningMap ρ σ ≃ₗ[ℂ] Representation.IntertwiningMap ρQ σQ :=
    { toFun := fun T =>
        { toLinearMap := T.toLinearMap
          isIntertwining' := fun g => by
            obtain ⟨k, rfl⟩ := hq g
            exact T.isIntertwining' k }
      invFun := fun T =>
        { toLinearMap := T.toLinearMap
          isIntertwining' := fun k => T.isIntertwining' (q k) }
      left_inv := fun T => Representation.IntertwiningMap.ext rfl
      right_inv := fun T => Representation.IntertwiningMap.ext rfl
      map_add' := fun _ _ => Representation.IntertwiningMap.ext rfl
      map_smul' := fun _ _ => Representation.IntertwiningMap.ext rfl }
  have hn : (Nat.card Q : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let : Invertible (Nat.card Q : ℂ) := invertibleOfNonzero hn
  have h := integral_surjective_finite_group q hq hm μ (fun g => σQ.character g * ρQ.character g⁻¹)
  simp_rw [← map_inv q] at h
  change (∫ k, σ.character k * ρ.character k⁻¹ ∂μ) = _ at h
  rw [← Nat.card_eq_fintype_card, Representation.card_inv_mul_sum_char_mul_char_eq_finrank,
    ← e.finrank_eq] at h
  exact h

/-- A compact character pairing is nonzero exactly when there is a nonzero
intertwining map between the two representations. -/
theorem compactCharacterInnerProduct_ne_zero_iff (μ : Measure K) [μ.IsHaarMeasure]
    (ρ : Representation ℂ K X) (σ : Representation ℂ K Y) (hρ : IsSmooth ρ) (hσ : IsSmooth σ) :
    (∫ k, σ.character k * ρ.character k⁻¹ ∂μ) ≠ 0 ↔
      ∃ T : Representation.IntertwiningMap ρ σ, T ≠ 0 := by
  have hvol : 0 < μ.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (isOpen_univ.measure_pos μ univ_nonempty).ne' isCompact_univ.measure_lt_top.ne
  rw [show (∫ k, σ.character k * ρ.character k⁻¹ ∂μ) = _ from compactCharacterInnerProduct μ ρ σ hρ hσ,
    mul_ne_zero_iff, and_iff_right (Complex.ofReal_ne_zero.mpr hvol.ne'), Nat.cast_ne_zero,
    ← Nat.pos_iff_ne_zero, Module.finrank_pos_iff, nontrivial_iff_exists_ne (0 : Representation.IntertwiningMap ρ σ)]

end Langlands.Representation.Character
