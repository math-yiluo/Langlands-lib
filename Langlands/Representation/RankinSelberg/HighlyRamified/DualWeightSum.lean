import Langlands.Representation.RankinSelberg.HighlyRamified.DualWeight
import Langlands.Representation.RankinSelberg.HighlyRamified.FourierRow
import Langlands.Representation.RankinSelberg.HighlyRamified.CosetRepresentatives

/-!
# Finite Fourier inversion for the weight of (4.4.18)

The weight `Φ₂` is supported in the compact lattice `ϖ^(-c) O^(m+1)` and is invariant under
translation by `O^(m+1)`. A finite set `T₂` of representatives of `ϖ^(-c) O^(m+1)` modulo
`O^(m+1)` therefore satisfies
`Σ_(z ∈ T₂) Φ₂(z) ∏_j vol(O)[z_(rev j) + v_j ∈ O] = vol(O)^(m+1) Φ₂(-rev v)`,
and the restricted finite Fourier transform `S₂` of `Φ₂` satisfies
`∫ S₂(rev x) ψ(⟨v, x⟩) dx = vol(O)^(m+1) Φ₂(-rev v)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualWeightSumFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualWeightSumValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualWeightSumLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualWeightSumFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance dualWeightSumFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {m : ℕ}

/-- The lattice `O^(m+1)`. -/
def integerLattice (m : ℕ) : AddSubgroup (Fin (m + 1) → F.Carrier) :=
  AddSubgroup.pi Set.univ fun _ => integerAddSubgroup F

theorem mem_integerLattice {z : Fin (m + 1) → F.Carrier} :
    z ∈ integerLattice F m ↔ ∀ i, z i ∈ (ValuativeRel.valuation F.Carrier).integer := by
  simp [integerLattice, AddSubgroup.mem_pi]

theorem isOpen_integerLattice : IsOpen (integerLattice F m : Set (Fin (m + 1) → F.Carrier)) := by
  have : ((integerLattice F m : AddSubgroup _) : Set (Fin (m + 1) → F.Carrier)) =
      Set.pi Set.univ fun _ => ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) := by
    ext z
    simp [mem_integerLattice]
  rw [this]
  exact isOpen_set_pi Set.finite_univ fun _ _ =>
    Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)

theorem isCompact_integer :
    IsCompact ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) := by
  have := localField_t2 F.Carrier
  exact isCompact_iff_compactSpace.mpr
    (inferInstanceAs (CompactSpace (ValuativeRel.valuation F.Carrier).integer))

/-- The lattice `ϖ^(-c) O^(m+1) = {z : ϖ^c z ∈ O^(m+1)}`. -/
def scaledLattice (ϖ : F.Carrier) (c : ℕ) (m : ℕ) : AddSubgroup (Fin (m + 1) → F.Carrier) where
  carrier := {z | ∀ i, ϖ ^ c * z i ∈ (ValuativeRel.valuation F.Carrier).integer}
  add_mem' := fun ha hb i => by
    simpa [mul_add] using add_mem (ha i) (hb i)
  zero_mem' := fun i => by simp
  neg_mem' := fun ha i => by
    simpa [mul_neg] using neg_mem (ha i)

theorem mem_scaledLattice {ϖ : F.Carrier} {c : ℕ} {z : Fin (m + 1) → F.Carrier} :
    z ∈ scaledLattice F ϖ c m ↔
      ∀ i, ϖ ^ c * z i ∈ (ValuativeRel.valuation F.Carrier).integer := Iff.rfl

theorem isCompact_scaledLattice {ϖ : F.Carrier} (hϖ : ϖ ≠ 0) (c : ℕ) :
    IsCompact (scaledLattice F ϖ c m : Set (Fin (m + 1) → F.Carrier)) := by
  have hc : ϖ ^ c ≠ 0 := pow_ne_zero _ hϖ
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin (m + 1) =>
      ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier)) :=
    isCompact_univ_pi fun _ => isCompact_integer F
  have himg := hK.image (f := fun z : Fin (m + 1) → F.Carrier => (ϖ ^ c)⁻¹ • z)
    (continuous_const_smul _)
  convert himg using 1
  ext z
  simp only [SetLike.mem_coe, mem_scaledLattice, Set.mem_image, Set.mem_pi, Set.mem_univ,
    forall_const]
  constructor
  · intro hz
    refine ⟨ϖ ^ c • z, fun i => by simpa using hz i, ?_⟩
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  · rintro ⟨y, hy, rfl⟩ i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    exact hy i

/-- `Φ₂` vanishes off `ϖ^(-c) O^(m+1)`. -/
theorem dualWeight_support {ω : F.Carrierˣ →* ℂˣ} {ϖ : F.Carrier} {c f : ℕ}
    {z : Fin (m + 1) → F.Carrier} (hz : dualWeight ω ϖ c f z ≠ 0) :
    z ∈ scaledLattice F ϖ c m := by
  rw [mem_scaledLattice]
  by_contra hne
  apply hz
  apply unitLastWeight_of_not_cond
  rintro ⟨h1, h2⟩
  apply hne
  intro i
  by_cases hi : i = Fin.last m
  · subst hi; exact h2.2.1
  · exact (h1 i hi).integral

/-- Finite representatives of the support of `Φ₂` modulo `O^(m+1)`. -/
theorem exists_dualWeight_reps (ω : F.Carrierˣ →* ℂˣ) {ϖ : F.Carrier} (hϖ : ϖ ≠ 0) (c f : ℕ) :
    ∃ T : Finset (Fin (m + 1) → F.Carrier),
      (∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t') ∧
      ∀ y, dualWeight ω ϖ c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m := by
  obtain ⟨T, -, hT, hcov⟩ := exists_finset_addCosetReps (scaledLattice F ϖ c m)
    (integerLattice F m) (isCompact_scaledLattice F hϖ c) (isOpen_integerLattice F)
  exact ⟨T, hT, fun y hy => hcov y (dualWeight_support F hy)⟩

open Classical in
/-- The finite inversion sum for `Φ₂`. -/
theorem sum_dualWeight_inversion {ω : F.Carrierˣ →* ℂˣ} {ϖ : F.Carrier} {c f : ℕ}
    (hf : 0 < f) (hω : TrivialOnPrincipalUnits ω f)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer, InPow f (ϖ ^ c * o))
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ y, dualWeight ω ϖ c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m)
    (a : ℂ) (v : Fin (m + 1) → F.Carrier) :
    ∑ z ∈ T, dualWeight ω ϖ c f z * ∏ j, (if z j.rev + v j ∈
        (ValuativeRel.valuation F.Carrier).integer then a else 0) =
      a ^ (m + 1) * dualWeight ω ϖ c f (fun k => -v k.rev) := by
  set y : Fin (m + 1) → F.Carrier := fun k => -v k.rev with hy
  have hprod : ∀ z : Fin (m + 1) → F.Carrier, ∏ j, (if z j.rev + v j ∈
      (ValuativeRel.valuation F.Carrier).integer then a else 0) =
      if z - y ∈ integerLattice F m then a ^ (m + 1) else 0 := by
    intro z
    have hiff : z - y ∈ integerLattice F m ↔
        ∀ j, z j.rev + v j ∈ (ValuativeRel.valuation F.Carrier).integer := by
      rw [mem_integerLattice]
      constructor
      · intro h j
        simpa [hy] using h j.rev
      · intro h k
        simpa [hy] using h k.rev
    by_cases h : ∀ j, z j.rev + v j ∈ (ValuativeRel.valuation F.Carrier).integer
    · simp only [hiff.2 h, ↓reduceIte]
      rw [Finset.prod_congr rfl (g := fun _ => a) fun j _ => by simp only [h j, ↓reduceIte],
        Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · have hn : z - y ∉ integerLattice F m := fun h' => h (hiff.1 h')
      simp only [hn, ↓reduceIte]
      push Not at h
      obtain ⟨j, hj⟩ := h
      exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp only [hj, ↓reduceIte])
  simp_rw [hprod, mul_ite, mul_zero]
  rw [← sum_reps_eq (integerLattice F m) (dualWeight ω ϖ c f)
    (fun z l hl => dualWeight_add hf hω hscale z l ((mem_integerLattice F).1 hl)) T hT hcov y,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> ring

open Classical in
/-- The restricted finite Fourier transform of `Φ₂` inverts to `Φ₂`:
`∫ S₂(rev x) ψ(⟨v, x⟩) dx = vol(O)^(m+1) Φ₂(-rev v)`. -/
theorem integral_dualWeight_fourier (ψ : UnitaryAdditiveCharacter F.Carrier)
    (η : AdditiveHaarMeasure F.Carrier) (hψ : HasIntegerConductorAt F ψ)
    {ω : F.Carrierˣ →* ℂˣ} {ϖ : F.Carrier} {c f : ℕ}
    (hf : 0 < f) (hω : TrivialOnPrincipalUnits ω f)
    (hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer, InPow f (ϖ ^ c * o))
    (T : Finset (Fin (m + 1) → F.Carrier))
    (hT : ∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ integerLattice F m → t = t')
    (hcov : ∀ y, dualWeight ω ϖ c f y ≠ 0 → ∃ t ∈ T, y - t ∈ integerLattice F m)
    (v : Fin (m + 1) → F.Carrier) :
    ∫ x : Matrix (Fin 1) (Fin (m + 1)) F.Carrier,
        (if ∀ k : Fin (m + 1), x 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer then
          ∑ z ∈ T, dualWeight ω ϖ c f z * ψ.complex (∑ k, z k * x 0 k.rev) else 0) *
          ψ.complex (∑ j, v j * x 0 j) ∂RankinSelberg.rectangularMeasure η 1 (m + 1) =
      ((η.measure ((integerAddSubgroup F : AddSubgroup F.Carrier) :
          Set F.Carrier)).toReal : ℂ) ^ (m + 1) *
        dualWeight ω ϖ c f (fun k => -v k.rev) := by
  rw [integral_restrictedFourier_character F ψ η hψ T _ v]
  exact sum_dualWeight_inversion F hf hω hscale T hT hcov _ v

end Langlands.RankinSelberg.HighlyRamified
