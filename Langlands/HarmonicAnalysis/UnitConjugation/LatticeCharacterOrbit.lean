import Langlands.HarmonicAnalysis.Bicharacter.SelfDual
import Langlands.HarmonicAnalysis.UnitConjugation.CompactExponentialCharacter
import Mathlib.Algebra.Group.AddChar
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Additive character orbits of compact unit groups -/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation

open Set Function

variable {R : Type*} [Ring R] [TopologicalSpace R]
  {e : R → R → ℂ} (he : IsSelfDualBicharacter e) (L : AddSubgroup R)

/-- The additive character of `L` associated to an ambient frequency. -/
def latticeAddChar (z : R) : AddChar L ℂ where
  toFun x := e x.val z
  map_zero_eq_one' := he.map_zero_left z
  map_add_eq_mul' x y := he.map_add_left x.val y.val z

@[simp] theorem latticeAddChar_apply (z : R) (x : L) :
    latticeAddChar he L z x = e x.val z := rfl

theorem isLocallyConstant_latticeAddChar (z : R) :
    IsLocallyConstant (latticeAddChar he L z : L → ℂ) :=
  he.isLocallyConstant.comp_continuous (continuous_subtype_val.prodMk continuous_const)

theorem latticeAddChar_eq_iff (a b : R) :
    latticeAddChar he L a = latticeAddChar he L b ↔ a - b ∈ he.annihilator (L : Set R) := by
  rw [he.mem_annihilator]
  constructor
  · intro h x hx
    have hval := congrArg (fun f : AddChar L ℂ => f ⟨x, hx⟩) h
    change e x a = e x b at hval
    rw [sub_eq_add_neg, he.map_add_right, hval, ← he.map_add_right, add_neg_cancel, he.map_zero_right]
  · intro h
    apply AddChar.ext
    intro x
    have hab := h x.val x.property
    rw [sub_eq_add_neg, he.map_add_right] at hab
    apply mul_right_cancel₀ (he.ne_zero _ (-b))
    change e x.val a * e x.val (-b) = e x.val b * e x.val (-b)
    rw [hab, ← he.map_add_right, add_neg_cancel, he.map_zero_right]

variable [IsTopologicalRing R]

/-- The additive orbit on `L` obtained by conjugating a frequency and then
restricting its character. -/
def latticeCharacterOrbit (K : Subgroup Rˣ) (z : R) : Set (AddChar L ℂ) :=
  range fun u : K => latticeAddChar he L (conjugationHomeomorph u.val z)

/-- The orbit from a compact group is finite, and its sum is invariant under
the same group when the lattice and bicharacter are preserved. -/
def LatticeCharacterOrbitStatement (K : Subgroup Rˣ) (z : R) : Prop :=
  IsCompact (L : Set R) → IsCompact (K : Set Rˣ) →
  (∀ u ∈ K, ∀ x ∈ L, conjugationHomeomorph u x ∈ L) →
  (∀ u ∈ K, ∀ x y, e (conjugationHomeomorph u x) (conjugationHomeomorph u y) = e x y) →
  ∃ J : Finset (AddChar L ℂ), (J : Set (AddChar L ℂ)) = latticeCharacterOrbit he L K z ∧
    J.Nonempty ∧ (∀ χ ∈ J, IsLocallyConstant (χ : L → ℂ)) ∧
    ∀ u ∈ K, ∀ x y : L, y.val = conjugationHomeomorph u x.val →
      ∑ χ ∈ J, χ y = ∑ χ ∈ J, χ x

private theorem latticeCharacterOrbit_finite (K : Subgroup Rˣ) (z : R)
    (hL : IsCompact (L : Set R)) (hK : IsCompact (K : Set Rˣ)) :
    (latticeCharacterOrbit he L K z).Finite := by
  let D := he.annihilator (L : Set R)
  let q : R →+ R ⧸ D := QuotientAddGroup.mk' D
  let : DiscreteTopology (R ⧸ D) :=
    QuotientAddGroup.discreteTopology_iff.mpr (he.isOpen_annihilator hL)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let f (k : K) := q (conjugationHomeomorph k.val z)
  have hf : Continuous f := QuotientAddGroup.continuous_mk.comp (by
    change Continuous fun k : K => (k.val : R) * z * (k.val⁻¹ : Rˣ).val
    exact ((Units.continuous_val.comp continuous_subtype_val).mul continuous_const).mul
      (Units.continuous_val.comp (continuous_inv.comp continuous_subtype_val)))
  have hfin := (isCompact_range hf).finite_of_discrete
  let s := (QuotientAddGroup.mk'_surjective D).hasRightInverse.choose
  have hs : RightInverse s q := (QuotientAddGroup.mk'_surjective D).hasRightInverse.choose_spec
  apply (hfin.image (fun a => latticeAddChar he L (s a))).subset
  rintro χ ⟨k, rfl⟩
  refine ⟨f k, mem_range_self k, (latticeAddChar_eq_iff he L _ _).2 ?_⟩
  apply QuotientAddGroup.eq_iff_sub_mem.mp
  exact hs (f k)

theorem latticeCharacterOrbit_sum (K : Subgroup Rˣ) (z : R) :
    LatticeCharacterOrbitStatement he L K z := by
  classical
  intro hL hK hLot hPair
  let J := (latticeCharacterOrbit_finite he L K z hL hK).toFinset
  have hJ (χ : AddChar L ℂ) : χ ∈ J ↔ ∃ u : K,
      latticeAddChar he L (conjugationHomeomorph u.val z) = χ :=
    (latticeCharacterOrbit_finite he L K z hL hK).mem_toFinset
  refine ⟨J, Set.Finite.coe_toFinset _, ?_, ?_, ?_⟩
  · exact ⟨_, (hJ _).2 ⟨1, rfl⟩⟩
  · intro χ hχ
    obtain ⟨k, rfl⟩ := (hJ χ).1 hχ
    exact isLocallyConstant_latticeAddChar he L _
  intro u hu x y hy
  let a : L →+ L :=
    { toFun := fun w => ⟨conjugationHomeomorph u w.val, hLot u hu _ w.property⟩
      map_zero' := Subtype.ext (by simp)
      map_add' := fun w v => Subtype.ext (by simp [mul_add, add_mul]) }
  have ha : Surjective a := by
    intro v
    let w : L := ⟨conjugationHomeomorph u⁻¹ v.val, hLot u⁻¹ (K.inv_mem hu) _ v.property⟩
    refine ⟨w, Subtype.ext ?_⟩
    change conjugationHomeomorph u (conjugationHomeomorph u⁻¹ v.val) = v.val
    rw [← conjugationHomeomorph_mul, mul_inv_cancel, conjugationHomeomorph_one]
  let p : AddChar L ℂ ↪ AddChar L ℂ :=
    ⟨fun χ => χ.compAddMonoidHom a, AddChar.compAddMonoidHom_injective_left a ha⟩
  have hp : J.map p = J := by
    apply Finset.eq_of_subset_of_card_le _ (Finset.card_map p).ge
    intro θ hθ
    obtain ⟨χ, hχ, rfl⟩ := Finset.mem_map.mp hθ
    obtain ⟨k, rfl⟩ := (hJ χ).1 hχ
    let b : K := ⟨u⁻¹ * k.val, K.mul_mem (K.inv_mem hu) k.property⟩
    refine (hJ _).2 ⟨b, AddChar.ext _ _ fun w => ?_⟩
    have h := hPair u hu w.val (conjugationHomeomorph b.val z)
    have hc : conjugationHomeomorph u (conjugationHomeomorph b.val z) =
        conjugationHomeomorph k.val z := by
      rw [← conjugationHomeomorph_mul, show u * b.val = k.val from mul_inv_cancel_left u k.val]
    rw [hc] at h
    exact h.symm
  have hax : a x = y := Subtype.ext hy.symm
  calc
    _ = ∑ χ ∈ J, p χ x := by
      apply Finset.sum_congr rfl
      intro χ _
      change χ y = χ (a x)
      rw [hax]
    _ = ∑ χ ∈ J.map p, χ x := (Finset.sum_map J p (fun χ : AddChar L ℂ => χ x)).symm
    _ = _ := by rw [hp]

section NormCongruence

open Metric

universe u v

local notation "B(" R "," h ")" => OpenAddSubgroup.toAddSubgroup
  (IsUltrametricDist.closedBall_openAddSubgroup R h)

/-- Given exponential product straightening, an orbit under the enlarged
congruence group defines a smooth character sum on the smaller unit group. -/
def NormUnitOrbitCharacterStatement (F : Type u) (R : Type v)
    [NontriviallyNormedField F] [CompleteSpace F] [CharZero F] [IsUltrametricDist F]
    [NormedRing R] [NormedAlgebra F R] [IsUltrametricDist R] [ProperSpace R]
    [FiniteDimensional F R] {e : R → R → ℂ} (he : IsSelfDualBicharacter e) : Prop :=
  ExponentialProductStraighteningStatement F R →
  (∀ a : Rˣ, ∀ x y, e (conjugationHomeomorph a x) (conjugationHomeomorph a y) = e x y) →
  ∃ c : ℝ, ∃ hc : 1 ≤ c, ∃ ε > (0 : ℝ), max 1 ‖(1 : R)‖ * (c * ε) < 1 ∧
    ∀ (r : ℝ) (hr : 0 < r) (hr₁ : r < 1) (hcr : c * r < 1), r ≤ ε → ∀ z : R,
      let L := B(R, hr)
      let H := normUnitCongruence (R := R) (mul_nonneg (zero_le_one.trans hc) hr.le) hcr
      let K := normUnitCongruence (R := R) hr.le hr₁
      ∃ J : Finset (AddChar L ℂ), (J : Set (AddChar L ℂ)) = latticeCharacterOrbit he L H z ∧
        J.Nonempty ∧
        ∃ (W : Type v) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
          (ρ : Representation ℂ K W), IsSmooth ρ ∧
          ∀ (x : L) (k : K), (k.val : R) = NormedSpace.exp (x : R) →
            ρ.character k = ∑ χ ∈ J, χ x

theorem normUnitOrbitCharacter {F : Type u} {A : Type v}
    [NontriviallyNormedField F] [CompleteSpace F] [CharZero F] [IsUltrametricDist F]
    [NormedRing A] [NormedAlgebra F A] [IsUltrametricDist A] [ProperSpace A]
    [FiniteDimensional F A] {eA : A → A → ℂ} (heA : IsSelfDualBicharacter eA) :
    NormUnitOrbitCharacterStatement F A heA := by
  intro hStraighten hPair
  obtain ⟨c, hc, ε, hε, hsmall, hChar⟩ := compactExponentialCharacter (F := F) (R := A) hStraighten
  refine ⟨c, hc, ε, hε, hsmall, fun r hr hr₁ hcr hrε z => ?_⟩
  let L := B(A, hr)
  have hcr₀ : 0 ≤ c * r := mul_nonneg (zero_le_one.trans hc) hr.le
  let H := normUnitCongruence (R := A) hcr₀ hcr
  have hHr : max 1 ‖(1 : A)‖ * (c * r) < 1 :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrε (zero_le_one.trans hc))
      (zero_le_one.trans (le_max_left _ _))).trans_lt hsmall
  have hL : IsCompact (L : Set A) := isCompact_closedBall _ _
  have hH : IsCompact (H : Set Aˣ) := isCompact_normUnitCongruence hcr₀ hcr
  have hstable (a : Aˣ) (ha : a ∈ H) (x : A) (hx : x ∈ L) :
      conjugationHomeomorph a x ∈ L := by
    change dist (conjugationHomeomorph a x) 0 ≤ r
    rw [dist_zero_right, norm_conjugation_eq_of_mem_normUnitCongruence hcr₀ hcr hHr ha]
    exact dist_zero_right x ▸ hx
  obtain ⟨J, hJ, hNonempty, hLC, hInv⟩ :=
    latticeCharacterOrbit_sum heA L H z hL hH hstable (fun a _ => hPair a)
  exact ⟨J, hJ, hNonempty, hChar r hr hr₁ hrε J hLC hInv⟩

end NormCongruence

end Langlands.HarmonicAnalysis.UnitConjugation
