import Langlands.Global.Adelic
import Langlands.Galois.Local.SpectralDefinitions
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.FieldTheory.Finite.Basic

noncomputable section

open scoped Valued
open NumberField IsDedekindDomain

universe u

namespace Langlands.Global.CompletionResidue

variable (K : Type u) [Field K] [NumberField K] (v : FinitePlace K)

local notation "Kv" => FiniteCompletion K v
local notation "Ov" => LocalGalois.baseIntegers Kv

/-- The actual embedding of global integers takes values in the norm valuation ring. -/
theorem norm_algebraMap_le_one (x : RingOfIntegers K) :
    ‖algebraMap (RingOfIntegers K) Kv x‖ ≤ 1 := by
  exact NumberField.FinitePlace.norm_le_one K v x

/-- Global integers embedded in the actual norm valuation ring of the completion. -/
def integersMap : RingOfIntegers K →+* Ov where
  toFun x := ⟨algebraMap (RingOfIntegers K) Kv x, norm_algebraMap_le_one K v x⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

@[simp]
theorem integersMap_coe (x : RingOfIntegers K) :
    (integersMap K v x : Kv) = algebraMap (RingOfIntegers K) Kv x := rfl

/-- Reduction of an actual global integer in the completed residue field. -/
def residueMap : RingOfIntegers K →+* IsLocalRing.ResidueField Ov :=
  (IsLocalRing.residue Ov).comp (integersMap K v)

@[simp]
theorem residueMap_eq_zero_iff (x : RingOfIntegers K) :
    residueMap K v x = 0 ↔ x ∈ v.asIdeal := by
  rw [residueMap, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff]
  change ‖algebraMap (RingOfIntegers K) Kv x‖ < 1 ↔ x ∈ v.asIdeal
  exact NumberField.FinitePlace.norm_lt_one_iff_mem K v x

theorem ker_residueMap : RingHom.ker (residueMap K v) = v.asIdeal := by
  ext x
  exact residueMap_eq_zero_iff K v x

/-- Every integral element of the completion is congruent modulo its maximal
ideal to an actual global integer. -/
theorem exists_integer_norm_sub_lt_one (x : Ov) :
    ∃ a : RingOfIntegers K, ‖(x : Kv) - algebraMap (RingOfIntegers K) Kv a‖ < 1 := by
  obtain ⟨b, hb⟩ := (v.denseRange_algebraMap K).exists_dist_lt (x : Kv)
    (by norm_num : (0 : ℝ) < 1)
  rw [dist_eq_norm] at hb
  have hbx : ‖algebraMap K Kv b‖ ≤ 1 := by
    have h := IsUltrametricDist.norm_add_le_max (algebraMap K Kv b - (x : Kv)) (x : Kv)
    rw [sub_add_cancel] at h
    exact h.trans (max_le (by simpa [norm_sub_rev] using hb.le) x.property)
  have hbval : v.valuation K b ≤ 1 := by
    rw [Valued.toNormedField.norm_le_one_iff] at hbx
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self,
      RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] using hbx
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hbval
    (1 : (WithZero (Multiplicative ℤ))ˣ)
  have hab : ‖algebraMap (RingOfIntegers K) Kv a - algebraMap K Kv b‖ < 1 := by
    rw [IsScalarTower.algebraMap_apply (RingOfIntegers K) K Kv, ← map_sub,
      Valued.toNormedField.norm_lt_one_iff]
    simpa only [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply,
      Algebra.algebraMap_self,
      RingHom.id_apply, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', Units.val_one] using ha
  refine ⟨a, ?_⟩
  have h := IsUltrametricDist.norm_add_le_max
    ((x : Kv) - algebraMap K Kv b)
    (algebraMap K Kv b - algebraMap (RingOfIntegers K) Kv a)
  rw [sub_add_sub_cancel] at h
  exact h.trans_lt (max_lt hb (by simpa only [norm_sub_rev] using hab))

/-- The residue map is surjective by integral approximation. -/
theorem residueMap_surjective : Function.Surjective (residueMap K v) := by
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨a, ha⟩ := exists_integer_norm_sub_lt_one K v x
  refine ⟨a, ?_⟩
  change IsLocalRing.residue Ov (integersMap K v a) = IsLocalRing.residue Ov x
  apply sub_eq_zero.mp
  rw [← map_sub, IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  change ‖algebraMap (RingOfIntegers K) Kv a - (x : Kv)‖ < 1
  simpa only [norm_sub_rev] using ha

/-- The canonical quotient comparison, induced by the number-field embedding. -/
def residueEquiv : (RingOfIntegers K ⧸ v.asIdeal) ≃+* IsLocalRing.ResidueField Ov :=
  (Ideal.quotEquivOfEq (ker_residueMap K v).symm).trans
    ((residueMap K v).quotientKerEquivOfSurjective (residueMap_surjective K v))

@[simp]
theorem residueEquiv_mk (x : RingOfIntegers K) :
    residueEquiv K v (Ideal.Quotient.mk v.asIdeal x) =
      IsLocalRing.residue Ov (integersMap K v x) := rfl

instance finite_residueField : Finite (IsLocalRing.ResidueField Ov) :=
  Finite.of_equiv (RingOfIntegers K ⧸ v.asIdeal) (residueEquiv K v).toEquiv

theorem card_residueField : Nat.card (IsLocalRing.ResidueField Ov) = Ideal.absNorm v.asIdeal := by
  exact Nat.card_congr (residueEquiv K v).symm.toEquiv

/-- The completed and global quotient residue fields have the same characteristic. -/
theorem ringChar_residueField :
    ringChar (IsLocalRing.ResidueField Ov) = ringChar (RingOfIntegers K ⧸ v.asIdeal) := by
  rw [ringChar.eq_iff]
  exact ((residueEquiv K v).toRingHom.charP_iff (residueEquiv K v).injective _).mp inferInstance

theorem one_lt_card_residueField : 1 < Nat.card (IsLocalRing.ResidueField Ov) := by
  rw [card_residueField]
  exact NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem prime_ringChar_residueField : Nat.Prime (ringChar (IsLocalRing.ResidueField Ov)) :=
  CharP.prime_ringChar _

/-- The ideal norm is a positive power of the actual completed residue characteristic. -/
theorem absNorm_eq_ringChar_pow :
    ∃ f : ℕ, 0 < f ∧
      Ideal.absNorm v.asIdeal = ringChar (IsLocalRing.ResidueField Ov) ^ f := by
  let : Fintype (IsLocalRing.ResidueField Ov) := Fintype.ofFinite _
  obtain ⟨f, _, hf⟩ := FiniteField.card (IsLocalRing.ResidueField Ov)
    (ringChar (IsLocalRing.ResidueField Ov))
  refine ⟨f, f.pos, ?_⟩
  simpa only [← card_residueField K v, Nat.card_eq_fintype_card] using hf

end Langlands.Global.CompletionResidue
