import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Extending positive characters across finite index
-/

noncomputable section

open scoped NNReal

namespace Langlands.PositiveCharacter

universe uA uG

/-- Positive real units have unique roots of each nonzero natural degree. -/
theorem pow_injective {n : ℕ} (hn : n ≠ 0) :
    Function.Injective (fun x : ℝ≥0ˣ => x ^ n) := by
  intro x y h
  apply Units.ext
  have hr := congrArg (fun z : ℝ≥0ˣ => (z : ℝ≥0) ^ ((n : ℝ)⁻¹)) h
  simpa only [Units.val_pow_eq_pow_val, NNReal.pow_rpow_inv_natCast _ hn] using hr

variable {A : Type uA} [CommGroup A]

private def indexPower (H : Subgroup A) : A →* H where
  toFun a := ⟨a ^ H.index, H.pow_index_mem a⟩
  map_one' := Subtype.ext (one_pow _)
  map_mul' a b := Subtype.ext (mul_pow a b H.index)

/-- The unique positive character extending `χ` from a finite-index subgroup.
Its value at `a` is the positive `H.index`-th root of `χ(a ^ H.index)`. -/
def finiteIndexExtension (H : Subgroup A) [H.FiniteIndex]
    (χ : H →* ℝ≥0ˣ) : A →* ℝ≥0ˣ :=
  (Units.map (NNReal.rpowMonoidHom ((H.index : ℝ)⁻¹))).comp
    (χ.comp (indexPower H))

@[simp]
theorem finiteIndexExtension_apply (H : Subgroup A) [H.FiniteIndex]
    (χ : H →* ℝ≥0ˣ) (a : A) :
    (finiteIndexExtension H χ a : ℝ≥0) =
      (χ ⟨a ^ H.index, H.pow_index_mem a⟩ : ℝ≥0) ^ ((H.index : ℝ)⁻¹) := rfl

@[simp]
theorem finiteIndexExtension_restrict (H : Subgroup A) [H.FiniteIndex]
    (χ : H →* ℝ≥0ˣ) (h : H) :
    finiteIndexExtension H χ h = χ h := by
  apply Units.ext
  rw [finiteIndexExtension_apply]
  have heq : (⟨(h : A) ^ H.index, H.pow_index_mem (h : A)⟩ : H) = h ^ H.index :=
    Subtype.ext rfl
  rw [heq, map_pow, Units.val_pow_eq_pow_val]
  exact NNReal.pow_rpow_inv_natCast _ Subgroup.FiniteIndex.index_ne_zero

theorem finiteIndexExtension_unique (H : Subgroup A) [H.FiniteIndex]
    (χ : H →* ℝ≥0ˣ) (ψ : A →* ℝ≥0ˣ)
    (hψ : ∀ h : H, ψ h = χ h) :
    ψ = finiteIndexExtension H χ := by
  apply MonoidHom.ext
  intro a
  apply pow_injective (n := H.index) Subgroup.FiniteIndex.index_ne_zero
  change ψ a ^ H.index = finiteIndexExtension H χ a ^ H.index
  rw [← map_pow, ← map_pow]
  exact (hψ ⟨a ^ H.index, H.pow_index_mem a⟩).trans
    (finiteIndexExtension_restrict H χ ⟨a ^ H.index, H.pow_index_mem a⟩).symm

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An open-kernel positive character on a compact group is trivial. -/
theorem eq_one_of_compact [SeparatelyContinuousMul G] [CompactSpace G] (χ : G →* ℝ≥0ˣ)
    (hχ : IsOpen (χ.ker : Set G)) (g : G) : χ g = 1 := by
  let : Finite (G ⧸ χ.ker) := χ.ker.quotient_finite_of_isOpen hχ
  have hn : χ.ker.index ≠ 0 := χ.ker.index_ne_zero_of_finite
  apply pow_injective hn
  change χ g ^ χ.ker.index = 1 ^ χ.ker.index
  rw [one_pow, ← map_pow]
  exact χ.ker.pow_index_mem g

/-- In particular, such a character is trivial on every compact subgroup. -/
theorem eq_one_on_compact [IsTopologicalGroup G] (χ : G →* ℝ≥0ˣ)
    (hχ : IsOpen (χ.ker : Set G)) (K : Subgroup G)
    (hK : IsCompact (K : Set G)) (k : K) : χ k = 1 := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact eq_one_of_compact (χ.comp K.subtype) (hχ.preimage continuous_subtype_val) k

end Langlands.PositiveCharacter
