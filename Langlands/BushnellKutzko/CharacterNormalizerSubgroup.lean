import Langlands.BushnellKutzko.CharacterIntertwining

/-! # Character normalizers and their action on intertwining sets -/

noncomputable section

open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uG

variable {G : Type uG} [Group G] {H : Subgroup G}

/-- The subgroup of elements preserving the domain and values of a character. -/
def characterNormalizerSubgroup (χ : H →* ℂˣ) : Subgroup G where
  carrier := characterNormalizer χ
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    intro x hx
    congr 1
    apply Subtype.ext
    simp
  mul_mem' := by
    rintro a b ⟨ha, haχ⟩ ⟨hb, hbχ⟩
    refine ⟨mul_mem ha hb, ?_⟩
    intro x hx
    have hbx := (Subgroup.mem_normalizer_iff.mp hb (x : G)).mp x.property
    let y : H := ⟨_, hbx⟩
    have hay := (Subgroup.mem_normalizer_iff.mp ha (y : G)).mp y.property
    have hxy : (⟨_, hx⟩ : H) = ⟨_, hay⟩ := by
      apply Subtype.ext
      change (a * b) * (x : G) * (a * b)⁻¹ = a * (b * (x : G) * b⁻¹) * a⁻¹
      simp only [mul_inv_rev, mul_assoc]
    rw [hxy, haχ y hay, hbχ x hbx]
  inv_mem' := by
    rintro a ⟨ha, haχ⟩
    refine ⟨inv_mem ha, ?_⟩
    intro x hx
    let y : H := ⟨_, hx⟩
    have hay : a * (y : G) * a⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp ha (y : G)).mp y.property
    have hyx : (⟨_, hay⟩ : H) = x := by
      apply Subtype.ext
      change a * (a⁻¹ * (x : G) * (a⁻¹)⁻¹) * a⁻¹ = x
      simp [← mul_assoc]
    simpa only [hyx] using (haχ y hay).symm

private theorem characterSelfIntertwining_mul_of_overlap {χ : H →* ℂˣ} {a b : G}
    (ha : a ∈ characterSelfIntertwining χ) (hb : b ∈ characterSelfIntertwining χ)
    (hmid : ∀ x : H, (a * b) * (x : G) * (a * b)⁻¹ ∈ H → b * (x : G) * b⁻¹ ∈ H) :
    a * b ∈ characterSelfIntertwining χ := by
  intro x hx
  have hbconj := hmid x hx
  let y : H := ⟨_, hbconj⟩
  have heq : a * (y : G) * a⁻¹ = (a * b) * (x : G) * (a * b)⁻¹ := by
    change a * (b * (x : G) * b⁻¹) * a⁻¹ = _
    group
  have hay : a * (y : G) * a⁻¹ ∈ H := heq.symm ▸ hx
  exact (congrArg χ (Subtype.ext heq.symm)).trans ((ha y hay).trans (hb x hbconj))

/-- Multiplication on the left by a character normalizer preserves self-intertwining. -/
theorem mem_characterSelfIntertwining_mul_left_iff {χ : H →* ℂˣ} {a b : G}
    (ha : a ∈ characterNormalizerSubgroup χ) :
    a * b ∈ characterSelfIntertwining χ ↔ b ∈ characterSelfIntertwining χ := by
  have hmul {a b : G} (ha : a ∈ characterNormalizerSubgroup χ)
      (hb : b ∈ characterSelfIntertwining χ) : a * b ∈ characterSelfIntertwining χ := by
    have h := show a ∈ characterNormalizer χ from ha
    refine characterSelfIntertwining_mul_of_overlap h.2 hb fun x hx => ?_
    apply (Subgroup.mem_normalizer_iff.mp h.1 (b * (x : G) * b⁻¹)).mpr
    simpa only [mul_assoc, mul_inv_rev] using hx
  exact ⟨fun h => by simpa using hmul (inv_mem ha) h, hmul ha⟩

/-- Multiplication on the right by a character normalizer preserves self-intertwining. -/
theorem mem_characterSelfIntertwining_mul_right_iff {χ : H →* ℂˣ} {a b : G}
    (hb : b ∈ characterNormalizerSubgroup χ) :
    a * b ∈ characterSelfIntertwining χ ↔ a ∈ characterSelfIntertwining χ := by
  have hmul {a b : G} (ha : a ∈ characterSelfIntertwining χ)
      (hb : b ∈ characterNormalizerSubgroup χ) : a * b ∈ characterSelfIntertwining χ := by
    have h := show b ∈ characterNormalizer χ from hb
    exact characterSelfIntertwining_mul_of_overlap ha h.2 fun x _ =>
      (Subgroup.mem_normalizer_iff.mp h.1 (x : G)).mp x.property
  exact ⟨fun h => by simpa only [mul_assoc, mul_inv_cancel, mul_one] using hmul h (inv_mem hb),
    fun h => hmul h hb⟩

/-- In a double-coset intertwining formula, the full normalizer is the product
of the outer subgroup with the domain-normalizing part of the middle subgroup.
The outer subgroup preserves the character and is normalized by the second factor. -/
theorem characterNormalizer_eq_mul_of_doubleCoset (χ : H →* ℂˣ) (Y B : Subgroup G)
    (hI : characterSelfIntertwining χ = (Y : Set G) * (B : Set G) * (Y : Set G))
    (hY : Y ≤ characterNormalizerSubgroup χ)
    (hK : B ⊓ Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (Y : Set G)) :
    characterNormalizer χ = (Y : Set G) * ((B ⊓ Subgroup.normalizer (H : Set G) : Subgroup G) : Set G) := by
  let N := characterNormalizerSubgroup χ
  have hB (b : G) (hb : b ∈ B) : b ∈ characterSelfIntertwining χ := by
    rw [hI]
    exact Set.mem_mul.mpr ⟨b, Set.mem_mul.mpr ⟨1, one_mem Y, b, hb, one_mul b⟩,
      1, one_mem Y, mul_one b⟩
  ext g
  constructor
  · intro hg
    have hgN : g ∈ N := hg
    obtain ⟨yb, hyb, z, hz, rfl⟩ := Set.mem_mul.mp (hI ▸ hg.2)
    obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hyb
    have hbzN : b * z ∈ N := by
      have := N.mul_mem (N.inv_mem (hY hy)) hgN
      convert this using 1
      group
    have hbN : b ∈ N := by
      have := N.mul_mem hbzN (N.inv_mem (hY hz))
      simpa only [mul_assoc, mul_inv_cancel, mul_one] using this
    have hbNormal := (show b ∈ characterNormalizer χ from hbN).1
    have hbK : b ∈ B ⊓ Subgroup.normalizer (H : Set G) := ⟨hb, hbNormal⟩
    have hbz : b * z * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hK hbK) z).mp hz
    exact Set.mem_mul.mpr ⟨y * (b * z * b⁻¹), Y.mul_mem hy hbz, b, hbK, by group⟩
  · rintro ⟨y, hy, b, hb, rfl⟩
    exact N.mul_mem (hY hy) ⟨hb.2, hB b hb.1⟩


end Langlands.BushnellKutzko
