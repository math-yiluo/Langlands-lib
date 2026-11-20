import Langlands.Global.Arithmetic.KrasnerNeighborhood

/-! # Simultaneous control of roots under coefficient perturbation -/

noncomputable section

open Polynomial IntermediateField

namespace Langlands.Global.FieldRealization

universe u v

variable {K : Type u} {L : Type v} [NormedField K] [NormedField L] [NormedAlgebra K L]

/-- Nearby monic polynomials of the same degree have distinct roots, and each root of
the new polynomial lies within the prescribed radius of a root of the old polynomial. -/
theorem exists_coeff_neighborhood_of_separable (f : K[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (hs : f.Separable) (hfs : (f.map (algebraMap K L)).Splits)
    (δ : L → ℝ) (hδ : ∀ a ∈ f.rootSet L, 0 < δ a) :
    ∃ ε > 0, ∀ (g : K[X]), g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → (g.map (algebraMap K L)).Splits →
      g.Separable ∧ ∀ b : L, aeval b g = 0 → ∃ a : L, aeval a f = 0 ∧ ‖a - b‖ < δ a := by
  classical
  let S := (f.aroots L).toFinset
  have hS {a : L} : a ∈ S ↔ a ∈ f.rootSet L := Iff.rfl
  let pairs := (S.product S).filter (fun p => p.1 ≠ p.2)
  let radii := insert 1 (S.image δ ∪ pairs.image (fun p => ‖p.1 - p.2‖ / 2))
  have hradii : radii.Nonempty := by simp [radii]
  let r := radii.inf' hradii id
  have hr : 0 < r := by
    dsimp [r]
    rw [Finset.lt_inf'_iff]
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact zero_lt_one
    rcases Finset.mem_union.mp hz with hz | hz
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hz
      exact hδ a (hS.mp ha)
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp).2)) (by norm_num)
  have hrδ {a : L} (ha : a ∈ f.rootSet L) : r ≤ δ a :=
    Finset.inf'_le id (Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_image_of_mem δ (hS.mpr ha))))
  have hrsep {a b : L} (ha : a ∈ f.rootSet L) (hb : b ∈ f.rootSet L) (hab : a ≠ b) :
      r ≤ ‖a - b‖ / 2 := by
    have hp : (a, b) ∈ pairs :=
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hS.mpr ha, hS.mpr hb⟩, hab⟩
    have hz : ‖a - b‖ / 2 ∈ radii := Finset.mem_insert_of_mem (Finset.mem_union_right _
      (Finset.mem_image_of_mem (fun p : L × L => ‖p.1 - p.2‖ / 2) hp))
    exact Finset.inf'_le id hz
  let sizes := insert 1 (S.image (fun a => max ‖a‖ 1))
  have hsizes : sizes.Nonempty := by simp [sizes]
  let B := sizes.sup' hsizes id
  have hB : 0 < B := zero_lt_one.trans_le (Finset.le_sup' id (Finset.mem_insert_self _ _))
  have hBa {a : L} (ha : a ∈ f.rootSet L) : max ‖a‖ 1 ≤ B :=
    Finset.le_sup' id (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem (fun a : L => max ‖a‖ 1) (hS.mpr ha)))
  let ε := (r / B) ^ f.natDegree / (f.natDegree + 1)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hbound : (((f.natDegree : ℝ) + 1) * ε) ^ (f.natDegree : ℝ)⁻¹ = r / B := by
    dsimp [ε]
    rw [mul_div_cancel₀ _ (by positivity), Real.pow_rpow_inv_natCast (by positivity) hd.ne']
  refine ⟨ε, hε, fun g hg hdeg hcoeff hgs => ?_⟩
  have hnear (a : f.rootSet L) : ∃ b : g.rootSet L, ‖(a : L) - (b : L)‖ < r := by
    obtain ⟨b, hb, hdist⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt hε
      (hf.mem_rootSet.mp a.property) hf hg hdeg hcoeff hgs
    refine ⟨⟨b, hg.mem_rootSet.mpr (mem_aroots.mp hb).2⟩, hdist.trans_le ?_⟩
    rw [hbound]
    exact (mul_le_mul_of_nonneg_left (hBa a.property) (div_nonneg hr.le hB.le)).trans_eq
      (div_mul_cancel₀ r hB.ne')
  choose β hβ using hnear
  have hinj : Function.Injective β := by
    intro a b hab
    by_contra hne
    have hne' : (a : L) ≠ (b : L) := fun h => hne (Subtype.ext h)
    have htriangle : ‖(a : L) - (b : L)‖ ≤
        ‖(a : L) - (β a : L)‖ + ‖(b : L) - (β b : L)‖ := by
      rw [hab, ← norm_sub_rev (β b : L) (b : L)]
      exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    have hd₁ := hrsep a.property b.property hne'
    have hd₂ := hβ a
    have hd₃ := hβ b
    linarith
  have hgcard : Fintype.card (g.rootSet L) = g.natDegree := by
    have hu : Fintype.card (g.rootSet L) ≤ g.natDegree := by
      simp_rw [rootSet_def, Finset.coe_sort_coe, Fintype.card_coe]
      exact (Multiset.toFinset_card_le _).trans g.card_roots_map_le_natDegree
    have hl := Fintype.card_le_of_injective β hinj
    rw [card_rootSet_eq_natDegree hs hfs, ← hdeg] at hl
    exact le_antisymm hu hl
  have hsurj : Function.Surjective β :=
    ((Fintype.bijective_iff_injective_and_card β).mpr
      ⟨hinj, (card_rootSet_eq_natDegree hs hfs).trans (hdeg.symm.trans hgcard.symm)⟩).2
  refine ⟨(card_rootSet_eq_natDegree_iff_of_splits hg.ne_zero hgs).mp hgcard, fun b hb => ?_⟩
  obtain ⟨a, hab⟩ := hsurj ⟨b, hg.mem_rootSet.mpr hb⟩
  have ha := hβ a
  rw [hab] at ha
  exact ⟨a, hf.mem_rootSet.mp a.property, ha.trans_le (hrδ a.property)⟩

/-- For a Krasner extension, a nearby root generates a field containing an original root. -/
theorem exists_coeff_neighborhood_adjoin_le [IsKrasner K L] (f : K[X]) (hf : f.Monic)
    (hd : 0 < f.natDegree) (hs : f.Separable) (hfs : (f.map (algebraMap K L)).Splits) :
    ∃ ε > 0, ∀ (g : K[X]), g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → (g.map (algebraMap K L)).Splits →
      g.Separable ∧ ∀ b : L, aeval b g = 0 → ∃ a : L, aeval a f = 0 ∧ a ∈ K⟮b⟯ := by
  obtain ⟨ε, hε, h⟩ := exists_coeff_neighborhood_of_separable f hf hd hs hfs
    (conjugateRadius K) (fun a _ => conjugateRadius_pos a)
  refine ⟨ε, hε, fun g hg hdeg hcoeff hgs => ?_⟩
  obtain ⟨hgsep, hnear⟩ := h g hg hdeg hcoeff hgs
  refine ⟨hgsep, fun b hb => ?_⟩
  obtain ⟨a, ha, hdist⟩ := hnear b hb
  have hai : IsIntegral K a := ⟨f, hf, ha⟩
  have hbi : IsIntegral K b := ⟨g, hg, hb⟩
  have hdiv := minpoly.dvd K a ha
  have hmin : (minpoly K a).Separable := hs.of_dvd hdiv
  have hsplit := hfs.of_dvd (map_ne_zero hf.ne_zero) (map_dvd _ hdiv)
  refine ⟨a, ha, IsKrasner.krasner hmin hsplit hbi (fun z hz hne => ?_)⟩
  exact hdist.trans_le (conjugateRadius_le a z hai hz hne)

/-- Uniform root matching in a coefficient neighborhood of a monic separable polynomial. -/
def PolynomialRootNeighborhoodStatement : Prop :=
  ∀ (K : Type u) (L : Type v) [NormedField K] [NormedField L] [NormedAlgebra K L]
    (f : K[X]), f.Monic → 0 < f.natDegree → f.Separable →
    (f.map (algebraMap K L)).Splits → ∀ (δ : L → ℝ), (∀ a ∈ f.rootSet L, 0 < δ a) →
    ∃ ε > 0, ∀ (g : K[X]), g.Monic → g.natDegree = f.natDegree →
      (∀ i, ‖g.coeff i - f.coeff i‖ < ε) → (g.map (algebraMap K L)).Splits →
      g.Separable ∧ ∀ b : L, aeval b g = 0 → ∃ a : L, aeval a f = 0 ∧ ‖a - b‖ < δ a

/-- The coefficient neighborhood with simultaneous control of all roots. -/
theorem polynomialRootNeighborhood : PolynomialRootNeighborhoodStatement.{u, v} := by
  intro K L _ _ _ f hf hd hs hfs δ hδ
  exact exists_coeff_neighborhood_of_separable f hf hd hs hfs δ hδ

end Langlands.Global.FieldRealization
