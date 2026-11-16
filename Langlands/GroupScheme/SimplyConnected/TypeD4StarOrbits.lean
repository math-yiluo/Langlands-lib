import Langlands.GroupScheme.SimplyConnected.TypeDRankOneOrbit
import Langlands.GroupScheme.Reductive.TitsIndexRankOneOrbit

/-! # Fixed leaves and transitive leaf orbits for the full type-D4 star action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.CartanDNumbering

/-- Moving any leaf of D4 to vertex zero preserves every Cartan entry. -/
theorem swap_leaf_preserves_D4 : ∀ t : Fin 4, t ≠ 1 → ∀ i j : Fin 4,
    CartanMatrix.D 4 (Equiv.swap t 0 i) (Equiv.swap t 0 j) =
      CartanMatrix.D 4 i j := by
  simp only [CartanMatrix.D, Matrix.of_apply]
  decide

private theorem third_leaf_unique {a b c d : Fin 4}
    (hab : a ≠ b) (ha : a ≠ 1) (hb : b ≠ 1)
    (hca : c ≠ a) (hcb : c ≠ b) (hc : c ≠ 1)
    (hda : d ≠ a) (hdb : d ≠ b) (hd : d ≠ 1) : c = d := by
  have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
  have ha' : a.val ≠ 1 := fun h => ha (Fin.ext h)
  have hb' : b.val ≠ 1 := fun h => hb (Fin.ext h)
  have hca' : c.val ≠ a.val := fun h => hca (Fin.ext h)
  have hcb' : c.val ≠ b.val := fun h => hcb (Fin.ext h)
  have hc' : c.val ≠ 1 := fun h => hc (Fin.ext h)
  have hda' : d.val ≠ a.val := fun h => hda (Fin.ext h)
  have hdb' : d.val ≠ b.val := fun h => hdb (Fin.ext h)
  have hd' : d.val ≠ 1 := fun h => hd (Fin.ext h)
  apply Fin.ext
  omega

end Langlands.CartanDNumbering

namespace Langlands.GroupScheme.TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- Reorient a D4 numbering by placing the supplied leaf at vertex zero. -/
def d4NumberingAt (e : d.Vertex ≃ Fin 4) (a : d.Vertex) : d.Vertex ≃ Fin 4 :=
  e.trans (Equiv.swap (e a) 0)

@[simp] theorem d4NumberingAt_self (e : d.Vertex ≃ Fin 4) (a : d.Vertex) :
    d.d4NumberingAt e a a = 0 := by
  simp [d4NumberingAt]

/-- Reorientation at a leaf retains the actual Cartan matrix. -/
theorem d4NumberingAt_cartan (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (a : d.Vertex) (ha : e a ≠ 1) (b c : d.Vertex) :
    d.cartan b c = CartanMatrix.D 4 (d.d4NumberingAt e a b) (d.d4NumberingAt e a c) := by
  rw [hD]
  exact (Langlands.CartanDNumbering.swap_leaf_preserves_D4 (e a) ha (e b) (e c)).symm

/-- A leaf fixed by the full star action gives fixed nonfork vertices after
reorientation. The other nonfork vertex is the intrinsically fixed center. -/
theorem star_fixes_nonfork_of_D4_fixed_leaf (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (a : d.Vertex) (ha : e a ≠ 1)
    (hfixed : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (b : d.Vertex)
    (hb : (d.d4NumberingAt e a b).val + 2 < 4) : d.star σ b = b := by
  by_cases hzero : (d.d4NumberingAt e a b).val = 0
  · have hba : b = a := (d.d4NumberingAt e a).injective (by
      rw [d.d4NumberingAt_self]
      exact Fin.ext hzero)
    simpa [hba] using hfixed σ
  · exact d.star_fixes_center_of_D (by decide) (d.d4NumberingAt e a)
      (d.d4NumberingAt_cartan e hD a ha) σ b (by omega)

/-- If no D4 leaf is fixed by every full Galois element, the full star
orbit of every leaf consists of all three leaves. -/
theorem star_transitive_on_D4_leaves_of_no_fixed_leaf (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a)
    (a b : d.Vertex) (ha : e a ≠ 1) (hb : e b ≠ 1) :
    ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = b := by
  classical
  by_cases hab : a = b
  · exact ⟨1, by simp [hab]⟩
  by_contra hnone
  have hnone' : ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K,
      d.star σ a ≠ b := by simpa only [not_exists] using hnone
  have hmove : ∀ x : d.Vertex, e x ≠ 1 →
      ∃ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ x ≠ x := by
    intro x hx
    by_contra h
    exact hno ⟨x, hx, by simpa only [not_exists, not_not] using h⟩
  obtain ⟨σ, hσ⟩ := hmove a ha
  obtain ⟨τ, hτ⟩ := hmove b hb
  have htip : ∀ (ρ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (x : d.Vertex),
      e x ≠ 1 → e (d.star ρ x) ≠ 1 := by
    intro ρ x hx h
    let c : d.Vertex := e.symm 1
    have hc : d.star ρ c = c :=
      d.star_fixes_center_of_D (by decide) e hD ρ c (by simp [c])
    have hxc : d.star ρ x = d.star ρ c := by
      apply e.injective
      simpa [hc, c] using h
    have hxc' := (d.starPermutation ρ).injective hxc
    exact hx (by simp [hxc', c])
  have hτa : d.star τ b ≠ a := by
    intro h
    apply hnone' τ⁻¹
    rw [← h, ← d.star_mul, inv_mul_cancel, d.star_one]
  have heq : e (d.star σ a) = e (d.star τ b) :=
    Langlands.CartanDNumbering.third_leaf_unique
      (e.injective.ne hab) ha hb
      (e.injective.ne hσ) (e.injective.ne (hnone' σ)) (htip σ a ha)
      (e.injective.ne hτa) (e.injective.ne hτ) (htip τ b hb)
  apply hnone' (τ⁻¹ * σ)
  rw [d.star_mul, e.injective heq, ← d.star_mul, inv_mul_cancel, d.star_one]

/-- At split rank one, a D4 action without a globally fixed leaf has exactly
two possible distinguished sets: the center, or all three leaves. -/
theorem D4_marking_cases_of_no_fixed_leaf (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hrank : splitRank G = 1)
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure K ≃ₐ[K] SeparableClosure K, d.star σ a = a) :
    (∀ a, a ∈ d.distinguishedVertices ↔ e a = 1) ∨
      (∀ a, a ∈ d.distinguishedVertices ↔ e a ≠ 1) := by
  classical
  let v := d.rankOneDistinguishedVertex hrank
  by_cases hv : e v.val = 1
  · left
    intro a
    constructor
    · intro ha
      obtain ⟨σ, hσ⟩ := d.exists_star_eq_of_rank_one hrank v ⟨a, ha⟩
      have hfix := d.star_fixes_center_of_D (by decide) e hD σ v.val (by rw [hv]; decide)
      simpa only [hfix, hv] using congrArg e hσ |>.symm
    · intro ha
      have hav : a = v.val := e.injective (ha.trans hv.symm)
      simpa only [hav] using v.property
  · right
    intro a
    rw [d.mem_distinguishedVertices_iff_rankOne_orbit hrank]
    constructor
    · rintro ⟨σ, rfl⟩ hcenter
      let c : d.Vertex := e.symm 1
      have hc := d.star_fixes_center_of_D (by decide) e hD σ c (by simp [c])
      have heq : d.star σ v.val = d.star σ c := by
        apply e.injective
        simpa only [hc, c, Equiv.apply_symm_apply] using hcenter
      exact hv (by simpa [c] using congrArg e ((d.starPermutation σ).injective heq))
    · intro ha
      exact d.star_transitive_on_D4_leaves_of_no_fixed_leaf e hD hno v.val a hv ha

end Langlands.GroupScheme.TitsIndexData
