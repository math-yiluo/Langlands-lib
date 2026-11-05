import Langlands.Group.TwoPowerUnitaryConjugation

/-! # Real internal conjugators for two-power unitary elements -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Langlands.Group.RealTwoPowerUnitaryConjugation

open Langlands.Group.AlgebraicMatrixPowers
open Langlands.Group.AlgebraicPolar
open Langlands.Group.InternalPolarFactors

variable {𝕜 : Type u} [RCLike 𝕜] {n : Type} [Fintype n] [DecidableEq n]

/-- Entrywise scalar conjugation, as a multiplicative map on matrix units. -/
def conjugateEntries : GL n 𝕜 →* GL n 𝕜 :=
  Matrix.GeneralLinearGroup.map (starRingEnd 𝕜)

@[simp] theorem conjugateEntries_val (g : GL n 𝕜) :
    (conjugateEntries g).val = g.val.map (starRingEnd 𝕜) := rfl

@[simp] theorem conjugateEntries_star (g : GL n 𝕜) :
    conjugateEntries (star g) = star (conjugateEntries g) := by
  apply Units.ext
  ext i j
  simp [conjugateEntries, Matrix.star_apply]

/-- Entrywise scalar conjugation preserves positive definiteness. -/
theorem posDef_conjugateEntries {g : GL n 𝕜} (hg : g.val.PosDef) :
    (conjugateEntries g).val.PosDef := by
  have heq : (conjugateEntries g).val = (star g.val).transpose := by
    ext i j
    rfl
  rw [heq]
  exact hg.conjTranspose.transpose

private theorem star_eq_inv_of_unitary {k : GL n 𝕜}
    (hk : k.val ∈ Matrix.unitaryGroup n 𝕜) : star k = k⁻¹ := by
  have hk' : k ∈ unitary (GL n 𝕜) := by
    rw [Units.unitary_eq]
    exact hk
  exact eq_inv_iff_mul_eq_one.mpr hk'.1

private theorem eq_of_posDef_mul_self_eq {a b : GL n 𝕜}
    (ha : a.val.PosDef) (hb : b.val.PosDef) (h : a * a = b * b) :
    a = b := by
  apply Units.ext
  apply (CFC.sq_eq_sq_iff a.val b.val ha.posSemidef.nonneg hb.posSemidef.nonneg).mp
  simpa only [pow_two, Units.val_mul] using congrArg Units.val h

/-- The positive square root of an entrywise real matrix is entrywise real. -/
theorem conjugateEntries_eq_self_of_posDef_square
    {a b : GL n 𝕜} (ha : a.val.PosDef) (hab : a * a = b)
    (hb : conjugateEntries b = b) : conjugateEntries a = a := by
  apply eq_of_posDef_mul_self_eq (posDef_conjugateEntries ha) ha
  rw [← map_mul, hab, hb]

/-- When scalar conjugation inverts an element with unitary square, its
positive polar square is entrywise real. -/
theorem conjugateEntries_star_mul_self
    (g : GL n 𝕜) (hbar : conjugateEntries g = g⁻¹)
    (hgg : (g * g).val ∈ Matrix.unitaryGroup n 𝕜) :
    conjugateEntries (star g * g) = star g * g := by
  have hsgg : star (g * g) = (g * g)⁻¹ := star_eq_inv_of_unitary hgg
  have hga : g * star g = (star g * g)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    calc
      g * star g * (star g * g) = g * star (g * g) * g := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hsgg]; group
  rw [map_mul, conjugateEntries_star, hbar, star_inv]
  calc
    (star g)⁻¹ * g⁻¹ = (g * star g)⁻¹ := by group
    _ = star g * g := by rw [hga, inv_inv]

/-- A unitary conjugate obtained inside the subgroup with an entrywise real
conjugating matrix. -/
def HasInternalRealUnitaryConjugate (H : Subgroup (GL n 𝕜)) (g : GL n 𝕜) : Prop :=
  ∃ c : GL n 𝕜, c ∈ H ∧ conjugateEntries c = c ∧
    (c * g * c⁻¹).val ∈ Matrix.unitaryGroup n 𝕜

private theorem posDef_inv {a : GL n 𝕜} (ha : a.val.PosDef) :
    (a⁻¹).val.PosDef := by
  simpa only [GeneralLinearGroup.coe_inv] using ha.inv

private theorem posDef_unitary_conjugate {a k : GL n 𝕜}
    (ha : a.val.PosDef) (hk : k.val ∈ Matrix.unitaryGroup n 𝕜) :
    (k * a * k⁻¹).val.PosDef := by
  have hs : k⁻¹ = star k := (star_eq_inv_of_unitary hk).symm
  rw [hs]
  exact k.isUnit.posDef_star_right_conjugate_iff.mpr ha

/-- An element inverted by scalar conjugation and having unitary square
admits an internal positive, entrywise real conjugator. -/
theorem exists_real_positive_conjugator_of_square_unitary
    (H : Subgroup (GL n 𝕜)) (hH : IsPolynomiallyDefined H)
    (hstar : ∀ g ∈ H, star g ∈ H) (g : GL n 𝕜) (hg : g ∈ H)
    (hbar : conjugateEntries g = g⁻¹)
    (hgg : (g * g).val ∈ Matrix.unitaryGroup n 𝕜) :
    ∃ c : GL n 𝕜, c ∈ H ∧ c.val.PosDef ∧ conjugateEntries c = c ∧
      (c * g * c⁻¹).val ∈ Matrix.unitaryGroup n 𝕜 := by
  obtain ⟨k, a, hk, ha, hku, hapos, hka⟩ :=
    exists_unitary_posDef_factors H hH hstar g hg
  have hsa : star a = a := Units.ext hapos.isHermitian.star_eq
  have hsk : star k = k⁻¹ := star_eq_inv_of_unitary hku
  have haa : a * a = star g * g := by
    rw [hka, star_mul, hsa, hsk]
    group
  have har : conjugateEntries a = a :=
    conjugateEntries_eq_self_of_posDef_square hapos haa
      (conjugateEntries_star_mul_self g hbar hgg)
  have hsgg : star (g * g) = (g * g)⁻¹ := star_eq_inv_of_unitary hgg
  have hga : g * star g = (star g * g)⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    calc
      g * star g * (star g * g) = g * star (g * g) * g := by
        simp only [star_mul, mul_assoc]
      _ = 1 := by rw [hsgg]; group
  have hsq : (k * a * k⁻¹) * (k * a * k⁻¹) = a⁻¹ * a⁻¹ := by
    rw [hka, star_mul, hsa, hsk] at hga
    calc
      k * a * k⁻¹ * (k * a * k⁻¹) = (k * a) * (a * k⁻¹) := by group
      _ = (a * k⁻¹ * (k * a))⁻¹ := hga
      _ = a⁻¹ * a⁻¹ := by group
  have hconj : k * a * k⁻¹ = a⁻¹ :=
    eq_of_posDef_mul_self_eq (posDef_unitary_conjugate hapos hku) (posDef_inv hapos) hsq
  obtain ⟨c, hc, hcpos, hcc⟩ := exists_positive_sqrt H hH a hapos ha
  have hcr : conjugateEntries c = c :=
    conjugateEntries_eq_self_of_posDef_square hcpos hcc har
  have hcsq : (k * c * k⁻¹) * (k * c * k⁻¹) = c⁻¹ * c⁻¹ := by
    calc
      k * c * k⁻¹ * (k * c * k⁻¹) = k * (c * c) * k⁻¹ := by group
      _ = a⁻¹ := by rw [hcc, hconj]
      _ = c⁻¹ * c⁻¹ := by rw [← hcc]; group
  have hcconj : k * c * k⁻¹ = c⁻¹ :=
    eq_of_posDef_mul_self_eq (posDef_unitary_conjugate hcpos hku)
      (posDef_inv hcpos) hcsq
  have hck : c * k = k * c⁻¹ := by
    calc
      c * k = (k * c * k⁻¹)⁻¹ * k := by rw [hcconj]; group
      _ = k * c⁻¹ := by group
  refine ⟨c, hc, hcpos, hcr, ?_⟩
  have hcg : c * g * c⁻¹ = k := by
    rw [hka, ← hcc]
    calc
      c * (k * (c * c)) * c⁻¹ = (c * k) * c := by group
      _ = k := by rw [hck]; group
  rwa [hcg]

/-- Internal two-power unitarization preserves reality of the conjugator
when scalar conjugation inverts the element. -/
theorem exists_real_conjugator_of_two_power_unitary
    (H : Subgroup (GL n 𝕜)) (hH : IsPolynomiallyDefined H)
    (hstar : ∀ g ∈ H, star g ∈ H) (r : ℕ)
    (g : GL n 𝕜) (hg : g ∈ H) (hbar : conjugateEntries g = g⁻¹)
    (hpow : (g ^ (2 ^ r)).val ∈ Matrix.unitaryGroup n 𝕜) :
    HasInternalRealUnitaryConjugate H g := by
  induction r generalizing g with
  | zero =>
      refine ⟨1, H.one_mem, map_one _, ?_⟩
      simpa using hpow
  | succ r ih =>
      have hbar' : conjugateEntries (g * g) = (g * g)⁻¹ := by
        rw [map_mul, hbar, _root_.mul_inv_rev]
      have hpow' : ((g * g) ^ (2 ^ r)).val ∈ Matrix.unitaryGroup n 𝕜 := by
        have heq : (g * g) ^ (2 ^ r) = g ^ (2 ^ (r + 1)) := by
          calc
            (g * g) ^ (2 ^ r) = (g ^ 2) ^ (2 ^ r) := by rw [pow_two]
            _ = g ^ (2 * (2 ^ r)) := (pow_mul g 2 (2 ^ r)).symm
            _ = g ^ (2 ^ (r + 1)) := by rw [pow_succ, Nat.mul_comm]
        rwa [heq]
      obtain ⟨b, hb, hbr, hbu⟩ := ih (g * g) (H.mul_mem hg hg) hbar' hpow'
      have hbsq : ((b * g * b⁻¹) * (b * g * b⁻¹)).val ∈
          Matrix.unitaryGroup n 𝕜 := by
        convert hbu using 1; congr 1; group
      have hbbar : conjugateEntries (b * g * b⁻¹) = (b * g * b⁻¹)⁻¹ := by
        rw [map_mul, map_mul, map_inv, hbr, hbar]
        group
      obtain ⟨a, ha, _, har, hau⟩ := exists_real_positive_conjugator_of_square_unitary
        H hH hstar (b * g * b⁻¹) (H.mul_mem (H.mul_mem hb hg) (H.inv_mem hb))
        hbbar hbsq
      refine ⟨a * b, H.mul_mem ha hb, ?_, ?_⟩
      · rw [map_mul, har, hbr]
      · convert hau using 1; congr 1; group

/-- Two-power torsion elements inverted by scalar conjugation admit
entrywise real conjugators inside the same subgroup. -/
theorem exists_real_conjugator_of_two_power_eq_one
    (H : Subgroup (GL n 𝕜)) (hH : IsPolynomiallyDefined H)
    (hstar : ∀ g ∈ H, star g ∈ H) (r : ℕ)
    (g : GL n 𝕜) (hg : g ∈ H) (hbar : conjugateEntries g = g⁻¹)
    (hpow : g ^ (2 ^ r) = 1) :
    HasInternalRealUnitaryConjugate H g := by
  apply exists_real_conjugator_of_two_power_unitary H hH hstar r g hg hbar
  rw [hpow]
  exact (Matrix.unitaryGroup n 𝕜).one_mem

end Langlands.Group.RealTwoPowerUnitaryConjugation
