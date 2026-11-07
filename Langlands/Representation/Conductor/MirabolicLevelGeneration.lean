import Langlands.Representation.Conductor.Congruence
import Langlands.Group.GL.MirabolicGeneration
import Langlands.Group.GL.MirabolicRadical

/-!
# Integral mirabolic generation of the newvector subgroup

The generation step in JPSS (1981), Section 5.3, for nonnegative levels.
-/

noncomputable section

namespace Langlands.Conductor

open Matrix Langlands.GeneralLinear

universe uR uF

variable {R : Type uR} [CommRing R] {n : ℕ}

/-- Integral mirabolic matrices whose final column reduces to the final standard
column modulo `I`. In blocks these are `[[h,u],[0,1]]` with `u` in `I`. -/
def integralJacquetMirabolic (n : ℕ) (I : Ideal R) :
    Subgroup (Langlands.GeneralLinear (n + 1) R) :=
  mirabolic n R ⊓ (oppositeMirabolic n (R ⧸ I)).comap
    (GeneralLinearGroup.map (Ideal.Quotient.mk I))

theorem mem_integralJacquetMirabolic (I : Ideal R)
    (g : Langlands.GeneralLinear (n + 1) R) :
    g ∈ integralJacquetMirabolic n I ↔ g ∈ mirabolic n R ∧
      ∀ i, g i (Fin.last n) -
        (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) i (Fin.last n) ∈ I := by
  change (_ ∧ _) ↔ _
  apply and_congr_right
  intro _
  change (∀ i, (GeneralLinearGroup.map (Ideal.Quotient.mk I) g).val i (Fin.last n) =
    if i = Fin.last n then 1 else 0) ↔ _
  apply forall_congr'
  intro i
  rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  simp [GeneralLinearGroup.map_apply, Matrix.one_apply]

@[simp] theorem integralJacquetMirabolic_top :
    integralJacquetMirabolic n (⊤ : Ideal R) = mirabolic n R := by
  ext g
  simp [mem_integralJacquetMirabolic]

private theorem mirabolic_eq_rowStabilizer :
    mirabolic n R = rowStabilizer (R := R) (Fin.last n) := by
  ext g
  change (∀ j, g.val (Fin.last n) j = if j = Fin.last n then 1 else 0) ↔
    g.val (Fin.last n) = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (Fin.last n)
  rw [funext_iff]
  simp [Matrix.one_apply, eq_comm]

private theorem inverseTranspose_map (S : Type*) [CommRing S] (f : R →+* S)
    (g : Langlands.GeneralLinear (n + 1) R) :
    inverseTranspose (n + 1) S (GeneralLinearGroup.map f g) =
      GeneralLinearGroup.map f (inverseTranspose (n + 1) R g) := by
  apply GeneralLinearGroup.ext
  intro i j
  simp only [inverseTranspose_entry, ← map_inv, GeneralLinearGroup.map_apply]

/-- The inverse-transposed Jacquet mirabolic is the intersection of the
last-column mirabolic with the actual last-row congruence subgroup. -/
theorem integralJacquetMirabolic_map_inverseTranspose (I : Ideal R) :
    (integralJacquetMirabolic n I).map (inverseTranspose (n + 1) R).toMonoidHom =
      integralCongruence n I ⊓ oppositeMirabolic n R := by
  ext g
  have hiff (a : Langlands.GeneralLinear (n + 1) R) :
      inverseTranspose (n + 1) R a ∈ integralCongruence n I ↔
        GeneralLinearGroup.map (Ideal.Quotient.mk I) a ∈
          oppositeMirabolic n (R ⧸ I) := by
    change GeneralLinearGroup.map (Ideal.Quotient.mk I)
      (inverseTranspose (n + 1) R a) ∈ rowStabilizer (Fin.last n) ↔ _
    rw [← inverseTranspose_map, ← mirabolic_eq_rowStabilizer]
    rw [← inverseTranspose_mem_oppositeMirabolic_iff]
    simp only [inverseTranspose_involutive]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨(hiff a).2 ha.2, (inverseTranspose_mem_oppositeMirabolic_iff a).2 ha.1⟩
  · intro hg
    refine ⟨inverseTranspose (n + 1) R g, ?_, by simp⟩
    constructor
    · exact (inverseTranspose_mem_oppositeMirabolic_iff _).1 (by simpa using hg.2)
    · exact (hiff _).1 (by simpa using hg.1)

private def ringTransvection (i j : Fin (n + 1)) (hij : i ≠ j) (c : R) :
    Langlands.GeneralLinear (n + 1) R where
  val := Matrix.transvection i j c
  inv := Matrix.transvection i j (-c)
  val_inv := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp
  inv_val := by rw [Matrix.transvection_mul_transvection_same _ _ hij]; simp

private def lowerShear (v : Fin n → R) : Langlands.GeneralLinear (n + 1) R :=
  inverseTranspose (n + 1) R ((Mirabolic.radicalElement v).val.val)⁻¹

private theorem lowerShear_first (v : Fin n → R)
    (i : Fin n) (j : Fin (n + 1)) :
    (lowerShear v).val i.castSucc j = if j = i.castSucc then 1 else 0 := by
  simp only [lowerShear, inverseTranspose_entry, inv_inv]
  exact Mirabolic.radicalElement_first v j i

private theorem lowerShear_last (v : Fin n → R) (j : Fin n) :
    (lowerShear v).val (Fin.last n) j.castSucc = v j := by
  simp only [lowerShear, inverseTranspose_entry, inv_inv]
  exact Mirabolic.radicalElement_last v j

private theorem lowerShear_column (v : Fin n → R) (i : Fin (n + 1)) :
    (lowerShear v).val i (Fin.last n) = if i = Fin.last n then 1 else 0 := by
  simp only [lowerShear, inverseTranspose_entry, inv_inv]
  exact Mirabolic.radicalElement_bottom v i

private theorem lowerShear_mem (I : Ideal R) (v : Fin n → R) (hv : ∀ i, v i ∈ I) :
    lowerShear v ∈ integralCongruence n I ⊓ oppositeMirabolic n R := by
  refine ⟨(mem_integralCongruence n I _).2 ?_, lowerShear_column v⟩
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [lowerShear_column]
  · simpa [lowerShear_last, Matrix.one_apply, (Fin.castSucc_ne_last _).symm] using hv j

private theorem ringTransvection_mem_mirabolic
    (i j : Fin (n + 1)) (hij : i ≠ j) (hi : i ≠ Fin.last n) (c : R) :
    ringTransvection i j hij c ∈ mirabolic n R := by
  intro k
  change (Matrix.transvection i j c) (Fin.last n) k = _
  simp [Matrix.transvection, Matrix.one_apply, hi, eq_comm]

private theorem lowerTransvection_mem (I : Ideal R)
    (j : Fin n) (c : R) (hc : c ∈ I) :
    ringTransvection (Fin.last n) j.castSucc
      (Fin.castSucc_ne_last j).symm c ∈
        integralCongruence n I ⊓ oppositeMirabolic n R := by
  constructor
  · apply (mem_integralCongruence n I _).2
    intro k
    change (Matrix.transvection (Fin.last n) j.castSucc c) (Fin.last n) k -
      (1 : Matrix _ _ R) (Fin.last n) k ∈ I
    simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> simp_all
  · intro k
    change (Matrix.transvection (Fin.last n) j.castSucc c) k (Fin.last n) = _
    simp [Matrix.transvection, Matrix.one_apply]

private theorem mem_of_same_last_row
    (H : Subgroup (Langlands.GeneralLinear (n + 1) R))
    (hP : mirabolic n R ≤ H)
    (g b : Langlands.GeneralLinear (n + 1) R) (hb : b ∈ H)
    (hrow : ∀ j, g.val (Fin.last n) j = b.val (Fin.last n) j) :
    g ∈ H := by
  have hp : g * b⁻¹ ∈ mirabolic n R := by
    intro j
    change (g.val * (b⁻¹).val) (Fin.last n) j = _
    have heq : (g.val * (b⁻¹).val) (Fin.last n) j =
        (b.val * (b⁻¹).val) (Fin.last n) j := by
      simp only [Matrix.mul_apply, hrow]
    rw [heq]
    change (b * b⁻¹).val (Fin.last n) j = _
    simp [Matrix.one_apply, eq_comm]
  simpa only [inv_mul_cancel_right] using H.mul_mem (hP hp) hb

private theorem exists_diagonal_last_row
    (hn : 0 < n) (I : Ideal R) (d : Rˣ) (hd : (d : R) - 1 ∈ I)
    (H : Subgroup (Langlands.GeneralLinear (n + 1) R))
    (hP : mirabolic n R ≤ H)
    (hQ : integralCongruence n I ⊓ oppositeMirabolic n R ≤ H) :
    ∃ b ∈ H, ∀ j, b.val (Fin.last n) j =
      if j = Fin.last n then (d : R) else 0 := by
  let a : Fin n := ⟨0, hn⟩
  let l := Fin.last n
  have hal : a.castSucc ≠ l := Fin.castSucc_ne_last a
  let q₁ := ringTransvection l a.castSucc hal.symm ((d : R) - 1)
  let p := ringTransvection a.castSucc l hal (1 : R)
  let q₂ := ringTransvection l a.castSucc hal.symm (-((d : R) - 1) * (↑d⁻¹ : R))
  let b := q₁ * p * q₂
  refine ⟨b, H.mul_mem (H.mul_mem (hQ (lowerTransvection_mem I a _ hd))
    (hP (ringTransvection_mem_mirabolic _ _ hal hal _)))
    (hQ (lowerTransvection_mem I a _ (I.mul_mem_right _ (I.neg_mem hd)))), ?_⟩
  intro j
  change ((Matrix.transvection l a.castSucc ((d : R) - 1) *
    Matrix.transvection a.castSucc l 1) *
    Matrix.transvection l a.castSucc (-((d : R) - 1) * (↑d⁻¹ : R)) :
      Matrix (Fin (n + 1)) (Fin (n + 1)) R) l j =
        if j = l then (d : R) else 0
  by_cases hja : j = a.castSucc
  · subst j
    rw [Matrix.mul_transvection_apply_same, Matrix.transvection_mul_apply_same,
      Matrix.transvection_mul_apply_same]
    simp [Matrix.transvection, hal, Ne.symm hal]
  · rw [Matrix.mul_transvection_apply_of_ne _ _ l j hja,
      Matrix.transvection_mul_apply_same]
    by_cases hjl : j = l
    · subst j
      simp [Matrix.transvection, hal]
    · simp [Matrix.transvection, Ne.symm hja, hjl, Ne.symm hjl]

private theorem mul_lowerShear_last (g : Langlands.GeneralLinear (n + 1) R)
    (v : Fin n → R) (j : Fin n) :
    (g * lowerShear v).val (Fin.last n) j.castSucc =
      g.val (Fin.last n) j.castSucc + g.val (Fin.last n) (Fin.last n) * v j := by
  change (g.val * (lowerShear v).val) (Fin.last n) j.castSucc = _
  simp [Matrix.mul_apply, Fin.sum_univ_castSucc, lowerShear_first, lowerShear_last]

private theorem mul_lowerShear_last_last (g : Langlands.GeneralLinear (n + 1) R)
    (v : Fin n → R) :
    (g * lowerShear v).val (Fin.last n) (Fin.last n) =
      g.val (Fin.last n) (Fin.last n) := by
  change (g.val * (lowerShear v).val) (Fin.last n) (Fin.last n) = _
  simp [Matrix.mul_apply, lowerShear_column]

/-- A last-row congruence matrix with unit bottom-right entry is generated by
the integral mirabolic and the congruent opposite mirabolic. -/
theorem mem_mirabolic_sup_of_isUnit_last_entry (hn : 0 < n) (I : Ideal R)
    (g : Langlands.GeneralLinear (n + 1) R)
    (hg : g ∈ integralCongruence n I)
    (hd : IsUnit (g (Fin.last n) (Fin.last n))) :
    g ∈ mirabolic n R ⊔ (integralCongruence n I ⊓ oppositeMirabolic n R) := by
  obtain ⟨d, hd⟩ := hd
  let H := mirabolic n R ⊔ (integralCongruence n I ⊓ oppositeMirabolic n R)
  have hP : mirabolic n R ≤ H := le_sup_left
  have hQ : integralCongruence n I ⊓ oppositeMirabolic n R ≤ H := le_sup_right
  have hdI : (d : R) - 1 ∈ I := by
    simpa only [Matrix.one_apply_eq, hd] using
      (mem_integralCongruence n I g).1 hg (Fin.last n)
  obtain ⟨b, hb, hbr⟩ := exists_diagonal_last_row hn I d hdI H hP hQ
  let v : Fin n → R := fun j => -(↑d⁻¹ : R) * g (Fin.last n) j.castSucc
  have hv : ∀ j, v j ∈ I := by
    intro j
    apply I.mul_mem_left
    simpa only [Matrix.one_apply, (Fin.castSucc_ne_last j).symm, ite_false, sub_zero]
      using (mem_integralCongruence n I g).1 hg j.castSucc
  have he : lowerShear v ∈ H := hQ (lowerShear_mem I v hv)
  have hge : g * lowerShear v ∈ H := by
    apply mem_of_same_last_row H hP _ b hb
    intro j
    rw [hbr j]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simpa only [ite_true, mul_lowerShear_last_last] using hd.symm
    · rw [mul_lowerShear_last]
      simp [v, ← hd, Fin.castSucc_ne_last]
  simpa only [mul_inv_cancel_right] using H.mul_mem hge (H.inv_mem he)

/-- Over a local ring, a proper-ideal congruence subgroup is generated by the
two indicated integral mirabolics, in rank at least two. -/
theorem mirabolic_sup_congruent_opposite_of_le_maximalIdeal [IsLocalRing R]
    (hn : 0 < n) (I : Ideal R) (hI : I ≤ IsLocalRing.maximalIdeal R) :
    mirabolic n R ⊔ (integralCongruence n I ⊓ oppositeMirabolic n R) =
      integralCongruence n I := by
  apply le_antisymm
  · apply sup_le
    · intro g hg
      apply (mem_integralCongruence n I g).2
      intro j
      simp [hg j, Matrix.one_apply, eq_comm]
    · exact inf_le_left
  · intro g hg
    apply mem_mirabolic_sup_of_isUnit_last_entry hn I g hg
    apply isUnit_last_entry n 1 (by decide) g
    simpa only [pow_one] using integralCongruence_mono n hI hg

/-- The two integral mirabolics generate the full general linear group over a
local ring, in rank at least two. -/
theorem integral_mirabolic_sup_opposite_eq_top [IsLocalRing R] (hn : 0 < n) :
    mirabolic n R ⊔ oppositeMirabolic n R = ⊤ := by
  let H := mirabolic n R ⊔ oppositeMirabolic n R
  have hP : mirabolic n R ≤ H := le_sup_left
  have hunit (g : Langlands.GeneralLinear (n + 1) R)
      (hd : IsUnit (g (Fin.last n) (Fin.last n))) : g ∈ H := by
    simpa only [integralCongruence_top, top_inf_eq] using
      mem_mirabolic_sup_of_isUnit_last_entry hn (⊤ : Ideal R) g (by simp) hd
  apply top_unique
  intro g _
  by_cases hd : IsUnit (g (Fin.last n) (Fin.last n))
  · exact hunit g hd
  · have hsum : IsUnit (∑ j : Fin (n + 1),
        g (Fin.last n) j * g⁻¹ j (Fin.last n)) := by
      change IsUnit ((g * g⁻¹).val (Fin.last n) (Fin.last n))
      simp
    obtain ⟨j, _, hj⟩ := IsLocalRing.exists_of_isUnit_sum hsum
    have hj : IsUnit (g (Fin.last n) j) := isUnit_of_mul_isUnit_left hj
    have hjl : j ≠ Fin.last n := by
      intro he
      exact hd (he ▸ hj)
    let p := ringTransvection j (Fin.last n) hjl (1 : R)
    have hp : p ∈ H := hP (ringTransvection_mem_mirabolic _ _ hjl hjl _)
    have hgp : IsUnit ((g * p) (Fin.last n) (Fin.last n)) := by
      change IsUnit ((g.val * Matrix.transvection j (Fin.last n) 1 :
        Matrix (Fin (n + 1)) (Fin (n + 1)) R)
        (Fin.last n) (Fin.last n))
      rw [Matrix.mul_transvection_apply_same, one_mul]
      have hsum' : IsUnit
          ((g (Fin.last n) (Fin.last n) + g (Fin.last n) j) +
            -g (Fin.last n) (Fin.last n)) := by
        simpa [add_comm, add_left_comm] using hj
      exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hsum').resolve_right
        (by simpa using hd)
    simpa only [mul_inv_cancel_right] using H.mul_mem (hunit (g * p) hgp) (H.inv_mem hp)

/-- Integral generation of every last-row congruence subgroup over a local
ring, including the unit-ideal (level-zero) case. -/
theorem mirabolic_sup_congruent_opposite [IsLocalRing R]
    (hn : 0 < n) (I : Ideal R) :
    mirabolic n R ⊔ (integralCongruence n I ⊓ oppositeMirabolic n R) =
      integralCongruence n I := by
  by_cases hI : I = ⊤
  · simpa only [hI, integralCongruence_top, top_inf_eq] using
      integral_mirabolic_sup_opposite_eq_top (R := R) hn
  · exact mirabolic_sup_congruent_opposite_of_le_maximalIdeal hn I
      (IsLocalRing.le_maximalIdeal hI)

/-- The nonnegative-level generation identity used in the JPSS conductor
argument, expressed using the actual integral Jacquet mirabolics. -/
theorem integralJacquetMirabolic_sup_inverseTranspose [IsLocalRing R]
    (hn : 0 < n) (I : Ideal R) :
    integralJacquetMirabolic n (⊤ : Ideal R) ⊔
      (integralJacquetMirabolic n I).map (inverseTranspose (n + 1) R).toMonoidHom =
        integralCongruence n I := by
  rw [integralJacquetMirabolic_top, integralJacquetMirabolic_map_inverseTranspose]
  exact mirabolic_sup_congruent_opposite hn I

end Langlands.Conductor
