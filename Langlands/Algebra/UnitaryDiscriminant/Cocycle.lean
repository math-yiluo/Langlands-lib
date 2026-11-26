import Langlands.Algebra.UnitaryDiscriminant.Lifts
import Langlands.Algebra.ScalarTwoCocycleTorsion

/-! # The determinant factor set of a twisted projective cocycle -/

noncomputable section

universe u

open Matrix

namespace Langlands.UnitaryDiscriminant

open ScalarTwoCocycle (IsTwoCocycle coboundary)

variable {F M : Type u} [Field F] [Field M] [Algebra F M]
  (H : Subgroup (M ≃ₐ[F] M)) {I : Type} [Fintype I] [DecidableEq I]

open Classical in
/-- The determinant factor set attached to a family `P` of invertible matrices, a family `c`
of unit scalars and an exponent `m`:
`μ(g, h) = c(g, h)^m · g(det P_h)^{ε(g)} · (-1)^{m ε(g) ε(h)}`,
where `ε(g) = 0` for `g ∈ H` and `ε(g) = 1` for `g ∉ H`. -/
def detCocycle (P : (M ≃ₐ[F] M) → GL I M) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ) (m : ℕ)
    (g h : M ≃ₐ[F] M) : Mˣ :=
  c g h ^ m * (if g ∈ H then 1 else g • GeneralLinearGroup.det (P h)) *
    (if g ∉ H ∧ h ∉ H then (-1) ^ m else 1)

variable {H}

theorem detCocycle_of_mem (P : (M ≃ₐ[F] M) → GL I M) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ)
    (m : ℕ) {g : M ≃ₐ[F] M} (hg : g ∈ H) (h : M ≃ₐ[F] M) :
    detCocycle H P c m g h = c g h ^ m := by
  simp [detCocycle, hg]

theorem detCocycle_of_not_mem_of_mem (P : (M ≃ₐ[F] M) → GL I M)
    (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ) (m : ℕ) {g h : M ≃ₐ[F] M} (hg : g ∉ H)
    (hh : h ∈ H) :
    detCocycle H P c m g h = c g h ^ m * g • GeneralLinearGroup.det (P h) := by
  simp [detCocycle, hg, hh]

theorem detCocycle_of_not_mem_of_not_mem (P : (M ≃ₐ[F] M) → GL I M)
    (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ) (m : ℕ) {g h : M ≃ₐ[F] M} (hg : g ∉ H)
    (hh : h ∉ H) :
    detCocycle H P c m g h = c g h ^ m * g • GeneralLinearGroup.det (P h) * (-1) ^ m := by
  simp [detCocycle, hg, hh]

theorem smul_neg_one_pow (g : M ≃ₐ[F] M) (m : ℕ) : g • ((-1 : Mˣ) ^ m) = (-1) ^ m := by
  rw [smul_pow']
  congr 1
  ext
  change g (-1) = -1
  simp

/-- The determinant factor set is an ordinary two-cocycle of `Gal(M/F)` with values in `Mˣ`,
provided `H` has index at most two (`hmul`), the scalars `c` satisfy the `m`-th power of the
twisted cocycle identity, and the determinants satisfy the determinant of the twisted
projective cocycle law in degree `2m`. -/
theorem detCocycle_isTwoCocycle (hmul : ∀ g h : M ≃ₐ[F] M, g * h ∈ H ↔ (g ∈ H ↔ h ∈ H))
    (P : (M ≃ₐ[F] M) → GL I M) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ) (m : ℕ)
    (hc : ∀ g h k, (c g h * c (g * h) k) ^ m = (twistUnit H g (c h k) * c g (h * k)) ^ m)
    (hdet : ∀ g h, GeneralLinearGroup.det (P g) * twistUnit H g (GeneralLinearGroup.det (P h)) =
      c g h ^ (2 * m) * GeneralLinearGroup.det (P (g * h))) :
    IsTwoCocycle (detCocycle H P c m) := by
  intro g h k
  have hA := hc g h k
  have hB := congrArg (g • ·) (hdet h k)
  simp only [smul_mul', smul_pow'] at hB
  have hgh := hmul g h
  have hhk := hmul h k
  by_cases hg : g ∈ H
  · -- `g` fixes `L`: the identity is the `m`-th power of the twisted cocycle identity.
    rw [twistUnit_of_mem hg] at hA
    have hA' := congrArg Units.val hA
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hA'
    rw [detCocycle_of_mem P c m hg, detCocycle_of_mem P c m hg]
    by_cases hh : h ∈ H
    · have hgh' : g * h ∈ H := hgh.2 (iff_of_true hg hh)
      rw [detCocycle_of_mem P c m hgh', detCocycle_of_mem P c m hh, smul_pow']
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      linear_combination hA'
    · have hgh' : g * h ∉ H := fun h' => hh ((hgh.1 h').1 hg)
      by_cases hk : k ∈ H
      · rw [detCocycle_of_not_mem_of_mem P c m hgh' hk,
          detCocycle_of_not_mem_of_mem P c m hh hk, smul_mul', smul_pow', smul_smul]
        apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        linear_combination ((((g * h) • GeneralLinearGroup.det (P k) : Mˣ)) : M) * hA'
      · rw [detCocycle_of_not_mem_of_not_mem P c m hgh' hk,
          detCocycle_of_not_mem_of_not_mem P c m hh hk, smul_mul', smul_mul', smul_pow',
          smul_smul, smul_neg_one_pow]
        apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
        linear_combination ((((g * h) • GeneralLinearGroup.det (P k) : Mˣ)) : M) * (-1) ^ m * hA'
  · -- `g` acts on `L` nontrivially.
    rw [twistUnit_of_not_mem hg] at hA
    have hA2 : (c g h * c (g * h) k * g • c h k) ^ m = c g (h * k) ^ m := by
      rw [mul_pow, hA, ← mul_pow, mul_comm, mul_inv_cancel_left]
    have hA' := congrArg Units.val hA2
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hA'
    by_cases hh : h ∈ H
    · have hgh' : g * h ∉ H := fun h' => hg ((hgh.1 h').2 hh)
      rw [twistUnit_of_mem hh, smul_smul] at hB
      have hB' := congrArg Units.val hB
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hB'
      rw [detCocycle_of_not_mem_of_mem P c m hg hh, detCocycle_of_mem P c m hh,
        smul_pow']
      by_cases hk : k ∈ H
      · have hhk' : h * k ∈ H := hhk.2 (iff_of_true hh hk)
        rw [detCocycle_of_not_mem_of_mem P c m hgh' hk, detCocycle_of_not_mem_of_mem P c m hg hhk']
        apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val]
        linear_combination (c g h : M) ^ m * (c (g * h) k : M) ^ m * hB' +
          ((g • GeneralLinearGroup.det (P (h * k)) : Mˣ) : M) * ((g • c h k : Mˣ) : M) ^ m * hA'
      · have hhk' : h * k ∉ H := fun h' => hk ((hhk.1 h').1 hh)
        rw [detCocycle_of_not_mem_of_not_mem P c m hgh' hk,
          detCocycle_of_not_mem_of_not_mem P c m hg hhk']
        apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
        linear_combination (-1 : M) ^ m * (c g h : M) ^ m * (c (g * h) k : M) ^ m * hB' +
          (-1 : M) ^ m * ((g • GeneralLinearGroup.det (P (h * k)) : Mˣ) : M) *
            ((g • c h k : Mˣ) : M) ^ m * hA'
    · have hgh' : g * h ∈ H := hgh.2 (iff_of_false hg hh)
      rw [twistUnit_of_not_mem hh, smul_inv', smul_smul, mul_inv_eq_iff_eq_mul] at hB
      have hB' := congrArg Units.val hB
      simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hB'
      rw [detCocycle_of_not_mem_of_not_mem P c m hg hh, detCocycle_of_mem P c m hgh']
      by_cases hk : k ∈ H
      · have hhk' : h * k ∉ H := fun h' => hh ((hhk.1 h').2 hk)
        rw [detCocycle_of_not_mem_of_mem P c m hh hk,
          detCocycle_of_not_mem_of_not_mem P c m hg hhk', smul_mul', smul_pow', smul_smul]
        apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
        linear_combination (-1 : M) ^ m * (c g h : M) ^ m * (c (g * h) k : M) ^ m * hB' +
          (-1 : M) ^ m * ((g • GeneralLinearGroup.det (P (h * k)) : Mˣ) : M) *
            (((g * h) • GeneralLinearGroup.det (P k) : Mˣ) : M) * ((g • c h k : Mˣ) : M) ^ m * hA'
      · have hhk' : h * k ∈ H := hhk.2 (iff_of_false hh hk)
        rw [detCocycle_of_not_mem_of_not_mem P c m hh hk,
          detCocycle_of_not_mem_of_mem P c m hg hhk', smul_mul', smul_mul', smul_pow',
          smul_smul, smul_neg_one_pow]
        apply Units.ext
        simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
        linear_combination (-1 : M) ^ m * (c g h : M) ^ m * (c (g * h) k : M) ^ m * hB' +
          (-1 : M) ^ m * ((g • GeneralLinearGroup.det (P (h * k)) : Mˣ) : M) *
            (((g * h) • GeneralLinearGroup.det (P k) : Mˣ) : M) * ((g • c h k : Mˣ) : M) ^ m * hA'

/-- The square of the determinant factor set is the coboundary of the determinants of the
lifts. -/
theorem detCocycle_mul_self
    (P : (M ≃ₐ[F] M) → GL I M) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ) (m : ℕ)
    (hdet : ∀ g h, GeneralLinearGroup.det (P g) * twistUnit H g (GeneralLinearGroup.det (P h)) =
      c g h ^ (2 * m) * GeneralLinearGroup.det (P (g * h)))
    (g h : M ≃ₐ[F] M) :
    detCocycle H P c m g h * detCocycle H P c m g h =
      coboundary (fun t => GeneralLinearGroup.det (P t)) g h := by
  have hB := hdet g h
  have hS : ((-1 : M) ^ m) * (-1) ^ m = 1 := by
    rw [← mul_pow]
    norm_num
  rw [coboundary, eq_mul_inv_iff_mul_eq]
  by_cases hg : g ∈ H
  · rw [twistUnit_of_mem hg] at hB
    have hB' := congrArg Units.val hB
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hB'
    rw [detCocycle_of_mem P c m hg]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    linear_combination (-1 : M) * hB'
  · rw [twistUnit_of_not_mem hg, mul_inv_eq_iff_eq_mul] at hB
    have hB' := congrArg Units.val hB
    simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hB'
    by_cases hh : h ∈ H
    · rw [detCocycle_of_not_mem_of_mem P c m hg hh]
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val]
      linear_combination (-1 : M) * ((g • GeneralLinearGroup.det (P h) : Mˣ) : M) * hB'
    · rw [detCocycle_of_not_mem_of_not_mem P c m hg hh]
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
      linear_combination (-1 : M) * ((g • GeneralLinearGroup.det (P h) : Mˣ) : M) * hB' +
        (c g h : M) ^ (2 * m) * ((g • GeneralLinearGroup.det (P h) : Mˣ) : M) ^ 2 *
          (GeneralLinearGroup.det (P (g * h)) : M) * hS

/-- The determinant of the twisted projective cocycle law. -/
theorem det_mul_twistUnit (P : (M ≃ₐ[F] M) → GL I M) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ)
    (hc : ∀ g h, P g * twistGL H g (P h) = GeneralLinearGroup.scalar I (c g h) * P (g * h))
    (g h : M ≃ₐ[F] M) :
    GeneralLinearGroup.det (P g) * twistUnit H g (GeneralLinearGroup.det (P h)) =
      c g h ^ Fintype.card I * GeneralLinearGroup.det (P (g * h)) := by
  have h' := congrArg GeneralLinearGroup.det (hc g h)
  rwa [map_mul, map_mul, det_twistGL, GeneralLinearGroup.det_scalar] at h'

/-- The `m`-th power of the twisted cocycle identity for the factor set of a twisted projective
cocycle of size `2m`; for `m = 0` both sides are `1`. -/
theorem pow_twisted_of_lifts (hmul : ∀ g h : M ≃ₐ[F] M, g * h ∈ H ↔ (g ∈ H ↔ h ∈ H))
    (P : (M ≃ₐ[F] M) → GL I M) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ)
    (hc : ∀ g h, P g * twistGL H g (P h) = GeneralLinearGroup.scalar I (c g h) * P (g * h))
    (m : ℕ) (hcard : Fintype.card I = 2 * m) (g h k : M ≃ₐ[F] M) :
    (c g h * c (g * h) k) ^ m = (twistUnit H g (c h k) * c g (h * k)) ^ m := by
  rcases isEmpty_or_nonempty I with hI | hI
  · have hm : m = 0 := by
      have := Fintype.card_eq_zero (α := I)
      omega
    subst hm
    simp
  · rw [twisted_cocycle P c hc (twistGL_twistGL hmul) g h k]

/-- The determinant factor set of a twisted projective cocycle of size `2m` is a two-cocycle. -/
theorem detCocycle_isTwoCocycle_of_lifts (hmul : ∀ g h : M ≃ₐ[F] M, g * h ∈ H ↔ (g ∈ H ↔ h ∈ H))
    (P : (M ≃ₐ[F] M) → GL I M) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ)
    (hc : ∀ g h, P g * twistGL H g (P h) = GeneralLinearGroup.scalar I (c g h) * P (g * h))
    (m : ℕ) (hcard : Fintype.card I = 2 * m) : IsTwoCocycle (detCocycle H P c m) :=
  detCocycle_isTwoCocycle hmul P c m (pow_twisted_of_lifts hmul P c hc m hcard)
    (fun g h => by rw [← hcard]; exact det_mul_twistUnit P c hc g h)

/-- Rescaling the lifts by unit scalars `b` multiplies the determinant factor set by the
coboundary of `b^m`, for any factor sets of the two families. -/
theorem detCocycle_eq_coboundary_mul
    (P : (M ≃ₐ[F] M) → GL I M) (c : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ)
    (hc : ∀ g h, P g * twistGL H g (P h) = GeneralLinearGroup.scalar I (c g h) * P (g * h))
    (P' : (M ≃ₐ[F] M) → GL I M) (c' : (M ≃ₐ[F] M) → (M ≃ₐ[F] M) → Mˣ)
    (hc' : ∀ g h, P' g * twistGL H g (P' h) = GeneralLinearGroup.scalar I (c' g h) * P' (g * h))
    (m : ℕ) (hcard : Fintype.card I = 2 * m) (b : (M ≃ₐ[F] M) → Mˣ)
    (hb : ∀ g, P' g = GeneralLinearGroup.scalar I (b g) * P g) (g h : M ≃ₐ[F] M) :
    detCocycle H P' c' m g h = coboundary (fun t => b t ^ m) g h * detCocycle H P c m g h := by
  rcases isEmpty_or_nonempty I with hI | hI
  · have hm : m = 0 := by
      have := Fintype.card_eq_zero (α := I)
      omega
    subst hm
    have hdet (X : GL I M) : GeneralLinearGroup.det X = 1 := by
      ext
      simp [Matrix.det_isEmpty]
    simp [detCocycle, coboundary, hdet]
  -- the new factor set
  have hinj : Function.Injective (GeneralLinearGroup.scalar I : Mˣ →* GL I M) := by
    intro a a' haa
    apply Units.ext
    let p : I := Classical.choice inferInstance
    have he := congrArg (fun X : GL I M => (X : Matrix I I M) p p) haa
    simpa only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      using he
  have hc'' : c' g h * b (g * h) = b g * twistUnit H g (b h) * c g h := by
    apply hinj
    apply mul_right_cancel (b := P (g * h))
    have h1 := hc' g h
    rw [hb, hb, hb, twistGL_mul, twistGL_scalar] at h1
    calc GeneralLinearGroup.scalar I (c' g h * b (g * h)) * P (g * h)
        = GeneralLinearGroup.scalar I (c' g h) *
            (GeneralLinearGroup.scalar I (b (g * h)) * P (g * h)) := by
          rw [map_mul, mul_assoc]
      _ = GeneralLinearGroup.scalar I (b g) * P g *
            (GeneralLinearGroup.scalar I (twistUnit H g (b h)) * twistGL H g (P h)) := h1.symm
      _ = GeneralLinearGroup.scalar I (b g * twistUnit H g (b h)) *
            (P g * twistGL H g (P h)) := by
          rw [map_mul, mul_assoc, ← mul_assoc (P g),
            ← GeneralLinearGroup.scalar_commute (twistUnit H g (b h)) (P g)]
          simp only [mul_assoc]
      _ = GeneralLinearGroup.scalar I (b g * twistUnit H g (b h) * c g h) * P (g * h) := by
          rw [hc, ← mul_assoc, ← map_mul]
  have hdet : GeneralLinearGroup.det (P' h) = b h ^ (2 * m) * GeneralLinearGroup.det (P h) := by
    rw [hb, map_mul, GeneralLinearGroup.det_scalar, hcard]
  have hc3 : c' g h = b g * twistUnit H g (b h) * c g h * (b (g * h))⁻¹ := by
    rw [← hc'', mul_inv_cancel_right]
  by_cases hg : g ∈ H
  · rw [detCocycle_of_mem P' c' m hg, detCocycle_of_mem P c m hg, hc3, twistUnit_of_mem hg,
      coboundary]
    apply Units.ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, smul_pow']
    ring
  · rw [twistUnit_of_not_mem hg] at hc3
    by_cases hh : h ∈ H
    · rw [detCocycle_of_not_mem_of_mem P' c' m hg hh, detCocycle_of_not_mem_of_mem P c m hg hh,
        hc3, hdet, coboundary, smul_mul', smul_pow', smul_pow']
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
      have hu : (((g • b h : Mˣ) : M)⁻¹ * ((g • b h : Mˣ) : M)) ^ m = 1 := by
        rw [inv_mul_cancel₀ (Units.ne_zero _), one_pow]
      rw [← inv_pow]
      linear_combination ((b g : Mˣ) : M) ^ m * ((c g h : Mˣ) : M) ^ m *
        ((g • GeneralLinearGroup.det (P h) : Mˣ) : M) * ((b (g * h) : Mˣ) : M)⁻¹ ^ m *
        ((g • b h : Mˣ) : M) ^ m * hu
    · rw [detCocycle_of_not_mem_of_not_mem P' c' m hg hh,
        detCocycle_of_not_mem_of_not_mem P c m hg hh, hc3, hdet, coboundary, smul_mul',
        smul_pow', smul_pow']
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        Units.val_neg, Units.val_one]
      have hu : (((g • b h : Mˣ) : M)⁻¹ * ((g • b h : Mˣ) : M)) ^ m = 1 := by
        rw [inv_mul_cancel₀ (Units.ne_zero _), one_pow]
      rw [← inv_pow]
      linear_combination ((b g : Mˣ) : M) ^ m * ((c g h : Mˣ) : M) ^ m *
        ((g • GeneralLinearGroup.det (P h) : Mˣ) : M) * ((b (g * h) : Mˣ) : M)⁻¹ ^ m *
        ((g • b h : Mˣ) : M) ^ m * (-1 : M) ^ m * hu

end Langlands.UnitaryDiscriminant
