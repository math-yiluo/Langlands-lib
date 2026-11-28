import Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier

/-!
# Invariant pairings and the idempotent decomposition

The two off-diagonal corners for an idempotent `e` are isotropic, and each is orthogonal
to the centralizer of `e`. An invariant pairing restricts to an invariant
pairing on the centralizer and gives a nondegenerate pairing between the opposite corners.
These identities give the decomposition of the Fourier kernel used in Harish-Chandra's
parabolic descent (1999, §1.2, Lemma 1.4).
-/

noncomputable section

namespace Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer

universe u v

variable (F : Type u) [Field F] {A : Type v} [Ring A] [Algebra F A]

/-- The projection `x ↦ e x (1 - e)` when `e` is idempotent. -/
def cornerProjection (e : A) : A →ₗ[F] A :=
  (LinearMap.mulRight F (1 - e)).comp (LinearMap.mulLeft F e)

theorem cornerProjection_apply (e x : A) : cornerProjection F e x = e * x * (1 - e) := rfl

/-- The off-diagonal corner `e A (1 - e)`. Its opposite corner is `offDiagonalCorner F (1 - e)`. -/
def offDiagonalCorner (e : A) : Submodule F A := (cornerProjection F e).range

theorem cornerProjection_mem (e x : A) : cornerProjection F e x ∈ offDiagonalCorner F e :=
  LinearMap.mem_range_self _ _

theorem diagonal_add_corners (e x : A) :
    diagonalProjection F e x + cornerProjection F e x + cornerProjection F (1 - e) x = x := by
  simp only [diagonalProjection_apply, cornerProjection_apply, sub_sub_cancel]
  noncomm_ring

variable {F} {e : A}

private theorem scaling_mul (he : IsIdempotentElem e) {s t : F} (hst : s * t = 1) :
    (s • e + (1 - e)) * (t • e + (1 - e)) = 1 := by
  obtain ⟨h₁, h₂, h₃, h₄, _, _, _, _⟩ := idempotent_mul_rules he
  have hts : t * s = 1 := (mul_comm _ _).trans hst
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, h₁, h₂, h₃, h₄,
    smul_zero, add_zero, zero_add, hts, one_smul]
  abel

/-- The diagonal unit acting by the scalar `t` on the `e` block and by `1` on the complement. -/
private def scalingUnit (he : IsIdempotentElem e) (t : Fˣ) : Aˣ where
  val := (t : F) • e + (1 - e)
  inv := ((t⁻¹ : Fˣ) : F) • e + (1 - e)
  val_inv := scaling_mul he t.val_inv
  inv_val := scaling_mul he t.inv_val

private theorem scalingUnit_conj_of_commute (he : IsIdempotentElem e) (t : Fˣ)
    {x : A} (hx : e * x = x * e) :
    (scalingUnit he t : A) * x * ((scalingUnit he t)⁻¹ : Aˣ).val = x := by
  have h : (scalingUnit he t : A) * x = x * (scalingUnit he t : A) := by
    change ((t : F) • e + (1 - e)) * x = x * ((t : F) • e + (1 - e))
    rw [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, one_mul, mul_one, hx]
  rw [h, mul_assoc, Units.mul_inv, mul_one]

private theorem scalingUnit_conj_corner (he : IsIdempotentElem e) (t : Fˣ)
    {x : A} (hx : x ∈ offDiagonalCorner F e) :
    (scalingUnit he t : A) * x * ((scalingUnit he t)⁻¹ : Aˣ).val = (t : F) • x := by
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨h₁, h₂, h₃, h₄, _, _, _, _⟩ := idempotent_mul_rules he
  change ((t : F) • e + (1 - e)) * (e * y * (1 - e)) *
    (((t⁻¹ : Fˣ) : F) • e + (1 - e)) = (t : F) • (e * y * (1 - e))
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, ← mul_assoc, h₁, h₂, zero_mul]
  simp only [mul_assoc, h₂, h₄, mul_zero, smul_zero, zero_add, add_zero]

variable {B : LinearMap.BilinForm F A}

private theorem pairing_eq_zero_of_weights (hB : IsInvariantPairing B) (g : Aˣ) {x y : A}
    {a b : F} (hx : (g : A) * x * ((g⁻¹ : Aˣ) : A) = a • x)
    (hy : (g : A) * y * ((g⁻¹ : Aˣ) : A) = b • y) (hab : a * b ≠ 1) : B x y = 0 := by
  have h := hB.conj_invariant g x y
  rw [hx, hy, LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, ← mul_assoc] at h
  have hzero : (a * b - 1) * B x y = 0 := by rwa [sub_mul, one_mul, sub_eq_zero]
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hab)

private theorem mem_centralizer_one_sub {x : A}
    (hx : x ∈ Subalgebra.centralizer F ({e} : Set A)) :
    x ∈ Subalgebra.centralizer F ({1 - e} : Set A) := by
  rw [mem_centralizer_singleton_iff] at hx ⊢
  rw [sub_mul, mul_sub, one_mul, mul_one, hx]

variable [CharZero F]

/-- The centralizer of `e` is orthogonal to the corner `e A (1 - e)`. -/
theorem pairing_centralizer_corner_eq_zero (he : IsIdempotentElem e) (hB : IsInvariantPairing B)
    {x y : A} (hx : x ∈ Subalgebra.centralizer F ({e} : Set A))
    (hy : y ∈ offDiagonalCorner F e) : B x y = 0 := by
  let t := Units.mk0 (2 : F) two_ne_zero
  apply pairing_eq_zero_of_weights hB (scalingUnit he t) (a := 1) (b := 2)
  · simpa only [one_smul] using
      scalingUnit_conj_of_commute he t ((mem_centralizer_singleton_iff F).mp hx)
  · exact scalingUnit_conj_corner he t hy
  · norm_num

/-- The corner `e A (1 - e)` is isotropic for the invariant pairing. -/
theorem pairing_corner_eq_zero (he : IsIdempotentElem e) (hB : IsInvariantPairing B)
    {x y : A} (hx : x ∈ offDiagonalCorner F e) (hy : y ∈ offDiagonalCorner F e) : B x y = 0 := by
  let t := Units.mk0 (2 : F) two_ne_zero
  exact pairing_eq_zero_of_weights hB (scalingUnit he t)
    (scalingUnit_conj_corner he t hx) (scalingUnit_conj_corner he t hy) (by norm_num [t])

/-- The restriction of an invariant pairing to the centralizer of an idempotent is invariant. -/
theorem invariantPairing_centralizer (he : IsIdempotentElem e) (hB : IsInvariantPairing B) :
    IsInvariantPairing (A := Subalgebra.centralizer F ({e} : Set A))
      (B.restrict (Subalgebra.centralizer F ({e} : Set A)).toSubmodule) := by
  let M := Subalgebra.centralizer F ({e} : Set A)
  change IsInvariantPairing (A := M) (B.restrict M.toSubmodule)
  have hleft : (B.restrict M.toSubmodule).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    change (x : A) = 0
    apply hB.nondegenerate.1 (x : A)
    intro y
    have hy : diagonalProjection F e y ∈ M :=
      (mem_centralizer_singleton_iff F).mpr (commute_diagonalProjection he y)
    conv_lhs => rw [← diagonal_add_corners F e y]
    rw [B.add_right, B.add_right]
    rw [show B (x : A) (diagonalProjection F e y) = 0 from hx ⟨_, hy⟩,
      pairing_centralizer_corner_eq_zero he hB x.2 (cornerProjection_mem F e y),
      pairing_centralizer_corner_eq_zero he.one_sub hB (mem_centralizer_one_sub x.2)
        (cornerProjection_mem F (1 - e) y)]
    simp
  refine ⟨hB.isSymm.restrict M.toSubmodule, ⟨hleft, ?_⟩, ?_⟩
  · intro x hx
    apply hleft x
    intro y
    exact (hB.isSymm.eq (x : A) (y : A)).trans (hx y)
  · intro u x y
    exact hB.conj_invariant (Units.map M.subtype.toMonoidHom u) (x : A) (y : A)

private theorem opposite_corner_separatingLeft (he : IsIdempotentElem e)
    (hB : IsInvariantPairing B) :
    (B.domRestrict₁₂ (offDiagonalCorner F e) (offDiagonalCorner F (1 - e))).SeparatingLeft := by
  intro x hx
  apply Subtype.ext
  change (x : A) = 0
  apply hB.nondegenerate.1 (x : A)
  intro y
  have hy : diagonalProjection F e y ∈ Subalgebra.centralizer F ({e} : Set A) :=
    (mem_centralizer_singleton_iff F).mpr (commute_diagonalProjection he y)
  conv_lhs => rw [← diagonal_add_corners F e y]
  rw [B.add_right, B.add_right, hB.isSymm.eq (x : A) (diagonalProjection F e y),
    pairing_centralizer_corner_eq_zero he hB hy x.2,
    pairing_corner_eq_zero he hB x.2 (cornerProjection_mem F e y),
    show B (x : A) (cornerProjection F (1 - e) y) = 0 from hx ⟨_, cornerProjection_mem F _ _⟩]
  simp

/-- The restrictions to the two opposite corners give a nondegenerate bilinear map. -/
theorem opposite_corner_nondegenerate (he : IsIdempotentElem e) (hB : IsInvariantPairing B) :
    (B.domRestrict₁₂ (offDiagonalCorner F e) (offDiagonalCorner F (1 - e))).Nondegenerate := by
  refine ⟨opposite_corner_separatingLeft he hB, ?_⟩
  have h := opposite_corner_separatingLeft he.one_sub hB
  rw [sub_sub_cancel] at h
  intro y hy
  apply h y
  intro x
  exact (hB.isSymm.eq (y : A) (x : A)).trans (hy x)

/-- The invariant pairing on a block upper triangular element and an arbitrary element
in block coordinates, as used in the Fourier transform of the constant term. -/
theorem pairing_add_corners (he : IsIdempotentElem e) (hB : IsInvariantPairing B)
    (x y : Subalgebra.centralizer F ({e} : Set A))
    (z w : offDiagonalCorner F e) (wOpp : offDiagonalCorner F (1 - e)) :
    B ((x : A) + z) ((y : A) + w + wOpp) = B x y + B z wOpp := by
  simp only [B.add_left, B.add_right,
    pairing_centralizer_corner_eq_zero he hB x.2 w.2,
    pairing_centralizer_corner_eq_zero he.one_sub hB (mem_centralizer_one_sub x.2) wOpp.2,
    (hB.isSymm.eq (z : A) (y : A)).trans (pairing_centralizer_corner_eq_zero he hB y.2 z.2),
    pairing_corner_eq_zero he hB z.2 w.2, zero_add, add_zero]

end Langlands.HarmonicAnalysis.UnitConjugation.IdempotentCentralizer
