import Langlands.GroupScheme.Examples.HermitianRootElimination

/-! # Root-generated reflections for a finite Hermitian middle space -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {L : Type u} {ι : Type v}
  [Field L] [Fintype ι]
  {c : RingInvolution L} {H : DiagonalForm c ι}

namespace Parameters

/-- The left opposite parameter in the three-root reflection. -/
def leftOppositeParameter (x : Parameters H) (hx : x.scalar ≠ 0) : Parameters H :=
  ⟨(fun i => -x.vector i / c.bar x.scalar, (c.bar x.scalar)⁻¹), by
    have hbar : c.bar x.scalar ≠ 0 := by simpa using hx
    have hp :
        H.pairing (fun i => -x.vector i / c.bar x.scalar)
            (fun i => -x.vector i / c.bar x.scalar) =
          H.pairing x.vector x.vector / (c.bar x.scalar * x.scalar) := by
      simp only [DiagonalForm.pairing, map_div₀, map_neg, RingInvolution.bar_bar]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hp, ← x.equation]
    simp only [map_inv₀, RingInvolution.bar_bar]
    field_simp⟩

/-- The right opposite parameter in the three-root reflection. -/
def rightOppositeParameter (x : Parameters H) (hx : x.scalar ≠ 0) : Parameters H :=
  ⟨(fun i => -x.vector i / x.scalar, (c.bar x.scalar)⁻¹), by
    have hbar : c.bar x.scalar ≠ 0 := by simpa using hx
    have hp :
        H.pairing (fun i => -x.vector i / x.scalar)
            (fun i => -x.vector i / x.scalar) =
          H.pairing x.vector x.vector / (x.scalar * c.bar x.scalar) := by
      simp only [DiagonalForm.pairing, map_div₀, map_neg]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hp, ← x.equation]
    simp only [map_inv₀, RingInvolution.bar_bar]
    field_simp⟩

@[simp] theorem leftOppositeParameter_vector (x : Parameters H) (hx : x.scalar ≠ 0) :
    (leftOppositeParameter x hx).vector = fun i => -x.vector i / c.bar x.scalar := rfl

@[simp] theorem leftOppositeParameter_scalar (x : Parameters H) (hx : x.scalar ≠ 0) :
    (leftOppositeParameter x hx).scalar = (c.bar x.scalar)⁻¹ := rfl

@[simp] theorem rightOppositeParameter_vector (x : Parameters H) (hx : x.scalar ≠ 0) :
    (rightOppositeParameter x hx).vector = fun i => -x.vector i / x.scalar := rfl

@[simp] theorem rightOppositeParameter_scalar (x : Parameters H) (hx : x.scalar ≠ 0) :
    (rightOppositeParameter x hx).scalar = (c.bar x.scalar)⁻¹ := rfl

end Parameters

variable [DecidableEq ι]

/-- The rank-one modification of the middle identity associated with a root parameter. -/
def reflectionMiddle (x : Parameters H) : Matrix ι ι L :=
  1 - Matrix.of (fun i j => c.bar (x.vector i) * H.weight j * x.vector j / x.scalar)

/-- The block reflection matrix, with the rank-one modification in its middle block. -/
def reflectionMatrix (x : Parameters H) : Matrix (Index ι) (Index ι) L :=
  Matrix.fromBlocks 0
    (Matrix.of fun _ j => Sum.elim (fun _ => 0) (fun _ => x.scalar) j)
    (Matrix.of fun i _ => Sum.elim (fun _ => 0) (fun _ => (c.bar x.scalar)⁻¹) i)
    (Matrix.fromBlocks (reflectionMiddle x) 0 0 0)

/-- The actual invertible product of the three root factors. -/
def reflectionElement (x : Parameters H) (hx : x.scalar ≠ 0) :
    Matrix.GeneralLinearGroup (Index ι) L :=
  oppositeEmbedding H (Parameters.leftOppositeParameter x hx) *
    Parameters.embedding H x *
    oppositeEmbedding H (Parameters.rightOppositeParameter x hx)

theorem reflectionElement_mem_elementarySubgroup (x : Parameters H) (hx : x.scalar ≠ 0) :
    reflectionElement x hx ∈ elementarySubgroup H :=
  (elementarySubgroup H).mul_mem
    ((elementarySubgroup H).mul_mem
      (oppositeEmbedding_mem_elementarySubgroup H _)
      (embedding_mem_elementarySubgroup H x))
    (oppositeEmbedding_mem_elementarySubgroup H _)

theorem reflectionElement_mem_specialUnitarySubgroup
    (x : Parameters H) (hx : x.scalar ≠ 0) :
    reflectionElement x hx ∈ specialUnitarySubgroup H :=
  elementarySubgroup_le_specialUnitarySubgroup H
    (reflectionElement_mem_elementarySubgroup x hx)

theorem reflectionElement_val (x : Parameters H) (hx : x.scalar ≠ 0) :
    (reflectionElement x hx : Matrix (Index ι) (Index ι) L) = reflectionMatrix x := by
  have hbar : c.bar x.scalar ≠ 0 := by simpa using hx
  have hq : (∑ k, H.weight k * x.vector k * c.bar (x.vector k)) =
      x.scalar + c.bar x.scalar := x.equation.symm
  have hs₁ : (∑ k, H.weight k * x.vector k *
        (-c.bar (x.vector k) / c.bar x.scalar)) =
      -(x.scalar + c.bar x.scalar) / c.bar x.scalar := by
    calc
      _ = -(∑ k, H.weight k * x.vector k * c.bar (x.vector k)) /
          c.bar x.scalar := by
        rw [← Finset.sum_neg_distrib, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hq]
  have hs₂ : (∑ k, H.weight k * (-x.vector k / c.bar x.scalar) *
        c.bar (x.vector k)) = -(x.scalar + c.bar x.scalar) / c.bar x.scalar := by
    rw [← hs₁]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hs₃ (i : ι) : (∑ k,
        (-c.bar (x.vector i) / x.scalar * (H.weight k * x.vector k) +
          if i = k then 1 else 0) * (-c.bar (x.vector k) / c.bar x.scalar)) =
      c.bar (x.vector i) * (x.scalar + c.bar x.scalar) /
        (x.scalar * c.bar x.scalar) - c.bar (x.vector i) / c.bar x.scalar := by
    simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    have hs : (∑ k, -c.bar (x.vector i) / x.scalar *
          (H.weight k * x.vector k) * (-c.bar (x.vector k) / c.bar x.scalar)) =
        c.bar (x.vector i) * (x.scalar + c.bar x.scalar) /
          (x.scalar * c.bar x.scalar) := by
      calc
        _ = c.bar (x.vector i) / (x.scalar * c.bar x.scalar) *
            (∑ k, H.weight k * x.vector k * c.bar (x.vector k)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          ring
        _ = _ := by rw [hq]; ring
    rw [hs]
    ring
  have hc (k : ι) : (c.bar x.scalar)⁻¹ * (H.weight k * x.vector k) +
      H.weight k * (-x.vector k / c.bar x.scalar) = 0 := by ring
  ext i j
  change ((oppositeEmbedding H (Parameters.leftOppositeParameter x hx) :
      Matrix (Index ι) (Index ι) L) * Parameters.matrix x *
      (oppositeEmbedding H (Parameters.rightOppositeParameter x hx) :
        Matrix (Index ι) (Index ι) L)) i j = _
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, oppositeEmbedding_apply,
      Parameters.matrix, Matrix.fromBlocks, swapIndex, Matrix.one_apply,
      reflectionMatrix, reflectionMiddle, map_div₀, hs₁, hs₂, hs₃, hc] <;>
    (try simp only [← x.equation]) <;> field_simp <;> ring_nf <;> simp only [true_or]

end Langlands.GroupScheme.HermitianRoot
