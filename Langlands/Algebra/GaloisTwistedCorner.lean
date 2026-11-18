import Langlands.Algebra.GaloisTwistedCompression
import Langlands.Algebra.CentralSimpleCorner

/-! # Brauer class of a compressed twisted-fixed algebra -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {N r : Type} [Fintype N] [DecidableEq N] [Fintype r] [DecidableEq r]

/-- The idempotent `E F` of `B` attached to a compression. -/
theorem isIdempotentElem_compression (B : Subalgebra k (Matrix N N K)) (F : Matrix r N K)
    (E : Matrix N r K) (hFE : F * E = 1) (hf : E * F ∈ B) :
    IsIdempotentElem (⟨E * F, hf⟩ : B) := by
  apply Subtype.ext
  change E * F * (E * F) = E * F
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc F, hFE, Matrix.one_mul]

theorem mul_mem_of_mem_compressed {B : Subalgebra k (Matrix N N K)} {F : Matrix r N K}
    {E : Matrix N r K} {hFE : F * E = 1} {hf : E * F ∈ B} {z : Matrix r r K}
    (hz : z ∈ compressed B F E hFE hf) : E * z * F ∈ B := by
  obtain ⟨x, hx, rfl⟩ := hz
  have : E * (F * x * E) * F = (E * F) * x * (E * F) := by simp only [Matrix.mul_assoc]
  rw [this]
  exact B.mul_mem (B.mul_mem hf hx) hf

/-- The compression `{F x E | x ∈ B}` is isomorphic to the corner `(E F) B (E F)`. -/
def compressedEquivCorner (B : Subalgebra k (Matrix N N K)) (F : Matrix r N K)
    (E : Matrix N r K) (hFE : F * E = 1) (hf : E * F ∈ B) :
    compressed B F E hFE hf ≃ₐ[k] (isIdempotentElem_compression B F E hFE hf).Corner :=
  AlgEquiv.ofRingEquiv (f := {
    toFun := fun z => ⟨⟨E * z.1 * F, mul_mem_of_mem_compressed z.2⟩, by
      rw [Subsemigroup.mem_corner_iff (isIdempotentElem_compression B F E hFE hf)]
      constructor
      · apply Subtype.ext
        change E * F * (E * z.1 * F) = E * z.1 * F
        rw [Matrix.mul_assoc E F, ← Matrix.mul_assoc F, ← Matrix.mul_assoc F, hFE,
          Matrix.one_mul, ← Matrix.mul_assoc]
      · apply Subtype.ext
        change E * z.1 * F * (E * F) = E * z.1 * F
        rw [← Matrix.mul_assoc, Matrix.mul_assoc (E * z.1) F E, hFE, Matrix.mul_one]⟩
    invFun := fun c => ⟨F * c.1.1 * E, mem_compressed c.1.2⟩
    left_inv := by
      intro z
      apply Subtype.ext
      change F * (E * z.1 * F) * E = z.1
      simp only [← Matrix.mul_assoc, hFE, Matrix.one_mul]
      rw [Matrix.mul_assoc, hFE, Matrix.mul_one]
    right_inv := by
      intro c
      have hc := (Subsemigroup.mem_corner_iff (isIdempotentElem_compression B F E hFE hf)).mp c.2
      have h1 : E * F * c.1.1 = c.1.1 := congrArg Subtype.val hc.1
      have h2 : c.1.1 * (E * F) = c.1.1 := congrArg Subtype.val hc.2
      apply Subtype.ext
      apply Subtype.ext
      change E * (F * c.1.1 * E) * F = c.1.1
      calc E * (F * c.1.1 * E) * F = E * F * c.1.1 * (E * F) := by simp only [Matrix.mul_assoc]
        _ = c.1.1 := by rw [h1, h2]
    map_mul' := by
      intro z w
      apply Subtype.ext
      apply Subtype.ext
      change E * (z.1 * w.1) * F = E * z.1 * F * (E * w.1 * F)
      calc E * (z.1 * w.1) * F = E * z.1 * (F * E) * w.1 * F := by
            rw [hFE, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = E * z.1 * F * (E * w.1 * F) := by simp only [Matrix.mul_assoc]
    map_add' := by
      intro z w
      apply Subtype.ext
      apply Subtype.ext
      change E * (z.1 + w.1) * F = E * z.1 * F + E * w.1 * F
      rw [Matrix.mul_add, Matrix.add_mul] })
    (by
      intro c
      apply Subtype.ext
      apply Subtype.ext
      have h := Langlands.Brauer.cornerInclusion_algebraMap (K := k)
        (isIdempotentElem_compression B F E hFE hf) c
      rw [Langlands.Brauer.cornerInclusion_apply] at h
      rw [h]
      change E * (algebraMap k (Matrix r r K) c) * F = c • (E * F)
      rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one])

theorem compression_ne_zero [Nonempty r] (B : Subalgebra k (Matrix N N K)) (F : Matrix r N K)
    (E : Matrix N r K) (hFE : F * E = 1) (hf : E * F ∈ B) : (⟨E * F, hf⟩ : B) ≠ 0 := by
  intro h
  have h0 : E * F = 0 := congrArg Subtype.val h
  have : (1 : Matrix r r K) = 0 := by
    calc (1 : Matrix r r K) = F * E * (F * E) := by rw [hFE, Matrix.one_mul]
      _ = F * (E * F) * E := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [h0, Matrix.mul_zero, Matrix.zero_mul]
  exact one_ne_zero this

variable [IsGalois k K]

/-- A compression of a twisted-fixed central simple `k`-form along `F E = 1` with `E F` in the
form is Brauer equivalent to the form (corner theorem). -/
theorem isBrauerEquivalent_toCSA_compressed [Nonempty N] [Nonempty r]
    (P : (K ≃ₐ[k] K) → Matrix N N K) (hP : ∀ σ, IsUnit (P σ))
    (B : Subalgebra k (Matrix N N K)) (hB : B ≤ twistedFixed P)
    (hspan : Submodule.span K (B : Set (Matrix N N K)) = ⊤)
    (F : Matrix r N K) (E : Matrix N r K) (hFE : F * E = 1) (hf : E * F ∈ B) :
    IsBrauerEquivalent
      (toCSA (fun σ => F.map σ * P σ * E) (isUnit_compressed_twist hB hP F E hFE hf)
        (compressed B F E hFE hf) (compressed_le_twistedFixed hB F E hFE hf)
        (span_compressed hspan F E hFE hf))
      (toCSA P hP B hB hspan) := by
  have he := isIdempotentElem_compression B F E hFE hf
  have hne := compression_ne_zero B F E hFE hf
  have h1 : IsBrauerEquivalent
      (toCSA (fun σ => F.map σ * P σ * E) (isUnit_compressed_twist hB hP F E hFE hf)
        (compressed B F E hFE hf) (compressed_le_twistedFixed hB F E hFE hf)
        (span_compressed hspan F E hFE hf))
      (Langlands.Brauer.cornerCSA (toCSA P hP B hB hspan) (e := (⟨E * F, hf⟩ : B)) he hne) :=
    ⟨1, 1, one_ne_zero, one_ne_zero, ⟨(compressedEquivCorner B F E hFE hf).mapMatrix⟩⟩
  exact h1.trans (Langlands.Brauer.isBrauerEquivalent_cornerCSA _ he hne)

end Langlands.Algebra.GaloisTwistedMatrix
