import Langlands.Algebra.GaloisTwistedMatrix

/-! # Compressions of twisted-fixed matrix algebras -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.Algebra.GaloisTwistedMatrix

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
  {N r : Type} [Fintype N] [DecidableEq N] [Fintype r] [DecidableEq r]

/-- The compression `{F x E | x ∈ B}` of a subalgebra `B ⊆ M_N(K)` along rectangular matrices with
`F E = 1` and `E F ∈ B`. It is a subalgebra of `M_r(K)`. -/
def compressed (B : Subalgebra k (Matrix N N K)) (F : Matrix r N K) (E : Matrix N r K)
    (hFE : F * E = 1) (hf : E * F ∈ B) : Subalgebra k (Matrix r r K) where
  carrier := {z | ∃ x ∈ B, F * x * E = z}
  mul_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    refine ⟨x * (E * F) * y, B.mul_mem (B.mul_mem hx hf) hy, ?_⟩
    simp only [Matrix.mul_assoc]
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x + y, B.add_mem hx hy, by rw [Matrix.mul_add, Matrix.add_mul]⟩
  algebraMap_mem' c := by
    refine ⟨algebraMap k (Matrix N N K) c, B.algebraMap_mem c, ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hFE]

theorem mem_compressed {B : Subalgebra k (Matrix N N K)} {F : Matrix r N K} {E : Matrix N r K}
    {hFE : F * E = 1} {hf : E * F ∈ B} {x : Matrix N N K} (hx : x ∈ B) :
    F * x * E ∈ compressed B F E hFE hf :=
  ⟨x, hx, rfl⟩

/-- The compression of a twisted-fixed algebra is twisted-fixed for the compressed twisting
matrices `σ(F) P σ E`. -/
theorem compressed_le_twistedFixed {B : Subalgebra k (Matrix N N K)}
    {P : (K ≃ₐ[k] K) → Matrix N N K} (hB : B ≤ twistedFixed P)
    (F : Matrix r N K) (E : Matrix N r K) (hFE : F * E = 1) (hf : E * F ∈ B) :
    compressed B F E hFE hf ≤ twistedFixed (fun σ => F.map σ * P σ * E) := by
  rintro _ ⟨x, hx, rfl⟩ σ
  have hfσ := hB hf σ
  have hxσ := hB hx σ
  have hF : F * (E * F) = F := by rw [← Matrix.mul_assoc, hFE, Matrix.one_mul]
  have hE : (E * F) * E = E := by rw [Matrix.mul_assoc, hFE, Matrix.mul_one]
  -- left side: σ(F) P (E F) x E = σ(F) σ(E F) P x E = σ(F) P x E
  have hL : F.map σ * P σ * E * (F * x * E) = F.map σ * P σ * x * E := by
    calc F.map σ * P σ * E * (F * x * E) = F.map σ * (P σ * (E * F)) * x * E := by
          simp only [Matrix.mul_assoc]
      _ = F.map σ * ((E * F).map σ * P σ) * x * E := by rw [hfσ]
      _ = (F * (E * F)).map σ * P σ * x * E := by
          simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = F.map σ * P σ * x * E := by rw [hF]
  have hR : (F * x * E).map σ * (F.map σ * P σ * E) = F.map σ * P σ * x * E := by
    calc (F * x * E).map σ * (F.map σ * P σ * E)
        = F.map σ * x.map σ * ((E * F).map σ * P σ) * E := by
          simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = F.map σ * x.map σ * (P σ * (E * F)) * E := by rw [hfσ]
      _ = F.map σ * (x.map σ * P σ) * ((E * F) * E) := by simp only [Matrix.mul_assoc]
      _ = F.map σ * P σ * x * E := by rw [← hxσ, hE]; simp only [Matrix.mul_assoc]
  rw [hL, hR]

/-- The compressed twisting matrices are invertible. -/
theorem isUnit_compressed_twist {B : Subalgebra k (Matrix N N K)}
    {P : (K ≃ₐ[k] K) → Matrix N N K} (hB : B ≤ twistedFixed P) (hP : ∀ σ, IsUnit (P σ))
    (F : Matrix r N K) (E : Matrix N r K) (hFE : F * E = 1) (hf : E * F ∈ B)
    (σ : K ≃ₐ[k] K) : IsUnit (F.map σ * P σ * E) := by
  have hfσ := hB hf σ
  have hPinv : P σ * (P σ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (hP σ))
  have hinv : (F.map σ * P σ * E) * (F * (P σ)⁻¹ * E.map σ) = 1 := by
    calc (F.map σ * P σ * E) * (F * (P σ)⁻¹ * E.map σ)
        = F.map σ * (P σ * (E * F)) * (P σ)⁻¹ * E.map σ := by simp only [Matrix.mul_assoc]
      _ = F.map σ * ((E * F).map σ * P σ) * (P σ)⁻¹ * E.map σ := by rw [hfσ]
      _ = F.map σ * (E * F).map σ * (P σ * (P σ)⁻¹) * E.map σ := by
          simp only [Matrix.mul_assoc]
      _ = (F * (E * F) * E).map σ := by
          rw [hPinv, Matrix.mul_one]
          simp only [Matrix.map_mul, Matrix.mul_assoc]
      _ = 1 := by
          rw [show F * (E * F) * E = 1 by
            rw [← Matrix.mul_assoc, hFE, Matrix.one_mul, hFE]]
          exact Matrix.map_one _ (map_zero σ) (map_one σ)
  exact ⟨⟨_, _, hinv, mul_eq_one_comm.mp hinv⟩, rfl⟩

/-- If `B` spans `M_N(K)`, its compression spans `M_r(K)`. -/
theorem span_compressed {B : Subalgebra k (Matrix N N K)}
    (hspan : Submodule.span K (B : Set (Matrix N N K)) = ⊤)
    (F : Matrix r N K) (E : Matrix N r K) (hFE : F * E = 1) (hf : E * F ∈ B) :
    Submodule.span K (compressed B F E hFE hf : Set (Matrix r r K)) = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have hz : E * z * F ∈ Submodule.span K (B : Set (Matrix N N K)) := by rw [hspan]; trivial
  have key : ∀ x ∈ Submodule.span K (B : Set (Matrix N N K)),
      F * x * E ∈ Submodule.span K (compressed B F E hFE hf : Set (Matrix r r K)) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (mem_compressed hx)
    | zero => simp
    | add x y _ _ h1 h2 => rw [Matrix.mul_add, Matrix.add_mul]; exact Submodule.add_mem _ h1 h2
    | smul c x _ h1 => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ c h1
  have := key _ hz
  rwa [show F * (E * z * F) * E = z by
    simp only [← Matrix.mul_assoc, hFE, Matrix.one_mul]
    rw [Matrix.mul_assoc, hFE, Matrix.mul_one]] at this

end Langlands.Algebra.GaloisTwistedMatrix
