import Mathlib.FieldTheory.Fixed
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! # Galois descent of semilinear vector spaces and Hilbert 90 for matrices -/

noncomputable section

universe u v w

namespace Langlands.LinearAlgebra.GaloisVectorDescent

open Matrix

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable (H : Subgroup (L ≃ₐ[k] L))

/-- Dedekind independence: a vanishing combination of the automorphisms in a finite
subgroup has zero coefficients. -/
theorem coeff_eq_zero_of_sum_eq_zero [Fintype H] (g : H → L)
    (hg : ∀ a : L, ∑ σ : H, g σ * σ.val a = 0) (σ : H) : g σ = 0 := by
  have hinj : Function.Injective (fun τ : H => ((τ.val : L ≃ₐ[k] L) : L →ₐ[k] L)) := by
    intro τ ρ h
    apply Subtype.ext
    ext x
    exact DFunLike.congr_fun h x
  have hli := (linearIndependent_toLinearMap k L L).comp _ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hli g _ σ
  apply LinearMap.ext
  intro a
  simpa [Function.comp_def] using hg a

variable [Finite H] {V : Type v} [AddCommGroup V] [Module L V]

/-- The vectors fixed by a semilinear action of a finite automorphism group span the
whole space over the larger field. -/
theorem span_fixed_eq_top (f : H → V →+ V) (hone : ∀ v, f 1 v = v)
    (hmul : ∀ σ τ v, f (σ * τ) v = f σ (f τ v))
    (hsmul : ∀ σ (a : L) v, f σ (a • v) = σ.val a • f σ v) :
    Submodule.span L {v : V | ∀ σ, f σ v = v} = ⊤ := by
  classical
  have : Fintype H := Fintype.ofFinite H
  by_contra hne
  obtain ⟨φ, hφ, hle⟩ :=
    Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  apply hφ
  apply LinearMap.ext
  intro v
  have htr (w : V) : (∑ τ : H, f τ w) ∈ {v : V | ∀ σ, f σ v = v} := by
    intro σ
    rw [map_sum]
    exact Fintype.sum_bijective (σ * ·) (Group.mulLeft_bijective σ) _ _
      (fun τ => (hmul σ τ w).symm)
  have hφtr (a : L) : ∑ τ : H, φ (f τ v) * τ.val a = 0 := by
    have h := hle (Submodule.subset_span (htr (a • v)))
    rw [LinearMap.mem_ker, map_sum] at h
    simpa only [hsmul, map_smul, smul_eq_mul, mul_comm] using h
  have h1 := coeff_eq_zero_of_sum_eq_zero H (fun τ => φ (f τ v)) hφtr 1
  simpa [hone] using h1

/-- A semilinear action of a finite automorphism group has a basis of fixed vectors. -/
theorem exists_fixed_basis (f : H → V →+ V) (hone : ∀ v, f 1 v = v)
    (hmul : ∀ σ τ v, f (σ * τ) v = f σ (f τ v))
    (hsmul : ∀ σ (a : L) v, f σ (a • v) = σ.val a • f σ v) :
    ∃ (s : Set V) (b : Module.Basis s L V), ∀ i σ, f σ (b i) = b i := by
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent L {v : V | ∀ σ, f σ v = v}
  refine ⟨s, Module.Basis.mk hli ?_, ?_⟩
  · rw [Subtype.range_coe, hspan, span_fixed_eq_top H f hone hmul hsmul]
  · intro i σ
    rw [Module.Basis.mk_apply]
    exact hs i.2 σ

variable {n : Type w} [Fintype n] [DecidableEq n]

/-- Hilbert 90 for `GL_n`: a matrix cocycle of a finite automorphism group is a
coboundary, in the form `c σ * σ(P) = P` with `P` invertible. -/
theorem exists_matrix_coboundary (c : H → Matrix n n L) (hc1 : c 1 = 1)
    (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val) :
    ∃ P : GL n L, ∀ σ, c σ * (P : Matrix n n L).map σ.val = P := by
  classical
  let f : H → (n → L) →+ (n → L) := fun σ =>
    { toFun := fun v => c σ *ᵥ (fun i => σ.val (v i))
      map_zero' := by
        change c σ *ᵥ (fun i => σ.val ((0 : n → L) i)) = 0
        simp only [Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero (c σ)
      map_add' := by
        intro v w
        change c σ *ᵥ (fun i => σ.val ((v + w) i)) =
          c σ *ᵥ (fun i => σ.val (v i)) + c σ *ᵥ (fun i => σ.val (w i))
        rw [← Matrix.mulVec_add]
        congr 1
        funext i
        simp }
  have hf (σ : H) (v : n → L) : f σ v = c σ *ᵥ (fun i => σ.val (v i)) := rfl
  have hone : ∀ v, f 1 v = v := by
    intro v
    simp [hf, hc1]
  have hmul : ∀ σ τ v, f (σ * τ) v = f σ (f τ v) := by
    intro σ τ v
    rw [hf, hf, hf, hc, ← Matrix.mulVec_mulVec]
    congr 1
    funext i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
      Subgroup.coe_mul, AlgEquiv.mul_apply]
  have hsmul : ∀ σ (a : L) v, f σ (a • v) = σ.val a • f σ v := by
    intro σ a v
    rw [hf, hf, ← Matrix.mulVec_smul]
    congr 1
    funext i
    simp
  obtain ⟨s, b, hb⟩ := exists_fixed_basis H f hone hmul hsmul
  let e : s ≃ n := b.indexEquiv (Pi.basisFun L n)
  let b₂ : Module.Basis n L (n → L) := b.reindex e
  have hb₂ (j : n) (σ : H) : f σ (b₂ j) = b₂ j := by
    simp only [b₂, Module.Basis.reindex_apply]
    exact hb _ σ
  let P : Matrix n n L := (Pi.basisFun L n).toMatrix b₂
  have hP (i j : n) : P i j = b₂ j i := by
    simp [P, Module.Basis.toMatrix_apply]
  let _ : Invertible P := (Pi.basisFun L n).invertibleToMatrix b₂
  refine ⟨unitOfInvertible P, fun σ => ?_⟩
  ext i j
  have h := congrFun (hb₂ j σ) i
  rw [hf] at h
  simp only [unitOfInvertible, Matrix.mul_apply, Matrix.map_apply, hP]
  simpa [Matrix.mulVec, dotProduct] using h

omit [Finite H] in
/-- An equation `c * σ(P) = P` with `P` invertible is the coboundary form
`c = P * σ(P⁻¹)`. -/
theorem eq_mul_map_inv_of_mul_map_eq (σ : L ≃ₐ[k] L) {c : Matrix n n L} (P : GL n L)
    (h : c * (P : Matrix n n L).map σ = P) :
    c = (P : Matrix n n L) * ((P⁻¹ : GL n L) : Matrix n n L).map σ := by
  have hmap : ∀ A B : Matrix n n L, (A * B).map σ = A.map σ * B.map σ :=
    fun A B => Matrix.map_mul (f := ((σ : L ≃ₐ[k] L) : L →+* L))
  have hinv : (P : Matrix n n L).map σ * ((P⁻¹ : GL n L) : Matrix n n L).map σ = 1 := by
    rw [← hmap, Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  calc c = c * ((P : Matrix n n L).map σ *
        ((P⁻¹ : GL n L) : Matrix n n L).map σ) := by rw [hinv, Matrix.mul_one]
    _ = (P : Matrix n n L) * ((P⁻¹ : GL n L) : Matrix n n L).map σ := by
        rw [← Matrix.mul_assoc, h]

/-- The coboundary form `c σ = P * σ(P⁻¹)` of matrix Hilbert 90. -/
theorem exists_matrix_coboundary' (c : H → Matrix n n L) (hc1 : c 1 = 1)
    (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val) :
    ∃ P : GL n L, ∀ σ,
      c σ = (P : Matrix n n L) * ((P⁻¹ : GL n L) : Matrix n n L).map σ.val := by
  obtain ⟨P, hP⟩ := exists_matrix_coboundary H c hc1 hc
  exact ⟨P, fun σ => eq_mul_map_inv_of_mul_map_eq σ.val P (hP σ)⟩

/-- A chosen invertible matrix trivialising a matrix cocycle of a finite
automorphism group, as provided by `exists_matrix_coboundary`. -/
def coboundaryMatrix (c : H → Matrix n n L) (hc1 : c 1 = 1)
    (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val) : GL n L :=
  Classical.choose (exists_matrix_coboundary H c hc1 hc)

/-- The chosen matrix satisfies `c σ * σ(P) = P`. -/
theorem coboundaryMatrix_spec (c : H → Matrix n n L) (hc1 : c 1 = 1)
    (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val) (σ : H) :
    c σ * (coboundaryMatrix H c hc1 hc : Matrix n n L).map σ.val =
      coboundaryMatrix H c hc1 hc :=
  Classical.choose_spec (exists_matrix_coboundary H c hc1 hc) σ

/-- The cocycle is the coboundary `c σ = P * σ(P⁻¹)` of the chosen matrix. -/
theorem eq_coboundaryMatrix_mul (c : H → Matrix n n L) (hc1 : c 1 = 1)
    (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val) (σ : H) :
    c σ = (coboundaryMatrix H c hc1 hc : Matrix n n L) *
      (((coboundaryMatrix H c hc1 hc)⁻¹ : GL n L) : Matrix n n L).map σ.val :=
  eq_mul_map_inv_of_mul_map_eq σ.val _ (coboundaryMatrix_spec H c hc1 hc σ)

end Langlands.LinearAlgebra.GaloisVectorDescent
