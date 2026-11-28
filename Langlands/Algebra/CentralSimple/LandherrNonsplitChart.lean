import Langlands.Algebra.CentralSimple.LandherrNonsplit

/-! # Matrix charts and reduced norms at a nonsplit completion -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root
open scoped TensorProduct

universe u

variable (F E : Type u) [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [Algebra.IsSeparable F E] [CharZero F]
  (K : Type u) [Field K] [Algebra F K] [hK : Fact (¬ IsSquare (algebraMap F K (skewSq F E)))]

attribute [local instance] nonsplitAlgebra nonsplit_isScalarTower nonsplit_smulCommClass

/-- The comparison `E ⊗_F K → K(√d)`, `e ⊗ k ↦ e k`. -/
def nonsplitCenterMap : E ⊗[F] K →ₐ[E] nonsplitField F E K :=
  Algebra.TensorProduct.lift (Algebra.ofId E _)
    ((Algebra.ofId K (nonsplitField F E K)).restrictScalars F) (fun _ _ => Commute.all _ _)

@[simp] theorem nonsplitCenterMap_tmul (e : E) (k : K) :
    nonsplitCenterMap F E K (e ⊗ₜ k) = nonsplitEmbedding F E K e * algebraMap K _ k := by
  simp [nonsplitCenterMap, Algebra.ofId_apply, algebraMap_nonsplit]

/-- Every element of `E ⊗_F K` is `1 ⊗ k₁ + r ⊗ k₂`. -/
theorem exists_eq_one_tmul_add_skewRoot_tmul (z : E ⊗[F] K) :
    ∃ k₁ k₂ : K, z = (1 : E) ⊗ₜ k₁ + skewRoot F E ⊗ₜ k₂ := by
  induction z using TensorProduct.inductionOn with
  | tmul e k =>
    obtain ⟨a, b, rfl⟩ := exists_eq_add_mul_skewRoot F E e
    refine ⟨algebraMap F K a * k, algebraMap F K b * k, ?_⟩
    have h1 : (algebraMap F E a) ⊗ₜ[F] k = (1 : E) ⊗ₜ[F] (algebraMap F K a * k) := by
      rw [← Algebra.smul_def, Algebra.algebraMap_eq_smul_one (A := E), TensorProduct.smul_tmul]
    have h2 : (algebraMap F E b * skewRoot F E) ⊗ₜ[F] k =
        skewRoot F E ⊗ₜ[F] (algebraMap F K b * k) := by
      rw [← Algebra.smul_def, ← Algebra.smul_def, TensorProduct.smul_tmul]
    rw [TensorProduct.add_tmul, h1, h2]
  | add x y hx hy =>
    obtain ⟨a₁, a₂, rfl⟩ := hx
    obtain ⟨b₁, b₂, rfl⟩ := hy
    refine ⟨a₁ + b₁, a₂ + b₂, ?_⟩
    rw [TensorProduct.tmul_add, TensorProduct.tmul_add]
    abel

theorem nonsplitCenterMap_one_add (k₁ k₂ : K) :
    nonsplitCenterMap F E K ((1 : E) ⊗ₜ k₁ + skewRoot F E ⊗ₜ k₂) = ⟨k₁, k₂⟩ := by
  rw [map_add, nonsplitCenterMap_tmul, nonsplitCenterMap_tmul, map_one, one_mul,
    nonsplitEmbedding_skewRoot]
  ext <;> simp [QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im]

theorem nonsplitCenterMap_bijective : Function.Bijective (nonsplitCenterMap F E K) := by
  refine ⟨?_, fun l => ⟨(1 : E) ⊗ₜ l.re + skewRoot F E ⊗ₜ l.im, ?_⟩⟩
  · intro z₁ z₂ h
    obtain ⟨a₁, a₂, rfl⟩ := exists_eq_one_tmul_add_skewRoot_tmul F E K z₁
    obtain ⟨b₁, b₂, rfl⟩ := exists_eq_one_tmul_add_skewRoot_tmul F E K z₂
    rw [nonsplitCenterMap_one_add, nonsplitCenterMap_one_add] at h
    have h1 := congrArg QuadraticAlgebra.re h
    have h2 := congrArg QuadraticAlgebra.im h
    simp only at h1 h2
    rw [h1, h2]
  · rw [nonsplitCenterMap_one_add]

/-- `E ⊗_F K ≃ K(√d)` as `E`-algebras. -/
def nonsplitCenterEquiv : E ⊗[F] K ≃ₐ[E] nonsplitField F E K :=
  AlgEquiv.ofBijective _ (nonsplitCenterMap_bijective F E K)

@[simp] theorem nonsplitCenterEquiv_tmul (e : E) (k : K) :
    nonsplitCenterEquiv F E K (e ⊗ₜ k) = nonsplitEmbedding F E K e * algebraMap K _ k :=
  nonsplitCenterMap_tmul F E K e k

/-- The conjugation of `E` extended to `E ⊗_F K`. -/
def centerConj : E ⊗[F] K →ₐ[F] E ⊗[F] K :=
  Algebra.TensorProduct.map (conjugation F E).toAlgHom (AlgHom.id F K)

theorem nonsplitCenterEquiv_centerConj (z : E ⊗[F] K) :
    nonsplitCenterEquiv F E K (centerConj F E K z) = star (nonsplitCenterEquiv F E K z) := by
  induction z using TensorProduct.inductionOn with
  | tmul e k =>
    simp only [centerConj, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      nonsplitCenterEquiv_tmul, star_mul]
    rw [← nonsplitConj_apply, ← nonsplitConj_apply, nonsplitConj_embedding, AlgEquiv.commutes,
      mul_comm]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy, star_add]

section Algebra

variable (B : Type u) [Ring B] [Algebra E B] [Algebra F B] [IsScalarTower F E B]
  [FiniteDimensional E B] [Algebra.IsCentral E B] [IsSimpleRing B]

theorem map_nonsplitCenterEquiv_tensorEquiv (z : K ⊗[F] B) :
    Algebra.TensorProduct.map (nonsplitCenterEquiv F E K).toAlgHom (AlgHom.id E B)
      (UnitaryPoints.tensorEquiv F E B K z) = nonsplitEquiv F E B K z := by
  induction z using TensorProduct.inductionOn with
  | tmul k b =>
    rw [UnitaryPoints.tensorEquiv_tmul, Algebra.TensorProduct.map_tmul, nonsplitEquiv_tmul]
    change nonsplitCenterEquiv F E K ((1 : E) ⊗ₜ k) ⊗ₜ[E] _ = _
    rw [nonsplitCenterEquiv_tmul, map_one, one_mul, AlgHom.id_apply]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The relative reduced norm at `K` is the reduced norm of `K(√d) ⊗_E B`. -/
theorem nonsplitCenterEquiv_relativeNorm (x : (K ⊗[F] B)ˣ) :
    nonsplitCenterEquiv F E K (UnitaryPoints.relativeNorm F E B K x : E ⊗[F] K) =
      reducedNorm E B (nonsplitField F E K) (nonsplitEquiv F E B K x) := by
  rw [UnitaryPoints.relativeNorm_val]
  have h := reducedNorm_naturality E B (nonsplitCenterEquiv F E K).toAlgHom
    (UnitaryPoints.tensorEquiv F E B K (x : K ⊗[F] B))
  rw [map_nonsplitCenterEquiv_tensorEquiv] at h
  exact h.symm

end Algebra

end Langlands.CentralSimple.Landherr
