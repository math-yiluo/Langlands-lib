import Langlands.GroupScheme.Quaternionic.MatrixReducedNorm
import Langlands.GroupScheme.Quaternionic.SkewHermitianAdjoinLine

/-! # Special unitary matrices of a skew Gram matrix over coefficient algebras

For an involution of the first kind `τ` of a central division algebra `D` over a field `F` and
a Gram matrix `H` over `D`, the special unitary matrices over a commutative `F`-algebra `R` are
the units `M` of `M_n(R ⊗ D)` with `M H Mᵗ^τ = H` and reduced norm one. Coefficient changes act
on them entrywise; Galois automorphisms of a coefficient field act in this way.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (τ : FirstKindInvolution F D) {n : ℕ}

/-- Entrywise coefficient change on matrices over `R ⊗ D`. -/
def coeffMap {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) :
    Matrix (Fin n) (Fin n) (R ⊗[F] D) →+* Matrix (Fin n) (Fin n) (S ⊗[F] D) :=
  (Algebra.TensorProduct.map f (AlgHom.id F D)).toRingHom.mapMatrix

theorem coeffMap_apply {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (M : Matrix (Fin n) (Fin n) (R ⊗[F] D)) :
    coeffMap f M = M.map (Algebra.TensorProduct.map f (AlgHom.id F D)) :=
  rfl

theorem coeffMap_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra F R]
    [Algebra F S] [Algebra F T] (f : R →ₐ[F] S) (g : S →ₐ[F] T)
    (M : Matrix (Fin n) (Fin n) (R ⊗[F] D)) :
    coeffMap g (coeffMap f M) = coeffMap (g.comp f) M := by
  ext i j
  simp only [coeffMap_apply, Matrix.map_apply]
  rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]

theorem coeffMap_id {R : Type u} [CommRing R] [Algebra F R]
    (M : Matrix (Fin n) (Fin n) (R ⊗[F] D)) : coeffMap (AlgHom.id F R) M = M := by
  ext i j
  simp only [coeffMap_apply, Matrix.map_apply, Algebra.TensorProduct.map_id, AlgHom.id_apply]

variable (n) in
/-- The image of a Gram matrix over `D` in matrices over `R ⊗ D`. -/
def gramOver (H : Matrix (Fin n) (Fin n) D) (R : Type u) [CommRing R] [Algebra F R] :
    Matrix (Fin n) (Fin n) (R ⊗[F] D) :=
  H.map (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D)

theorem coeffMap_gramOver {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (H : Matrix (Fin n) (Fin n) D) :
    coeffMap f (gramOver n H R) = gramOver n H S := by
  ext i j
  simp [coeffMap_apply, gramOver]

theorem coeffMap_adjoint {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (M : Matrix (Fin n) (Fin n) (R ⊗[F] D)) :
    coeffMap f ((τ.baseChange R).matrix (Fin n) M) =
      (τ.baseChange S).matrix (Fin n) (coeffMap f M) := by
  ext i j
  simp only [coeffMap_apply, Matrix.map_apply, FirstKindInvolution.matrix_apply]
  exact τ.map_baseChange f (M j i)

variable [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n]

/-- A matrix over `R ⊗ D` is special unitary for `H` when it preserves `H` and has reduced
norm one. -/
def IsSU (H : Matrix (Fin n) (Fin n) D) {R : Type u} [CommRing R] [Algebra F R]
    (M : Matrix (Fin n) (Fin n) (R ⊗[F] D)) : Prop :=
  M * gramOver n H R * (τ.baseChange R).matrix (Fin n) M = gramOver n H R ∧
    matrixReducedNorm R M = 1

theorem IsSU.coeffMap {H : Matrix (Fin n) (Fin n) D} {R S : Type u} [CommRing R] [CommRing S]
    [Algebra F R] [Algebra F S] (f : R →ₐ[F] S) {M : Matrix (Fin n) (Fin n) (R ⊗[F] D)}
    (h : IsSU τ H M) : IsSU τ H (coeffMap f M) := by
  refine ⟨?_, ?_⟩
  · rw [← coeffMap_adjoint, ← coeffMap_gramOver f H, ← _root_.map_mul, ← _root_.map_mul, h.1]
  · rw [coeffMap_apply, matrixReducedNorm_naturality, h.2, _root_.map_one]

/-- The group of special unitary matrices for `H` over `R`. -/
def suGroup (H : Matrix (Fin n) (Fin n) D) (R : Type u) [CommRing R] [Algebra F R] :
    Subgroup (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ where
  carrier := {u | IsSU τ H (u : Matrix (Fin n) (Fin n) (R ⊗[F] D))}
  one_mem' := by
    refine ⟨?_, ?_⟩
    · simp only [Units.val_one, Matrix.one_mul, FirstKindInvolution.map_one, Matrix.mul_one]
    · simp only [Units.val_one, _root_.map_one]
  mul_mem' := by
    intro a b ha hb
    set adj := (τ.baseChange R).matrix (Fin n)
    set A : Matrix (Fin n) (Fin n) (R ⊗[F] D) := (a : Matrix (Fin n) (Fin n) (R ⊗[F] D))
    set B : Matrix (Fin n) (Fin n) (R ⊗[F] D) := (b : Matrix (Fin n) (Fin n) (R ⊗[F] D))
    have hA : A * gramOver n H R * adj A = gramOver n H R := ha.1
    have hB : B * gramOver n H R * adj B = gramOver n H R := hb.1
    refine ⟨?_, ?_⟩
    · change A * B * gramOver n H R * adj (A * B) = gramOver n H R
      rw [FirstKindInvolution.map_mul]
      calc A * B * gramOver n H R * (adj B * adj A)
          = A * (B * gramOver n H R * adj B) * adj A := by simp only [Matrix.mul_assoc]
        _ = gramOver n H R := by rw [hB, hA]
    · change matrixReducedNorm R (A * B) = 1
      rw [_root_.map_mul, ha.2, hb.2, mul_one]
  inv_mem' := by
    intro a ha
    set adj := (τ.baseChange R).matrix (Fin n)
    set M : Matrix (Fin n) (Fin n) (R ⊗[F] D) := (a : Matrix (Fin n) (Fin n) (R ⊗[F] D))
    set Mi : Matrix (Fin n) (Fin n) (R ⊗[F] D) := ((a⁻¹ : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) :
      Matrix (Fin n) (Fin n) (R ⊗[F] D))
    have h1 : Mi * M = 1 := Units.inv_mul a
    have h2 : M * Mi = 1 := Units.mul_inv a
    have hM : M * gramOver n H R * adj M = gramOver n H R := ha.1
    refine ⟨?_, ?_⟩
    · change Mi * gramOver n H R * adj Mi = gramOver n H R
      calc Mi * gramOver n H R * adj Mi = Mi * (M * gramOver n H R * adj M) * adj Mi := by
            rw [hM]
        _ = (Mi * M) * gramOver n H R * (adj M * adj Mi) := by
            simp only [Matrix.mul_assoc]
        _ = gramOver n H R := by
            rw [h1, ← FirstKindInvolution.map_mul, h1, FirstKindInvolution.map_one, Matrix.one_mul,
              Matrix.mul_one]
    · have h := congrArg (matrixReducedNorm R) h1
      rw [_root_.map_mul, ha.2, mul_one, _root_.map_one] at h
      exact h

theorem mem_suGroup {H : Matrix (Fin n) (Fin n) D} {R : Type u} [CommRing R] [Algebra F R]
    (u : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) :
    u ∈ suGroup τ H R ↔ IsSU τ H (u : Matrix (Fin n) (Fin n) (R ⊗[F] D)) :=
  Iff.rfl

/-- Entrywise coefficient change on units. -/
def unitMap {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) :
    (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ →* (Matrix (Fin n) (Fin n) (S ⊗[F] D))ˣ :=
  Units.map (coeffMap f).toMonoidHom

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
@[simp] theorem val_unitMap {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (u : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) :
    (unitMap f u : Matrix (Fin n) (Fin n) (S ⊗[F] D)) = coeffMap f u :=
  rfl

theorem unitMap_mem {H : Matrix (Fin n) (Fin n) D} {R S : Type u} [CommRing R] [CommRing S]
    [Algebra F R] [Algebra F S] (f : R →ₐ[F] S) {u : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ}
    (hu : u ∈ suGroup τ H R) : unitMap f u ∈ suGroup τ H S :=
  hu.coeffMap τ f

end Langlands.GroupScheme.Quaternionic.SkewUnitary
