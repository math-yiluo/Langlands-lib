import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisCocycle

/-! # The descended Gram matrix of a special unitary Galois cocycle

A crossed homomorphism `c` of special unitary matrices for `H` over a finite Galois
extension `L/F` is a coboundary `c s = p · s(p)⁻¹` of an invertible matrix `p` (Hilbert 90).
The twisted Gram matrix `p⁻¹ H (p⁻¹)*` is Galois fixed and descends to a Gram matrix `H'` over
`D`. Coboundary data over an extension `M` of a field `K ⊇ F` give an isometry between `H'`
and `H` over `K`.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]

section FixedGram

variable {L : Type u} [Field L] [Algebra F L] {n : ℕ}

theorem gramOver_injective :
    Function.Injective (fun H : Matrix (Fin n) (Fin n) D => gramOver (F := F) n H L) := by
  intro H H' h
  ext i j
  have h' := congrFun (congrFun h i) j
  exact Algebra.TensorProduct.includeRight_injective (algebraMap F L).injective h'

theorem coeffMap_algebraMap_lid (B : Matrix (Fin n) (Fin n) (F ⊗[F] D)) :
    coeffMap (Algebra.ofId F L) B =
      gramOver n (B.map (Algebra.TensorProduct.lid F D)) L := by
  ext i j
  simp only [coeffMap_apply, gramOver, Matrix.map_apply]
  induction B i j using TensorProduct.inductionOn with
  | tmul a d =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.lid_tmul,
      Algebra.TensorProduct.includeRight_apply, Algebra.ofId_apply, ← mul_one (algebraMap F L a),
      ← Algebra.smul_def, ← TensorProduct.smul_tmul]
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add]

variable [FiniteDimensional F D] [FiniteDimensional F L] [IsGalois F L]

/-- A Galois-fixed matrix over `L ⊗ D` is the image of a matrix over `D`. -/
theorem exists_gramOver_eq_of_fixed (A : Matrix (Fin n) (Fin n) (L ⊗[F] D))
    (hA : ∀ s : L ≃ₐ[F] L, coeffMap s.toAlgHom A = A) :
    ∃ B : Matrix (Fin n) (Fin n) D, gramOver n B L = A := by
  obtain ⟨B, hB⟩ := exists_coeffMap_eq_of_fixed (K := F) (M := L) (D := D) A (fun s => hA s)
  refine ⟨B.map (Algebra.TensorProduct.lid F D), ?_⟩
  rw [← coeffMap_algebraMap_lid, ← hB]
  rfl

end FixedGram

section Descent

variable [Algebra.IsCentral F D] [FiniteDimensional F D] (τ : FirstKindInvolution F D)
  {n : ℕ} [NeZero n] (H : Matrix (Fin n) (Fin n) D)
  {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- A Hilbert 90 primitive of a crossed homomorphism together with its descended Gram matrix:
`c s = p · s(p)⁻¹` and `p H' p* = H` over `L`. -/
structure GramDescent (c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) where
  /-- The Hilbert 90 primitive. -/
  primitive : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ
  coboundary : ∀ s, c s = primitive * (unitMap s.toAlgHom primitive)⁻¹
  /-- The descended Gram matrix. -/
  gram : Matrix (Fin n) (Fin n) D
  gram_eq : (primitive : Matrix (Fin n) (Fin n) (L ⊗[F] D)) * gramOver n gram L *
    (τ.baseChange L).matrix (Fin n) primitive = gramOver n H L

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
theorem coeffMap_units_inv {R S : Type u} [CommRing R] [CommRing S] [Algebra F R] [Algebra F S]
    (f : R →ₐ[F] S) (p : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) :
    coeffMap f ((p⁻¹ : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) : Matrix (Fin n) (Fin n) (R ⊗[F] D)) =
      ((unitMap f p)⁻¹ : (Matrix (Fin n) (Fin n) (S ⊗[F] D))ˣ) := by
  rw [← map_inv]
  rfl

variable [Infinite F]

theorem exists_gramDescent {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ}
    (hc : IsCrossed c) (hsu : ∀ s, c s ∈ suGroup τ H L) : Nonempty (GramDescent τ H c) := by
  obtain ⟨p, hp⟩ := hc.exists_coboundary
  set adj := (τ.baseChange L).matrix (Fin n)
  set P : Matrix (Fin n) (Fin n) (L ⊗[F] D) := (p : Matrix (Fin n) (Fin n) (L ⊗[F] D))
  set Pi : Matrix (Fin n) (Fin n) (L ⊗[F] D) := ((p⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) :
    Matrix (Fin n) (Fin n) (L ⊗[F] D))
  have hfix : ∀ s : L ≃ₐ[F] L, coeffMap s.toAlgHom (Pi * gramOver n H L * adj Pi) =
      Pi * gramOver n H L * adj Pi := by
    intro s
    have hs : ((unitMap s.toAlgHom p)⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) = p⁻¹ * c s := by
      rw [hp s, ← mul_assoc, inv_mul_cancel, one_mul]
    have hs' : coeffMap s.toAlgHom Pi = Pi * (c s : Matrix (Fin n) (Fin n) (L ⊗[F] D)) := by
      rw [coeffMap_units_inv, hs, Units.val_mul]
    rw [_root_.map_mul, _root_.map_mul, coeffMap_gramOver, coeffMap_adjoint, hs',
      FirstKindInvolution.map_mul]
    have hsu' := (hsu s).1
    calc Pi * ↑(c s) * gramOver n H L * (adj ↑(c s) * adj Pi)
        = Pi * (↑(c s) * gramOver n H L * adj ↑(c s)) * adj Pi := by simp only [Matrix.mul_assoc]
      _ = Pi * gramOver n H L * adj Pi := by rw [hsu']
  obtain ⟨B, hB⟩ := exists_gramOver_eq_of_fixed _ hfix
  refine ⟨⟨p, hp, B, ?_⟩⟩
  rw [hB]
  change P * (Pi * gramOver n H L * adj Pi) * adj P = gramOver n H L
  have h1 : P * Pi = 1 := Units.mul_inv p
  calc P * (Pi * gramOver n H L * adj Pi) * adj P
      = (P * Pi) * gramOver n H L * (adj Pi * adj P) := by simp only [Matrix.mul_assoc]
    _ = gramOver n H L := by
      rw [h1, ← FirstKindInvolution.map_mul, h1, FirstKindInvolution.map_one, Matrix.one_mul,
        Matrix.mul_one]

end Descent

end Langlands.GroupScheme.Quaternionic.SkewUnitary
