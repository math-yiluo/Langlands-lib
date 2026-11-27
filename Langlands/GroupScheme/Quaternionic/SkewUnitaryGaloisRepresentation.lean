import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisLocal
import Langlands.GroupScheme.Rational.NumberFieldBinarySkewRepresentation
import Langlands.GroupScheme.Rational.NumberFieldInnerTypeAHasseReduction
import Langlands.GroupScheme.Quaternionic.SymplecticPoints

/-! # Local representations by the descended Gram matrix

For a locally trivial crossed homomorphism of special unitary matrices over a number field,
the descended Gram matrix is antihermitian and invertible when `H` is, and it represents each
diagonal value of `H` at every completion.
-/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
  [FiniteDimensional F D] (τ : FirstKindInvolution F D) {n : ℕ} [NeZero n]
  (H : Matrix (Fin n) (Fin n) D)
  {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]

/-- Coboundary data over every finite Galois extension of a field `K ⊇ F` receiving `L`. -/
def IsCoboundaryAt (c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ)
    (K : Type u) [Field K] [Algebra F K] : Prop :=
  ∀ (M : Type u) [Field M] [Algebra K M] [Algebra F M] [IsScalarTower F K M] [Algebra L M]
    [IsScalarTower F L M] [FiniteDimensional K M] [IsGalois K M],
    ∃ b ∈ suGroup τ H M, ∀ s : M ≃ₐ[K] M,
      unitMap (IsScalarTower.toAlgHom F L M) (c ((s.restrictScalars F).restrictNormal L)) =
        b * (unitMap (s.restrictScalars F).toAlgHom b)⁻¹

/-- Coboundary data at every archimedean and every nonarchimedean completion. -/
def IsLocallyCoboundary [NumberField F] (c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) :
    Prop :=
  (∀ w : Global.InfinitePlace F, IsCoboundaryAt τ H c w.Completion) ∧
    ∀ v : Global.FinitePlace F, IsCoboundaryAt τ H c (Global.FiniteCompletion F v)

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
theorem adjoint_gramOver (R : Type u) [CommRing R] [Algebra F R] (G : Matrix (Fin n) (Fin n) D) :
    (τ.baseChange R).matrix (Fin n) (gramOver (F := F) n G R) =
      gramOver (F := F) n (τ.matrix (Fin n) G) R := by
  ext i j
  simp [gramOver, FirstKindInvolution.matrix_apply]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
theorem gramOver_mul (R : Type u) [CommRing R] [Algebra F R] (A B : Matrix (Fin n) (Fin n) D) :
    gramOver (F := F) n (A * B) R = gramOver (F := F) n A R * gramOver (F := F) n B R :=
  Matrix.map_mul

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
/-- The self-value of a row of `t` for `G` is the diagonal entry of `t G t*`. -/
theorem matrixSesqBilin_row (R : Type u) [CommRing R] [Algebra F R]
    (t G : Matrix (Fin n) (Fin n) (R ⊗[F] D)) (i : Fin n) :
    (τ.baseChange R).matrixSesqBilin G (t i) (t i) =
      (t * G * (τ.baseChange R).matrix (Fin n) t) i i := by
  simp only [FirstKindInvolution.matrixSesqBilin, LinearMap.mk₂_apply, Matrix.mul_apply,
    FirstKindInvolution.matrix_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

variable [Infinite F]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [FiniteDimensional F L] [IsGalois F L]
  [Infinite F] [NeZero n] in
theorem GramDescent.gram_antihermitian [Invertible (2 : F)]
    {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ}
    (d : GramDescent τ H c) (hH : τ.matrix (Fin n) H = -H) : τ.IsAntihermitian d.gram := by
  set adj := (τ.baseChange L).matrix (Fin n)
  set P : Matrix (Fin n) (Fin n) (L ⊗[F] D) := (d.primitive : Matrix (Fin n) (Fin n) (L ⊗[F] D))
  set Pi : Matrix (Fin n) (Fin n) (L ⊗[F] D) :=
    ((d.primitive⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) : Matrix (Fin n) (Fin n) (L ⊗[F] D))
  have h1 : Pi * P = 1 := Units.inv_mul d.primitive
  have hG : gramOver n d.gram L = Pi * gramOver n H L * adj Pi := by
    calc gramOver n d.gram L = (Pi * P) * gramOver n d.gram L * (adj P * adj Pi) := by
          rw [h1, ← FirstKindInvolution.map_mul, h1, FirstKindInvolution.map_one, Matrix.one_mul,
            Matrix.mul_one]
      _ = Pi * (P * gramOver n d.gram L * adj P) * adj Pi := by simp only [Matrix.mul_assoc]
      _ = Pi * gramOver n H L * adj Pi := by rw [d.gram_eq]
  have hneg : ∀ X : Matrix (Fin n) (Fin n) D, gramOver (F := F) n (-X) L = -gramOver n X L := by
    intro X
    ext i j
    simp [gramOver, TensorProduct.tmul_neg]
  have hskew : τ.matrix (Fin n) d.gram = -d.gram := by
    apply gramOver_injective (F := F) (L := L)
    change gramOver n (τ.matrix (Fin n) d.gram) L = gramOver n (-d.gram) L
    rw [← adjoint_gramOver, hG, FirstKindInvolution.map_mul, FirstKindInvolution.map_mul,
      FirstKindInvolution.apply_apply, adjoint_gramOver, hH, hneg, hneg, hG]
    simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    rfl
  refine ⟨hskew, fun k => ?_⟩
  have hdiag : τ (d.gram k k) = -d.gram k k := congrFun (congrFun hskew k) k
  refine τ.mem_alternatingSubspace.mpr ⟨(⅟(2 : F)) • d.gram k k, ?_⟩
  rw [τ.map_smul, hdiag, smul_neg, sub_neg_eq_add, invOf_two_smul_add_invOf_two_smul]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [FiniteDimensional F L] [IsGalois F L]
  [Infinite F] [NeZero n] in
theorem gramOver_isUnit (R : Type u) [CommRing R] [Algebra F R] {G : Matrix (Fin n) (Fin n) D}
    (hG : IsUnit G) : IsUnit (gramOver (F := F) n G R) :=
  hG.map (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D).toRingHom.mapMatrix

omit [Algebra.IsCentral F D] [Infinite F] [NeZero n] in
theorem GramDescent.gram_isUnit {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ}
    (d : GramDescent τ H c) (hu : IsUnit H) : IsUnit d.gram := by
  set adj := (τ.baseChange L).matrix (Fin n)
  set P : Matrix (Fin n) (Fin n) (L ⊗[F] D) := (d.primitive : Matrix (Fin n) (Fin n) (L ⊗[F] D))
  set Pi : Matrix (Fin n) (Fin n) (L ⊗[F] D) :=
    ((d.primitive⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) : Matrix (Fin n) (Fin n) (L ⊗[F] D))
  have h1 : Pi * P = 1 := Units.inv_mul d.primitive
  have h2 : P * Pi = 1 := Units.mul_inv d.primitive
  have hG : gramOver n d.gram L = Pi * gramOver n H L * adj Pi := by
    calc gramOver n d.gram L = (Pi * P) * gramOver n d.gram L * (adj P * adj Pi) := by
          rw [h1, ← FirstKindInvolution.map_mul, h1, FirstKindInvolution.map_one, Matrix.one_mul,
            Matrix.mul_one]
      _ = Pi * (P * gramOver n d.gram L * adj P) * adj Pi := by simp only [Matrix.mul_assoc]
      _ = Pi * gramOver n H L * adj Pi := by rw [d.gram_eq]
  have hPi : IsUnit Pi := (d.primitive⁻¹).isUnit
  have hadj : IsUnit (adj Pi) := ⟨⟨adj Pi, adj P, by rw [← FirstKindInvolution.map_mul, h2,
    FirstKindInvolution.map_one], by rw [← FirstKindInvolution.map_mul, h1,
    FirstKindInvolution.map_one]⟩, rfl⟩
  have hGL : IsUnit (gramOver (F := F) n d.gram L) := by
    rw [hG]
    exact (hPi.mul (gramOver_isUnit L hu)).mul hadj
  obtain ⟨W, hW⟩ := hGL
  have hfix : ∀ s : L ≃ₐ[F] L, coeffMap s.toAlgHom ((W⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) :
      Matrix (Fin n) (Fin n) (L ⊗[F] D)) = ((W⁻¹ : (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ) :
      Matrix (Fin n) (Fin n) (L ⊗[F] D)) := by
    intro s
    have hWs : unitMap s.toAlgHom W = W := by
      apply Units.ext
      rw [val_unitMap, hW, coeffMap_gramOver]
    rw [coeffMap_units_inv, hWs]
  obtain ⟨V, hV⟩ := exists_gramOver_eq_of_fixed _ hfix
  have hGV : d.gram * V = 1 := by
    apply gramOver_injective (F := F) (L := L)
    change gramOver n (d.gram * V) L = gramOver n 1 L
    rw [gramOver_mul, hV, ← hW, Units.mul_inv]
    ext i j
    simp [gramOver, Matrix.one_apply]
  have hVG : V * d.gram = 1 := by
    apply gramOver_injective (F := F) (L := L)
    change gramOver n (V * d.gram) L = gramOver n 1 L
    rw [gramOver_mul, hV, ← hW, Units.inv_mul]
    ext i j
    simp [gramOver, Matrix.one_apply]
  exact ⟨⟨d.gram, V, hGV, hVG⟩, rfl⟩

open FiniteAlgebraUnits.MatrixPoints in
omit [Infinite F] in
/-- At a field `K ⊇ F` with coboundary data, the descended Gram matrix represents each
diagonal value of `H`. -/
theorem GramDescent.exists_represent_over
    {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ} (d : GramDescent τ H c)
    (K : Type u) [Field K] [Algebra F K] [CharZero K] (hK : IsCoboundaryAt τ H c K) (i : Fin n) :
    ∃ x : Fin n → K ⊗[F] D, (τ.baseChange K).matrixSesqBilin
      (coefficientEquiv F D K ((1 : K) ⊗ₜ[F] d.gram)) x x = (1 : K) ⊗ₜ[F] H i i := by
  obtain ⟨M, _, _, _, _, _, _, _, _⟩ := CentralSimpleUnits.exists_finiteGalois_over_baseChange F K L
  obtain ⟨b, hb, hcob⟩ := hK M
  obtain ⟨t, ht⟩ := GramDescent.exists_isometry_of_coboundary (K := K) (M := M) τ H d b hb hcob
  refine ⟨(t : Matrix (Fin n) (Fin n) (K ⊗[F] D)) i, ?_⟩
  rw [FirstKindInvolution.coefficientEquiv_one_tmul_eq_map, matrixSesqBilin_row]
  exact congrFun (congrFun ht i) i

omit [Infinite F] in
/-- The descended Gram matrix represents each diagonal value of `H` at every completion. -/
theorem GramDescent.isLocallyRepresented [NumberField F]
    {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ} (d : GramDescent τ H c)
    (hloc : IsLocallyCoboundary τ H c) (i : Fin n) : τ.IsLocallyRepresented d.gram (H i i) := by
  intro v
  rcases v with w | v
  · let : CharZero w.Completion := charZero_of_injective_algebraMap
      (algebraMap F w.Completion).injective
    exact d.exists_represent_over τ H w.Completion (hloc.1 w) i
  · let : CharZero (Global.FiniteCompletion F v) := charZero_of_injective_algebraMap
      (algebraMap F (Global.FiniteCompletion F v)).injective
    exact d.exists_represent_over τ H (Global.FiniteCompletion F v) (hloc.2 v) i

end Langlands.GroupScheme.Quaternionic.SkewUnitary
