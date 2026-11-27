import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisInduction

/-! # Transport of special unitary crossed homomorphisms along a congruence

Conjugation by an invertible matrix `P` over `D` identifies special unitary matrices for `H`
with special unitary matrices for `P H P*`, compatibly with coefficient changes. It transports
crossed homomorphisms, coboundary data and coboundaries.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
  [FiniteDimensional F D] (τ : FirstKindInvolution F D) {n : ℕ} [NeZero n]

variable (F) in
/-- The image of a unit over `D` in units over `R ⊗ D`. -/
def unitOver (P : (Matrix (Fin n) (Fin n) D)ˣ) (R : Type u) [CommRing R] [Algebra F R] :
    (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D).toRingHom.mapMatrix.toMonoidHom P

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
theorem val_unitOver (P : (Matrix (Fin n) (Fin n) D)ˣ) (R : Type u) [CommRing R] [Algebra F R] :
    (unitOver F P R : Matrix (Fin n) (Fin n) (R ⊗[F] D)) =
      gramOver n (P : Matrix (Fin n) (Fin n) D) R :=
  rfl

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
theorem unitMap_unitOver (P : (Matrix (Fin n) (Fin n) D)ˣ) {R S : Type u} [CommRing R]
    [CommRing S] [Algebra F R] [Algebra F S] (f : R →ₐ[F] S) :
    unitMap f (unitOver F P R) = unitOver F P S := by
  apply Units.ext
  rw [val_unitMap, val_unitOver, val_unitOver, coeffMap_gramOver]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
theorem gramOver_congr (P : (Matrix (Fin n) (Fin n) D)ˣ) (H : Matrix (Fin n) (Fin n) D)
    (R : Type u) [CommRing R] [Algebra F R] :
    gramOver n ((P : Matrix (Fin n) (Fin n) D) * H * τ.matrix (Fin n) P) R =
      (unitOver F P R : Matrix (Fin n) (Fin n) (R ⊗[F] D)) * gramOver n H R *
        (τ.baseChange R).matrix (Fin n) (unitOver F P R : Matrix (Fin n) (Fin n) (R ⊗[F] D)) := by
  rw [gramOver_mul, gramOver_mul, val_unitOver, adjoint_gramOver]

/-- Conjugation by the image of `P` carries special unitary matrices for `H` to special unitary
matrices for `P H P*`. -/
theorem conj_mem_suGroup (P : (Matrix (Fin n) (Fin n) D)ˣ) (H : Matrix (Fin n) (Fin n) D)
    {R : Type u} [CommRing R] [Algebra F R] {u : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ}
    (hu : u ∈ suGroup τ H R) :
    unitOver F P R * u * (unitOver F P R)⁻¹ ∈
      suGroup τ ((P : Matrix (Fin n) (Fin n) D) * H * τ.matrix (Fin n) P) R := by
  set Q := unitOver F P R
  set adj := (τ.baseChange R).matrix (Fin n)
  set QM : Matrix (Fin n) (Fin n) (R ⊗[F] D) := (Q : Matrix (Fin n) (Fin n) (R ⊗[F] D))
  set QiM : Matrix (Fin n) (Fin n) (R ⊗[F] D) :=
    ((Q⁻¹ : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) : Matrix (Fin n) (Fin n) (R ⊗[F] D))
  set UM : Matrix (Fin n) (Fin n) (R ⊗[F] D) := (u : Matrix (Fin n) (Fin n) (R ⊗[F] D))
  have hQ : QiM * QM = 1 := Units.inv_mul Q
  have hQ' : QM * QiM = 1 := Units.mul_inv Q
  have hU : UM * gramOver n H R * adj UM = gramOver n H R := hu.1
  refine ⟨?_, ?_⟩
  · change QM * UM * QiM * gramOver n _ R * adj (QM * UM * QiM) = gramOver n _ R
    rw [gramOver_congr, FirstKindInvolution.map_mul, FirstKindInvolution.map_mul]
    change QM * UM * QiM * (QM * gramOver n H R * adj QM) * (adj QiM * (adj UM * adj QM)) =
      QM * gramOver n H R * adj QM
    calc QM * UM * QiM * (QM * gramOver n H R * adj QM) * (adj QiM * (adj UM * adj QM))
        = QM * UM * (QiM * QM) * gramOver n H R * (adj QM * adj QiM) * adj UM * adj QM := by
          simp only [Matrix.mul_assoc]
      _ = QM * (UM * gramOver n H R * adj UM) * adj QM := by
          rw [hQ, ← FirstKindInvolution.map_mul, hQ, FirstKindInvolution.map_one]
          simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = QM * gramOver n H R * adj QM := by rw [hU]
  · change matrixReducedNorm R (QM * UM * QiM) = 1
    rw [_root_.map_mul, _root_.map_mul, hu.2, mul_one, ← _root_.map_mul, hQ', _root_.map_one]

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
theorem unitOver_inv (P : (Matrix (Fin n) (Fin n) D)ˣ) (R : Type u) [CommRing R] [Algebra F R] :
    unitOver F P⁻¹ R = (unitOver F P R)⁻¹ :=
  map_inv _ P

omit [Algebra.IsCentral F D] [FiniteDimensional F D] [NeZero n] in
theorem inv_congr_gram (P : (Matrix (Fin n) (Fin n) D)ˣ) (H : Matrix (Fin n) (Fin n) D) :
    ((P⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) : Matrix (Fin n) (Fin n) D) *
        ((P : Matrix (Fin n) (Fin n) D) * H * τ.matrix (Fin n) P) *
        τ.matrix (Fin n) ((P⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) : Matrix (Fin n) (Fin n) D) = H := by
  have h1 : ((P⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) : Matrix (Fin n) (Fin n) D) *
      (P : Matrix (Fin n) (Fin n) D) = 1 := Units.inv_mul P
  have h2 : τ.matrix (Fin n) (P : Matrix (Fin n) (Fin n) D) *
      τ.matrix (Fin n) ((P⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) : Matrix (Fin n) (Fin n) D) = 1 := by
    rw [← FirstKindInvolution.map_mul, h1, FirstKindInvolution.map_one]
  calc ((P⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) : Matrix (Fin n) (Fin n) D) *
        ((P : Matrix (Fin n) (Fin n) D) * H * τ.matrix (Fin n) P) *
        τ.matrix (Fin n) ((P⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) : Matrix (Fin n) (Fin n) D)
      = (((P⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) : Matrix (Fin n) (Fin n) D) *
          (P : Matrix (Fin n) (Fin n) D)) * H * (τ.matrix (Fin n) (P : Matrix (Fin n) (Fin n) D) *
          τ.matrix (Fin n) ((P⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) : Matrix (Fin n) (Fin n) D)) := by
        simp only [Matrix.mul_assoc]
    _ = H := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/-- Conjugation by the inverse image of `P` carries special unitary matrices for `P H P*` back
to special unitary matrices for `H`. -/
theorem conj_inv_mem_suGroup (P : (Matrix (Fin n) (Fin n) D)ˣ) (H : Matrix (Fin n) (Fin n) D)
    {R : Type u} [CommRing R] [Algebra F R] {u : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ}
    (hu : u ∈ suGroup τ ((P : Matrix (Fin n) (Fin n) D) * H * τ.matrix (Fin n) P) R) :
    (unitOver F P R)⁻¹ * u * unitOver F P R ∈ suGroup τ H R := by
  have h := conj_mem_suGroup τ P⁻¹ _ hu
  rw [inv_congr_gram, unitOver_inv, inv_inv] at h
  exact h

/-- Transport of coboundary data along a congruence. -/
theorem IsCoboundaryAt.congr {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L]
    [IsGalois F L] (P : (Matrix (Fin n) (Fin n) D)ˣ) (H : Matrix (Fin n) (Fin n) D)
    {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ} (K : Type u) [Field K] [Algebra F K]
    (h : IsCoboundaryAt τ ((P : Matrix (Fin n) (Fin n) D) * H * τ.matrix (Fin n) P) c K) :
    IsCoboundaryAt τ H (fun s => (unitOver F P L)⁻¹ * c s * unitOver F P L) K := by
  intro M _ _ _ _ _ _ _ _
  obtain ⟨b, hb, hcob⟩ := h M
  refine ⟨(unitOver F P M)⁻¹ * b * unitOver F P M, conj_inv_mem_suGroup τ P H hb, fun s => ?_⟩
  simp only [_root_.map_mul, map_inv, unitMap_unitOver, hcob s]
  group

variable [NumberField F]

/-- The Hasse principle for special unitary crossed homomorphisms for one Gram matrix. -/
def HasseFor (H : Matrix (Fin n) (Fin n) D) : Prop :=
  ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    (c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ), IsCrossed c →
    (∀ s, c s ∈ suGroup τ H L) → IsLocallyCoboundary τ H c →
    ∃ a ∈ suGroup τ H L, ∀ s, c s = a * (unitMap s.toAlgHom a)⁻¹

/-- The Hasse principle for `H` gives the Hasse principle for every congruent Gram matrix. -/
theorem HasseFor.congr (P : (Matrix (Fin n) (Fin n) D)ˣ) {H : Matrix (Fin n) (Fin n) D}
    (hH : HasseFor τ H) :
    HasseFor τ ((P : Matrix (Fin n) (Fin n) D) * H * τ.matrix (Fin n) P) := by
  intro L _ _ _ _ c hc hsu hloc
  set c' : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ :=
    fun s => (unitOver F P L)⁻¹ * c s * unitOver F P L with hc'
  have hcr : IsCrossed c' := by
    intro s t
    simp only [hc', hc s t, _root_.map_mul, map_inv, unitMap_unitOver]
    group
  have hsu' : ∀ s, c' s ∈ suGroup τ H L := fun s => conj_inv_mem_suGroup τ P H (hsu s)
  have hloc' : IsLocallyCoboundary τ H c' :=
    ⟨fun w => IsCoboundaryAt.congr τ P H _ (hloc.1 w),
      fun v => IsCoboundaryAt.congr τ P H _ (hloc.2 v)⟩
  obtain ⟨a, ha, hcob⟩ := hH L c' hcr hsu' hloc'
  refine ⟨unitOver F P L * a * (unitOver F P L)⁻¹, conj_mem_suGroup τ P H ha, fun s => ?_⟩
  have h := hcob s
  simp only [hc'] at h
  calc c s = unitOver F P L * ((unitOver F P L)⁻¹ * c s * unitOver F P L) * (unitOver F P L)⁻¹ := by
        group
    _ = _ := by
        rw [h]
        simp only [_root_.map_mul, map_inv, unitMap_unitOver]
        group

end Langlands.GroupScheme.Quaternionic.SkewUnitary
