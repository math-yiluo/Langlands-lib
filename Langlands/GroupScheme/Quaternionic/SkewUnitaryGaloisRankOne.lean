import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisInduction
import Langlands.GroupScheme.Quaternionic.SkewUnitaryGaloisCongruence
import Langlands.GroupScheme.Rational.NumberFieldQuaternionIntertwinerNorm

/-! # The special unitary Hasse principle in rank one

For a Gram matrix `H = (h)` of size one, a special unitary crossed homomorphism `c` is the
coboundary `c s = p (s p)⁻¹` of a unit `p` (Hilbert 90) with descended Gram matrix `(g)`. The
reduced norm `ν` of `p` lies in `F`. Coboundary data at a completion `K` give an element of
`K ⊗ D` intertwining `h` and `ν g` with reduced norm `ν⁻¹`; by the local-to-global principle
for the reduced norm on intertwiners there is such an element `y ∈ D`, and `p y` is a special
unitary primitive of `c`.
-/

noncomputable section

universe u

open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.Quaternionic.SkewUnitary

open Langlands.CentralSimple

section OneByOne

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
  [FiniteDimensional F D]

theorem matrix_fin_one_eq_diagonal {A : Type*} [Zero A] (X : Matrix (Fin 1) (Fin 1) A) :
    X = Matrix.diagonal (fun _ => X 0 0) := by
  ext i j
  fin_cases i
  fin_cases j
  rfl

theorem fin_one_mul_apply {A : Type*} [NonUnitalNonAssocSemiring A]
    (X Y : Matrix (Fin 1) (Fin 1) A) : (X * Y) 0 0 = X 0 0 * Y 0 0 := by
  rw [Matrix.mul_apply, Fin.sum_univ_one]

theorem matrixReducedNorm_fin_one (R : Type u) [CommRing R] [Algebra F R]
    (X : Matrix (Fin 1) (Fin 1) (R ⊗[F] D)) :
    matrixReducedNorm R X = reducedNorm F D R (X 0 0) := by
  conv_lhs => rw [matrix_fin_one_eq_diagonal X]
  rw [matrixReducedNorm_diagonal, Fin.prod_univ_one]

theorem matrixReducedNorm_coeffMap {n : ℕ} [NeZero n] {R S : Type u} [CommRing R] [CommRing S]
    [Algebra F R] [Algebra F S] (f : R →ₐ[F] S) (X : Matrix (Fin n) (Fin n) (R ⊗[F] D)) :
    matrixReducedNorm S (coeffMap f X) = f (matrixReducedNorm R X) :=
  matrixReducedNorm_naturality f X

theorem matrixReducedNorm_units_inv {n : ℕ} [NeZero n] (R : Type u) [CommRing R] [Algebra F R]
    (X : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) :
    matrixReducedNorm R ((X⁻¹ : (Matrix (Fin n) (Fin n) (R ⊗[F] D))ˣ) :
        Matrix (Fin n) (Fin n) (R ⊗[F] D)) * matrixReducedNorm R (X : Matrix (Fin n) (Fin n) (R ⊗[F] D)) = 1 := by
  rw [← _root_.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, _root_.map_one]

end OneByOne

section NormDescent

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
  [FiniteDimensional F D]
  {K M : Type u} [Field K] [Field M] [Algebra F K] [Algebra F M] [Algebra K M]
  [IsScalarTower F K M] [FiniteDimensional K M] [IsGalois K M]
  (τ : FirstKindInvolution F D) {n : ℕ} [NeZero n] (H : Matrix (Fin n) (Fin n) D)
  {L : Type u} [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
  [Algebra L M] [IsScalarTower F L M]

omit [FiniteDimensional F L] in
/-- Coboundary data over `M` give an isometry between the descended Gram matrix and `H`
over `K`, whose reduced norm is that of the Hilbert 90 primitive. -/
theorem GramDescent.exists_isometry_norm_of_coboundary
    {c : (L ≃ₐ[F] L) → (Matrix (Fin n) (Fin n) (L ⊗[F] D))ˣ} (d : GramDescent τ H c)
    (ν : F) (hν : matrixReducedNorm L (d.primitive : Matrix (Fin n) (Fin n) (L ⊗[F] D)) =
      algebraMap F L ν)
    (b : (Matrix (Fin n) (Fin n) (M ⊗[F] D))ˣ) (hb : b ∈ suGroup τ H M)
    (hcob : ∀ s : M ≃ₐ[K] M, unitMap (IsScalarTower.toAlgHom F L M)
        (c ((s.restrictScalars F).restrictNormal L)) =
      b * (unitMap (s.restrictScalars F).toAlgHom b)⁻¹) :
    ∃ t : (Matrix (Fin n) (Fin n) (K ⊗[F] D))ˣ,
      (t : Matrix (Fin n) (Fin n) (K ⊗[F] D)) * gramOver n d.gram K *
        (τ.baseChange K).matrix (Fin n) t = gramOver n H K ∧
      matrixReducedNorm K (t : Matrix (Fin n) (Fin n) (K ⊗[F] D)) = algebraMap F K ν := by
  let ι := IsScalarTower.toAlgHom F L M
  let T := b⁻¹ * unitMap ι d.primitive
  have hT : ∀ s : M ≃ₐ[K] M, unitMap (s.restrictScalars F).toAlgHom T = T := by
    intro s
    set ρ := (s.restrictScalars F).restrictNormal L
    have h1 : (unitMap (s.restrictScalars F).toAlgHom b)⁻¹ = b⁻¹ * unitMap ι (c ρ) := by
      rw [hcob s, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : c ρ * unitMap ρ.toAlgHom d.primitive = d.primitive := by
      rw [d.coboundary ρ, mul_assoc, inv_mul_cancel, mul_one]
    change unitMap (s.restrictScalars F).toAlgHom (b⁻¹ * unitMap ι d.primitive) = _
    rw [_root_.map_mul, map_inv, h1, unitMap_restrictNormal (K := K) (M := M) s, mul_assoc,
      ← _root_.map_mul, h2]
  obtain ⟨t, ht⟩ := exists_unitMap_eq_of_fixed (K := K) (M := M) T hT
  have hval : coeffMap (IsScalarTower.toAlgHom F K M) (t : Matrix (Fin n) (Fin n) (K ⊗[F] D)) =
      (T : Matrix (Fin n) (Fin n) (M ⊗[F] D)) := congrArg Units.val ht
  refine ⟨t, ?_, ?_⟩
  · apply coeffMap_tower_injective (K := K) (M := M)
    rw [_root_.map_mul, _root_.map_mul, coeffMap_adjoint, coeffMap_gramOver, coeffMap_gramOver,
      hval]
    set adj := (τ.baseChange M).matrix (Fin n)
    set Bi : Matrix (Fin n) (Fin n) (M ⊗[F] D) :=
      ((b⁻¹ : (Matrix (Fin n) (Fin n) (M ⊗[F] D))ˣ) : Matrix (Fin n) (Fin n) (M ⊗[F] D))
    set P : Matrix (Fin n) (Fin n) (M ⊗[F] D) :=
      coeffMap ι (d.primitive : Matrix (Fin n) (Fin n) (L ⊗[F] D))
    have hP : P * gramOver n d.gram M * adj P = gramOver n H M := by
      have h := congrArg (coeffMap ι) d.gram_eq
      rw [_root_.map_mul, _root_.map_mul, coeffMap_adjoint, coeffMap_gramOver,
        coeffMap_gramOver] at h
      exact h
    have hBi : Bi * gramOver n H M * adj Bi = gramOver n H M := ((suGroup τ H M).inv_mem hb).1
    change Bi * P * gramOver n d.gram M * adj (Bi * P) = gramOver n H M
    rw [FirstKindInvolution.map_mul]
    calc Bi * P * gramOver n d.gram M * (adj P * adj Bi)
        = Bi * (P * gramOver n d.gram M * adj P) * adj Bi := by simp only [Matrix.mul_assoc]
      _ = gramOver n H M := by rw [hP, hBi]
  · apply (algebraMap K M).injective
    have h1 := matrixReducedNorm_coeffMap (IsScalarTower.toAlgHom F K M)
      (t : Matrix (Fin n) (Fin n) (K ⊗[F] D))
    rw [hval] at h1
    change algebraMap K M _ = _
    rw [← IsScalarTower.algebraMap_apply F K M]
    rw [IsScalarTower.coe_toAlgHom'] at h1
    rw [← h1]
    change matrixReducedNorm M (((b⁻¹ : (Matrix (Fin n) (Fin n) (M ⊗[F] D))ˣ) :
      Matrix (Fin n) (Fin n) (M ⊗[F] D)) * coeffMap ι (d.primitive :
        Matrix (Fin n) (Fin n) (L ⊗[F] D))) = _
    rw [_root_.map_mul, ((suGroup τ H M).inv_mem hb).2, one_mul, matrixReducedNorm_coeffMap, hν]
    change algebraMap L M (algebraMap F L ν) = _
    rw [← IsScalarTower.algebraMap_apply]

end NormDescent

section RankOne

variable {F D : Type u} [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

omit [NumberField F] in
/-- A rank-one isometry `t (g) tᵗ^τ = (h)` of reduced norm `ν` gives the intertwiner `t⁻¹` of
`h` and `g` for the scalar `ν⁻¹`, of reduced norm `ν⁻¹`. -/
theorem hasIntertwinerOfNorm_of_isometry [CharZero F] {K : Type u} [Field K] [Algebra F K]
    (G H : Matrix (Fin 1) (Fin 1) D) (ν : F) (hν : ν ≠ 0)
    (t : (Matrix (Fin 1) (Fin 1) (K ⊗[F] D))ˣ)
    (ht : (t : Matrix (Fin 1) (Fin 1) (K ⊗[F] D)) * gramOver 1 G K *
      ((σ.quaternionConjugation hdim hsym).baseChange K).matrix (Fin 1) t = gramOver 1 H K)
    (htN : matrixReducedNorm K (t : Matrix (Fin 1) (Fin 1) (K ⊗[F] D)) = algebraMap F K ν) :
    FirstKindInvolution.HasIntertwinerOfNorm ν⁻¹ (H 0 0) (G 0 0) K := by
  set τK := (σ.quaternionConjugation hdim hsym).baseChange K
  set t0 := (t : Matrix (Fin 1) (Fin 1) (K ⊗[F] D)) 0 0
  set ti := ((t⁻¹ : (Matrix (Fin 1) (Fin 1) (K ⊗[F] D))ˣ) : Matrix (Fin 1) (Fin 1) (K ⊗[F] D)) 0 0
  have hti : ti * t0 = 1 := by
    have h := congrFun (congrFun (Units.inv_mul t) 0) 0
    rwa [fin_one_mul_apply, Matrix.one_apply_eq] at h
  have h00 : t0 * (1 ⊗ₜ[F] G 0 0) * τK t0 = 1 ⊗ₜ[F] H 0 0 := by
    have h := congrFun (congrFun ht 0) 0
    rwa [fin_one_mul_apply, fin_one_mul_apply, FirstKindInvolution.matrix_apply] at h
  have hN0 : reducedNorm F D K t0 = algebraMap F K ν := by
    rw [← matrixReducedNorm_fin_one]
    exact htN
  have hnorm : t0 * τK t0 = algebraMap F (K ⊗[F] D) ν := by
    rw [σ.quaternionConjugation_norm_baseChange hdim hsym K t0, hN0,
      ← IsScalarTower.algebraMap_apply]
  have hτt : τK t0 = ti * algebraMap F (K ⊗[F] D) ν := by
    calc τK t0 = (ti * t0) * τK t0 := by rw [hti, one_mul]
      _ = ti * (t0 * τK t0) := mul_assoc _ _ _
      _ = ti * algebraMap F (K ⊗[F] D) ν := by rw [hnorm]
  refine ⟨ti, ?_, ?_⟩
  · rw [← h00, hτt]
    calc ν⁻¹ • (ti * (t0 * (1 ⊗ₜ[F] G 0 0) * (ti * algebraMap F (K ⊗[F] D) ν)))
        = ν⁻¹ • ((ti * t0) * (1 ⊗ₜ[F] G 0 0) * ti * algebraMap F (K ⊗[F] D) ν) := by
          simp only [mul_assoc]
      _ = ν⁻¹ • (algebraMap F (K ⊗[F] D) ν * ((1 ⊗ₜ[F] G 0 0) * ti)) := by
          rw [hti, one_mul, Algebra.commutes, mul_assoc]
      _ = (1 ⊗ₜ[F] G 0 0) * ti := by
          rw [← Algebra.smul_def, smul_smul, inv_mul_cancel₀ hν, one_smul]
  · have h := (reducedNorm F D K).map_mul ti t0
    rw [hti, _root_.map_one, hN0] at h
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left h.symm

/-- The special unitary Hasse principle for Gram matrices of size one. -/
theorem suHasse_one : SUHasse σ hdim hsym 1 := by
  intro H hH hu L _ _ _ _ c hc hsu hloc
  set τ := σ.quaternionConjugation hdim hsym
  let : Invertible (2 : F) := invertibleOfNonzero two_ne_zero
  obtain ⟨d⟩ := exists_gramDescent τ H hc hsu
  set P := d.primitive
  set PM : Matrix (Fin 1) (Fin 1) (L ⊗[F] D) := (P : Matrix (Fin 1) (Fin 1) (L ⊗[F] D))
  have hfix : ∀ s : L ≃ₐ[F] L, s (matrixReducedNorm L PM) = matrixReducedNorm L PM := by
    intro s
    have h1 : matrixReducedNorm L (c s : Matrix (Fin 1) (Fin 1) (L ⊗[F] D)) = 1 := (hsu s).2
    rw [d.coboundary s, Units.val_mul, _root_.map_mul] at h1
    have h2 := matrixReducedNorm_units_inv L (unitMap s.toAlgHom P)
    rw [val_unitMap, matrixReducedNorm_coeffMap] at h2
    show s.toAlgHom (matrixReducedNorm L PM) = matrixReducedNorm L PM
    calc s.toAlgHom (matrixReducedNorm L PM)
        = (matrixReducedNorm L PM * matrixReducedNorm L
            (((unitMap s.toAlgHom P)⁻¹ : (Matrix (Fin 1) (Fin 1) (L ⊗[F] D))ˣ) :
              Matrix (Fin 1) (Fin 1) (L ⊗[F] D))) * s.toAlgHom (matrixReducedNorm L PM) := by
          rw [h1, one_mul]
      _ = matrixReducedNorm L PM * (matrixReducedNorm L
            (((unitMap s.toAlgHom P)⁻¹ : (Matrix (Fin 1) (Fin 1) (L ⊗[F] D))ˣ) :
              Matrix (Fin 1) (Fin 1) (L ⊗[F] D)) * s.toAlgHom (matrixReducedNorm L PM)) :=
          mul_assoc _ _ _
      _ = matrixReducedNorm L PM := by rw [h2, mul_one]
  obtain ⟨ν, hν⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (matrixReducedNorm L PM)).mpr hfix
  have hν0 : ν ≠ 0 := by
    intro h0
    have h2 := matrixReducedNorm_units_inv L P
    change _ * matrixReducedNorm L PM = 1 at h2
    rw [← hν, h0, _root_.map_zero, mul_zero] at h2
    exact zero_ne_one h2
  have hlocal : ∀ (K : Type u) [Field K] [Algebra F K] [CharZero K], IsCoboundaryAt τ H c K →
      FirstKindInvolution.HasIntertwinerOfNorm ν⁻¹ (H 0 0) (d.gram 0 0) K := by
    intro K _ _ _ hK
    obtain ⟨M, _, _, _, _, _, _, _, _⟩ :=
      CentralSimpleUnits.exists_finiteGalois_over_baseChange F K L
    obtain ⟨b, hb, hcob⟩ := hK M
    obtain ⟨t, ht, htN⟩ := GramDescent.exists_isometry_norm_of_coboundary (K := K) (M := M) τ H d
      ν hν.symm b hb hcob
    exact hasIntertwinerOfNorm_of_isometry σ hdim hsym d.gram H ν hν0 t ht htN
  obtain ⟨y, hy, hyN⟩ := FirstKindInvolution.exists_intertwiner_of_local σ hdim hsym ν⁻¹ (H 0 0)
    (d.gram 0 0)
    (fun w => by
      let : CharZero w.Completion :=
        charZero_of_injective_algebraMap (algebraMap F w.Completion).injective
      exact hlocal _ (hloc.1 w))
    (fun v => by
      let : CharZero (Global.FiniteCompletion F v) :=
        charZero_of_injective_algebraMap (algebraMap F (Global.FiniteCompletion F v)).injective
      exact hlocal _ (hloc.2 v))
  have hyτ : y * τ y = algebraMap F D ν⁻¹ := by
    rw [σ.quaternionConjugation_norm hdim hsym, hyN]
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hyτ
    exact (map_ne_zero_iff _ (algebraMap F D).injective).mpr (inv_ne_zero hν0) hyτ.symm
  have hyg : y * H 0 0 * τ y = d.gram 0 0 := by
    apply smul_right_injective D (inv_ne_zero hν0)
    change ν⁻¹ • (y * H 0 0 * τ y) = ν⁻¹ • d.gram 0 0
    calc ν⁻¹ • (y * H 0 0 * τ y) = (ν⁻¹ • (y * H 0 0)) * τ y := by rw [smul_mul_assoc]
      _ = d.gram 0 0 * y * τ y := by rw [hy]
      _ = d.gram 0 0 * algebraMap F D ν⁻¹ := by rw [mul_assoc, hyτ]
      _ = ν⁻¹ • d.gram 0 0 := by rw [← Algebra.commutes, ← Algebra.smul_def]
  set E : Matrix (Fin 1) (Fin 1) D := Matrix.diagonal (fun _ => y)
  have hEu : IsUnit E :=
    (Pi.isUnit_iff.mpr fun _ => isUnit_iff_ne_zero.mpr hy0).map (Matrix.diagonalRingHom (Fin 1) D)
  have hEH : ((hEu.unit : (Matrix (Fin 1) (Fin 1) D)ˣ) : Matrix (Fin 1) (Fin 1) D) * H *
      τ.matrix (Fin 1) (hEu.unit : (Matrix (Fin 1) (Fin 1) D)ˣ) = d.gram := by
    rw [IsUnit.unit_spec]
    ext i j
    fin_cases i
    fin_cases j
    change (E * H * τ.matrix (Fin 1) E) 0 0 = d.gram 0 0
    rw [fin_one_mul_apply, fin_one_mul_apply, FirstKindInvolution.matrix_apply]
    simp only [E, Matrix.diagonal_apply_eq]
    exact hyg
  set EL := unitOver F hEu.unit L
  have hELM : (EL : Matrix (Fin 1) (Fin 1) (L ⊗[F] D)) =
      coeffMap (Algebra.ofId F L) (gramOver 1 E F) := by
    rw [val_unitOver, IsUnit.unit_spec, coeffMap_gramOver]
  refine ⟨P * EL, ⟨?_, ?_⟩, fun s => ?_⟩
  · have hcong := gramOver_congr τ hEu.unit H L
    rw [hEH] at hcong
    set adj := (τ.baseChange L).matrix (Fin 1)
    set ELM : Matrix (Fin 1) (Fin 1) (L ⊗[F] D) := (EL : Matrix (Fin 1) (Fin 1) (L ⊗[F] D))
    change PM * ELM * gramOver 1 H L * adj (PM * ELM) = gramOver 1 H L
    rw [FirstKindInvolution.map_mul]
    calc PM * ELM * gramOver 1 H L * (adj ELM * adj PM)
        = PM * (ELM * gramOver 1 H L * adj ELM) * adj PM := by simp only [Matrix.mul_assoc]
      _ = PM * gramOver 1 d.gram L * adj PM := by rw [← hcong]
      _ = gramOver 1 H L := d.gram_eq
  · change matrixReducedNorm L (PM * (EL : Matrix (Fin 1) (Fin 1) (L ⊗[F] D))) = 1
    rw [_root_.map_mul, hELM, matrixReducedNorm_coeffMap, matrixReducedNorm_fin_one (R := F), ← hν]
    have hE0 : (gramOver 1 E F) 0 0 = (1 : F) ⊗ₜ[F] y := by
      simp [gramOver, E]
    rw [hE0, hyN, Algebra.ofId_apply, ← _root_.map_mul, mul_inv_cancel₀ hν0, _root_.map_one]
  · show c s = d.primitive * unitOver F hEu.unit L *
      (unitMap s.toAlgHom (d.primitive * unitOver F hEu.unit L))⁻¹
    rw [d.coboundary s, _root_.map_mul, unitMap_unitOver]
    group

end RankOne

end Langlands.GroupScheme.Quaternionic.SkewUnitary
