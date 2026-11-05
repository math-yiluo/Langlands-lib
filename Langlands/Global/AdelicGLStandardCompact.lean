import Langlands.Global.PrimitiveAdelicGLn
import Langlands.Global.ArchimedeanCompact
import Langlands.Global.FiniteAdelicGL.StandardIntegralCompact
import Langlands.LinearAlgebra.TriangularUnitary

/-! # The standard compact subgroup of the actual adelic `GL(n)` and bounded factors -/

noncomputable section

universe u

open scoped Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

open Langlands.LinearAlgebra.TriangularUnitary

/-! ## Local linear algebra -/

section Subring

variable {K : Type*} [Field K] (O : Subring K) {n : ℕ}

/-- A determinant of a matrix with entries in a subring lies in the subring. -/
theorem det_mem_of_forall_mem {A : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ O) :
    A.det ∈ O := by
  let A' : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hA i j⟩
  have hA' : O.subtype.mapMatrix A' = A := rfl
  rw [← hA', ← RingHom.map_det]
  exact A'.det.property

/-- The adjugate of a matrix with entries in a subring has entries in the subring. -/
theorem adjugate_mem_of_forall_mem {A : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ O)
    (i j : Fin n) : A.adjugate i j ∈ O := by
  let A' : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hA i j⟩
  have hA' : O.subtype.mapMatrix A' = A := rfl
  rw [← hA', ← RingHom.map_adjugate]
  exact (A'.adjugate i j).property

/-- If the entries of `A` and the inverse of its determinant lie in a subring, then so do
the entries of `A⁻¹`. -/
theorem inv_mem_of_forall_mem {A : Matrix (Fin n) (Fin n) K} (hA : ∀ i j, A i j ∈ O)
    (hdet : A.det⁻¹ ∈ O) (i j : Fin n) : A⁻¹ i j ∈ O := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact O.mul_mem hdet (adjugate_mem_of_forall_mem O hA i j)

end Subring

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- Two-sided bounds on the diagonal of the triangular factor `b` of `M = b u`, from an entry
bound `B` on `M⁻¹` and `‖det M‖ = 1`. -/
theorem diag_bounds_of_isTriangularUnitaryFactorization {M b u : Matrix (Fin n) (Fin n) 𝕜}
    (hf : IsTriangularUnitaryFactorization M b u) {B : ℝ} (hB : 1 ≤ B)
    (hinv : ∀ i j, ‖M⁻¹ i j‖ ≤ B) (hdet : ‖M.det‖ = 1) (i : Fin n) :
    (Real.sqrt n * B)⁻¹ ≤ ‖b i i‖ ∧ ‖b i i‖ ≤ (Real.sqrt n * B) ^ n := by
  classical
  have hM0 : (0 : ℝ) ≤ ∑ p : Fin n × Fin n, ‖M p.1 p.2‖ :=
    Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hMB : ∀ i j, ‖M i j‖ ≤ ∑ p : Fin n × Fin n, ‖M p.1 p.2‖ := fun i j =>
    Finset.single_le_sum (f := fun p : Fin n × Fin n => ‖M p.1 p.2‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ (i, j))
  have hlow : ∀ j, (Real.sqrt n * B)⁻¹ ≤ ‖b j j‖ :=
    (bounds_of_isTriangularUnitaryFactorization hf hM0 (zero_le_one.trans hB) hMB hinv).2.2
  refine ⟨hlow i, ?_⟩
  have hsq : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fin.pos i).ne'
  have hC : 1 ≤ Real.sqrt n * B := one_le_mul_of_one_le_of_one_le hsq hB
  have hb : ‖b.det‖ = 1 := by
    have hu : ‖u.det‖ = 1 := CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary hf.2.2.1)
    rw [hf.2.2.2, Matrix.det_mul, norm_mul, hu, mul_one] at hdet
    exact hdet
  rw [Matrix.det_of_isUpperTriangular hf.1, norm_prod] at hb
  have hsplit := Finset.mul_prod_erase Finset.univ (fun j => ‖b j j‖) (Finset.mem_univ i)
  rw [hb] at hsplit
  have hm : (0 : ℝ) < (Real.sqrt n * B)⁻¹ := inv_pos.mpr (zero_lt_one.trans_le hC)
  have hge : (Real.sqrt n * B)⁻¹ ^ (n - 1) ≤ ∏ j ∈ Finset.univ.erase i, ‖b j j‖ := by
    have h := Finset.prod_le_prod₀ (s := Finset.univ.erase i)
      (f := fun _ => (Real.sqrt n * B)⁻¹) (g := fun j => ‖b j j‖)
      (fun _ _ => hm.le) (fun j _ => hlow j)
    rwa [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin] at h
  calc ‖b i i‖ = (∏ j ∈ Finset.univ.erase i, ‖b j j‖)⁻¹ := eq_inv_of_mul_eq_one_left hsplit
    _ ≤ ((Real.sqrt n * B)⁻¹ ^ (n - 1))⁻¹ := inv_anti₀ (pow_pos hm _) hge
    _ = (Real.sqrt n * B) ^ (n - 1) := by rw [inv_pow, inv_inv]
    _ ≤ (Real.sqrt n * B) ^ n := pow_le_pow_right₀ hC (Nat.sub_le n 1)

/-- If `M = b u` with `u` unitary and `U` is an invertible matrix with value `u`, then
`M U⁻¹ = b`. -/
theorem mul_inv_val_eq {M b u : Matrix (Fin n) (Fin n) 𝕜}
    (hf : IsTriangularUnitaryFactorization M b u) {U : Matrix.GeneralLinearGroup (Fin n) 𝕜}
    (hU : U.val = u) : M * (U⁻¹).val = b := by
  have hu := Matrix.mem_unitaryGroup_iff.mp hf.2.2.1
  have hinv : (U⁻¹).val = star u := Units.inv_eq_of_mul_eq_one_right (by rw [hU]; exact hu)
  rw [hinv, hf.2.2.2, Matrix.mul_assoc, hu, Matrix.mul_one]

end RCLike

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

/-! ## The standard compact subgroup -/

/-- The standard compact subgroup of the actual adelic `GL(n)`: real orthogonal or complex
unitary at the infinite places (`standardInfiniteCompact`) and invertible over the
integral finite adeles at the finite places (`FiniteAdelicGL.standardIntegral`). -/
def standardCompact : Subgroup (AdelicGL F n) :=
  (standardInfiniteCompact F n).comap (AdelicGL.infinite F n).toMonoidHom ⊓
    (FiniteAdelicGL.standardIntegral F n).toSubgroup.comap (AdelicGL.finite F n).toMonoidHom

theorem mem_standardCompact_iff (g : AdelicGL F n) :
    g ∈ standardCompact F n ↔ AdelicGL.infinite F n g ∈ standardInfiniteCompact F n ∧
      AdelicGL.finite F n g ∈ FiniteAdelicGL.standardIntegral F n :=
  Iff.rfl

theorem isCompact_standardCompact :
    IsCompact (standardCompact F n : Set (AdelicGL F n)) := by
  have h : (standardCompact F n : Set (AdelicGL F n)) = AdelicGL.split F n ⁻¹'
      ((standardInfiniteCompact F n : Set (InfiniteAdelicGL F n)) ×ˢ
        (FiniteAdelicGL.standardIntegral F n : Set (FiniteAdelicGL F n))) := rfl
  rw [h]
  exact ((AdelicGL.split F n).toHomeomorph.isCompact_preimage).mpr
    ((isCompact_standardInfiniteCompact F n).prod
      (FiniteAdelicGL.standardIntegralCompact F n))

/-! ## Finite places -/

/-- The inverse of a bounded unimodular matrix is invertible over the integral finite
adeles at the finite places. -/
theorem finite_inv_mem_standardIntegral {B : ℝ} {k : AdelicGL F n}
    (hk : IsBoundedUnimodular F n B k) :
    AdelicGL.finite F n k⁻¹ ∈ FiniteAdelicGL.standardIntegral F n := by
  have hint : ∀ (v : FinitePlace F) (x : FiniteCompletion F v), ‖x‖ ≤ 1 →
      x ∈ v.adicCompletionIntegers F := fun v x hx => by
    simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff] using hx
  rw [FiniteAdelicGL.mem_standardIntegral, ← map_inv, inv_inv]
  refine ⟨fun i j v => ?_, fun i j v => hint v _ (hk.1 v i j)⟩
  let f := finiteProjection F v
  let O := (v.adicCompletionIntegers F).toSubring
  have hA : ∀ i j, f.mapMatrix k.val i j ∈ O := fun i j => hint v _ (hk.1 v i j)
  have hdet : (f.mapMatrix k.val).det⁻¹ ∈ O := by
    apply hint v
    rw [norm_inv, ← RingHom.map_det]
    rw [show ‖f k.val.det‖ = 1 from hk.2.2.1 v, inv_one]
  have hinv : (f.mapMatrix k.val)⁻¹ = f.mapMatrix (k⁻¹).val := by
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_one]
  have h := inv_mem_of_forall_mem O hA hdet i j
  rw [hinv] at h
  exact h

/-! ## Infinite places -/

variable {F n}

/-- The coordinate at a real place of the mixed space. -/
def realCoord (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}) :
    NumberField.mixedEmbedding.mixedSpace F →+* ℝ :=
  (Pi.evalRingHom (fun _ => ℝ) v).comp (RingHom.fst _ _)

/-- The coordinate at a complex place of the mixed space. -/
def complexCoord
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}) :
    NumberField.mixedEmbedding.mixedSpace F →+* ℂ :=
  (Pi.evalRingHom (fun _ => ℂ) v).comp (RingHom.snd _ _)

omit [NumberField F] in
theorem norm_realCoord (x : NumberField.InfiniteAdeleRing F)
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}) :
    ‖realCoord v (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)‖ = ‖x v.1‖ := by
  change ‖NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v.1)‖ = _
  exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    v.2).norm_map_of_map_zero (map_zero _) _

omit [NumberField F] in
theorem norm_complexCoord (x : NumberField.InfiniteAdeleRing F)
    (v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}) :
    ‖complexCoord v (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)‖ = ‖x v.1‖ := by
  change ‖NumberField.InfinitePlace.Completion.extensionEmbedding v.1 (x v.1)‖ = _
  exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding
    v.1).norm_map_of_map_zero (map_zero _) _

section Coordinate

variable {𝕜 : Type*} [RCLike 𝕜] (φ : NumberField.mixedEmbedding.mixedSpace F →+* 𝕜)

omit [NumberField F] in
/-- Local inverse bounds and determinant norm in a coordinate `φ` that computes the norm
at the infinite place `w`. -/
theorem local_bounds (w : InfinitePlace F)
    (hφ : ∀ x : NumberField.InfiniteAdeleRing F,
      ‖φ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)‖ = ‖x w‖)
    {B : ℝ} (h : InfiniteAdelicGL F n)
    (hinv : ∀ i j, ‖(h⁻¹ : InfiniteAdelicGL F n) i j w‖ ≤ B) (hdet : ‖h.val.det w‖ = 1) :
    (∀ i j, ‖(Matrix.GeneralLinearGroup.map φ (archimedeanGLCoordinates F n h)).val⁻¹ i j‖ ≤
      B) ∧
      ‖(Matrix.GeneralLinearGroup.map φ (archimedeanGLCoordinates F n h)).val.det‖ = 1 := by
  constructor
  · intro i j
    rw [← Matrix.coe_units_inv, ← map_inv (Matrix.GeneralLinearGroup.map φ),
      ← map_inv (archimedeanGLCoordinates F n)]
    change ‖φ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F
      ((h⁻¹ : InfiniteAdelicGL F n) i j))‖ ≤ B
    rw [hφ]
    exact hinv i j
  · have he : (Matrix.GeneralLinearGroup.map φ (archimedeanGLCoordinates F n h)).val.det =
        φ (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F h.val.det) := by
      change (φ.mapMatrix ((NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.mapMatrix
        h.val)).det = _
      rw [← RingHom.map_det, ← RingHom.map_det]
      rfl
    rw [he, hφ, hdet]

omit [NumberField F] in
theorem local_mul_inv (h κ : InfiniteAdelicGL F n) :
    (Matrix.GeneralLinearGroup.map φ (archimedeanGLCoordinates F n (h * κ⁻¹))).val =
      (Matrix.GeneralLinearGroup.map φ (archimedeanGLCoordinates F n h)).val *
        ((Matrix.GeneralLinearGroup.map φ (archimedeanGLCoordinates F n κ))⁻¹).val := by
  rw [map_mul, map_inv, map_mul, map_inv, Units.val_mul]

end Coordinate

omit [NumberField F] in
/-- **Archimedean triangular–compact factorization.** An infinite adelic matrix `h` whose
inverse has entries bounded by `B ≥ 1` and whose determinant has norm one at every
infinite place is `β κ`, with `κ` in the standard orthogonal–unitary compact subgroup and
`β` upper triangular with diagonal norms in `[(√n B)⁻¹, (√n B)ⁿ]` at every infinite
place. -/
theorem exists_infinite_factorization {B : ℝ} (hB : 1 ≤ B) (h : InfiniteAdelicGL F n)
    (hinv : ∀ (w : InfinitePlace F) (i j : Fin n), ‖(h⁻¹ : InfiniteAdelicGL F n) i j w‖ ≤ B)
    (hdet : ∀ w : InfinitePlace F, ‖h.val.det w‖ = 1) :
    ∃ β κ : InfiniteAdelicGL F n, h = β * κ ∧ κ ∈ standardInfiniteCompact F n ∧
      β.val.IsUpperTriangular ∧ ∀ (w : InfinitePlace F) (i : Fin n),
        (Real.sqrt n * B)⁻¹ ≤ ‖β i i w‖ ∧ ‖β i i w‖ ≤ (Real.sqrt n * B) ^ n := by
  classical
  let X := archimedeanGLCoordinates F n h
  choose br ur hfr using fun v => exists_upperTriangular_mul_unitary
    (Matrix.GeneralLinearGroup.map (realCoord v) X).val (Units.isUnit _)
  choose bc uc hfc using fun v => exists_upperTriangular_mul_unitary
    (Matrix.GeneralLinearGroup.map (complexCoord v) X).val (Units.isUnit _)
  let p : ArchimedeanCompactFactors F n :=
    (fun v => ⟨ur v, (hfr v).2.2.1⟩, fun v => ⟨uc v, (hfc v).2.2.1⟩)
  let κ := ArchimedeanCompactFactors.toInfiniteAdelicGL F n p
  have hκr : ∀ v, (Matrix.GeneralLinearGroup.map (realCoord v)
      (archimedeanGLCoordinates F n κ)).val = ur v := fun v => by
    ext i j
    rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
    rfl
  have hκc : ∀ v, (Matrix.GeneralLinearGroup.map (complexCoord v)
      (archimedeanGLCoordinates F n κ)).val = uc v := fun v => by
    ext i j
    rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
    rfl
  have hβr : ∀ v, (Matrix.GeneralLinearGroup.map (realCoord v)
      (archimedeanGLCoordinates F n (h * κ⁻¹))).val = br v := fun v => by
    rw [local_mul_inv]
    exact mul_inv_val_eq (hfr v) (hκr v)
  have hβc : ∀ v, (Matrix.GeneralLinearGroup.map (complexCoord v)
      (archimedeanGLCoordinates F n (h * κ⁻¹))).val = bc v := fun v => by
    rw [local_mul_inv]
    exact mul_inv_val_eq (hfc v) (hκc v)
  refine ⟨h * κ⁻¹, κ, (inv_mul_cancel_right h κ).symm, ⟨p, rfl⟩, ?_, ?_⟩
  · intro i j hij
    apply (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F).injective
    rw [map_zero]
    apply Prod.ext
    · funext v
      exact (congrArg (fun M => M i j) (hβr v)).trans ((hfr v).1 hij)
    · funext v
      exact (congrArg (fun M => M i j) (hβc v)).trans ((hfc v).1 hij)
  · intro w i
    by_cases hw : NumberField.InfinitePlace.IsReal w
    · let v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v} := ⟨w, hw⟩
      have hφ : ∀ x : NumberField.InfiniteAdeleRing F,
          ‖realCoord v (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)‖ = ‖x w‖ :=
        fun x => norm_realCoord x v
      obtain ⟨hi, hd⟩ := local_bounds (realCoord v) w hφ h (hinv w) (hdet w)
      have he : ‖(h * κ⁻¹) i i w‖ = ‖br v i i‖ :=
        (hφ ((h * κ⁻¹) i i)).symm.trans (congrArg (fun M => ‖M i i‖) (hβr v))
      rw [he]
      exact diag_bounds_of_isTriangularUnitaryFactorization (hfr v) hB hi hd i
    · let v : {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v} :=
        ⟨w, NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hw⟩
      have hφ : ∀ x : NumberField.InfiniteAdeleRing F,
          ‖complexCoord v (NumberField.InfiniteAdeleRing.ringEquiv_mixedSpace F x)‖ = ‖x w‖ :=
        fun x => norm_complexCoord x v
      obtain ⟨hi, hd⟩ := local_bounds (complexCoord v) w hφ h (hinv w) (hdet w)
      have he : ‖(h * κ⁻¹) i i w‖ = ‖bc v i i‖ :=
        (hφ ((h * κ⁻¹) i i)).symm.trans (congrArg (fun M => ‖M i i‖) (hβc v))
      rw [he]
      exact diag_bounds_of_isTriangularUnitaryFactorization (hfc v) hB hi hd i

/-! ## Bounded unimodular matrices -/

variable (F n)

/-- **Triangular–compact factorization of bounded unimodular inverses.** If `k` is bounded
unimodular with bound `B ≥ 1`, then `k⁻¹ = β κ` with `κ` in the standard compact subgroup
and `β` upper triangular, equal to the identity at every finite place, with diagonal norms
in `[(√n B)⁻¹, (√n B)ⁿ]` at every infinite place. -/
theorem exists_upperTriangular_mul_mem_standardCompact {B : ℝ} (hB : 1 ≤ B)
    {k : AdelicGL F n} (hk : IsBoundedUnimodular F n B k) :
    ∃ β κ : AdelicGL F n, k⁻¹ = β * κ ∧ κ ∈ standardCompact F n ∧
      β.val.IsUpperTriangular ∧ AdelicGL.finite F n β = 1 ∧
      ∀ (w : InfinitePlace F) (i : Fin n),
        (Real.sqrt n * B)⁻¹ ≤ ‖infiniteProjection F w (β i i)‖ ∧
          ‖infiniteProjection F w (β i i)‖ ≤ (Real.sqrt n * B) ^ n := by
  have hinvk : (AdelicGL.infinite F n k⁻¹)⁻¹ = AdelicGL.infinite F n k := by
    rw [← map_inv, inv_inv]
  have hdetk : ∀ w : InfinitePlace F, ‖(AdelicGL.infinite F n k⁻¹).val.det w‖ = 1 := by
    intro w
    have h1 : (AdelicGL.infinite F n k⁻¹).val.det * (AdelicGL.infinite F n k).val.det = 1 := by
      rw [← Matrix.det_mul, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.det_one]
    have h2 : (AdelicGL.infinite F n k).val.det = (k.val.det).1 := by
      exact (RingHom.map_det (RingHom.fst (NumberField.InfiniteAdeleRing F)
        (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers F) F)) k.val).symm
    have h3 : (AdelicGL.infinite F n k⁻¹).val.det w * (k.val.det).1 w = 1 := by
      rw [← h2]
      exact congrFun h1 w
    have h4 : ‖(k.val.det).1 w‖ = 1 := hk.2.2.2 w
    have h5 := congrArg norm h3
    rw [norm_mul, h4, mul_one, norm_one] at h5
    exact h5
  obtain ⟨β, κ, hβκ, hκ, hβ, hbd⟩ := exists_infinite_factorization hB
    (AdelicGL.infinite F n k⁻¹) (fun w i j => by rw [hinvk]; exact hk.2.1 w i j) hdetk
  refine ⟨AdelicGL.pair F n β 1, AdelicGL.pair F n κ (AdelicGL.finite F n k⁻¹), ?_,
    (mem_standardCompact_iff F n _).mpr ⟨by rw [AdelicGL.infinite_pair]; exact hκ,
      by rw [AdelicGL.finite_pair]; exact finite_inv_mem_standardIntegral F n hk⟩,
    ?_, AdelicGL.finite_pair F n β 1, fun w i => hbd w i⟩
  · apply (AdelicGL.split F n).injective
    rw [map_mul]
    change (AdelicGL.infinite F n k⁻¹, AdelicGL.finite F n k⁻¹) =
      (AdelicGL.infinite F n (AdelicGL.pair F n β 1),
        AdelicGL.finite F n (AdelicGL.pair F n β 1)) *
      (AdelicGL.infinite F n (AdelicGL.pair F n κ (AdelicGL.finite F n k⁻¹)),
        AdelicGL.finite F n (AdelicGL.pair F n κ (AdelicGL.finite F n k⁻¹)))
    rw [AdelicGL.infinite_pair, AdelicGL.finite_pair, AdelicGL.infinite_pair,
      AdelicGL.finite_pair, Prod.mk_mul_mk, one_mul, ← hβκ]
  · intro i j hij
    have hji : j < i := hij
    change (AdelicGL.pair F n β 1) i j = 0
    rw [AdelicGL.pair_apply, hβ hij, Units.val_one, Matrix.one_apply_ne (ne_of_gt hji)]
    rfl

end Langlands.Global.PrimitiveAdelicHeight
