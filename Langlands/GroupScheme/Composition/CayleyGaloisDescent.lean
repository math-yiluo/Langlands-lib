import Langlands.GroupScheme.Composition.CayleyMatrixIsomorphism

/-! # Finite Galois twists of arbitrary Cayley data -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.CayleyDatum

open CayleyGaloisTwist

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  (c : CayleyDatum K) [Infinite K] [Invertible (2 : K)]

local notation "φ" => algebraMap K L
local notation "V" => CayleyVector L

/-- The discrepancy of a change of basis with its Galois translates lies in the
  automorphism group of the original Cayley datum. -/
def IsGaloisTwist (P : GL (Fin 8) L) : Prop :=
  ∀ σ : L ≃ₐ[K] L, c.IsAutomorphismMatrix φ
    (P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)

variable (P : GL (Fin 8) L)

/-- The Cayley multiplication transported to the new coordinates over `L`. -/
private def transportedMul : V →ₗ[L] V →ₗ[L] V :=
  ((c.multiplicationBilin φ).compl₁₂ (↑P : Matrix (Fin 8) (Fin 8) L).mulVecLin
    (↑P : Matrix (Fin 8) (Fin 8) L).mulVecLin).compr₂
    (↑(P⁻¹) : Matrix (Fin 8) (Fin 8) L).mulVecLin

omit [Infinite K] [Invertible (2 : K)] in
private theorem transportedMul_apply (x y : V) :
    c.transportedMul P x y = (↑(P⁻¹) : Matrix (Fin 8) (Fin 8) L) *ᵥ
      c.multiplicationOver φ ((↑P : Matrix (Fin 8) (Fin 8) L) *ᵥ x)
        ((↑P : Matrix (Fin 8) (Fin 8) L) *ᵥ y) := rfl

private def transportedUnit : V := (↑(P⁻¹) : Matrix (Fin 8) (Fin 8) L) *ᵥ c.unitOver φ

private def transportedNorm : QuadraticForm L V :=
  (c.normOver φ).comp (↑P : Matrix (Fin 8) (Fin 8) L).mulVecLin

omit [Infinite K] in
private theorem transportedNorm_apply (x : V) :
    c.transportedNorm P x = c.normOver φ ((↑P : Matrix (Fin 8) (Fin 8) L) *ᵥ x) := rfl

variable {c P} (hP : c.IsGaloisTwist P)

local notation "M" => c.transportedMul P
local notation "U" => c.transportedUnit P
local notation "N" => c.transportedNorm P

omit [Infinite K] [Invertible (2 : K)] in
private theorem galois_comp_algebraMap (σ : L ≃ₐ[K] L) :
    (σ : L →+* L).comp φ = φ := by
  ext k
  exact σ.commutes k

include hP in
omit [Infinite K] [Invertible (2 : K)] in
private theorem transportedMul_fixed (σ : L ≃ₐ[K] L) (x y : CayleyVector K) :
    (fun i => σ (M (lift x) (lift y) i)) = M (lift x) (lift y) := by
  let a := (P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)⁻¹
  have ha := ((hP σ).inv (c := c)).2
  have hp : GeneralLinearGroup.map (σ : L →+* L) P = a * P := CayleyGaloisTwist.map_eq σ
  change (fun i => (σ : L →+* L) (M (lift x) (lift y) i)) = _
  have hx : (fun i => (σ : L →+* L) (lift x i)) = (lift x : V) := galois_lift σ x
  have hy : (fun i => (σ : L →+* L) (lift y i)) = (lift y : V) := galois_lift σ y
  simp only [transportedMul_apply, map_mulVec_fun, c.map_multiplicationOver_vec,
    galois_comp_algebraMap, hx, hy]
  simp only [← coe_map, map_inv, hp]
  rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← ha, inv_mulVec_mulVec]

include hP in
omit [Infinite K] [Invertible (2 : K)] in
private theorem transportedUnit_fixed (σ : L ≃ₐ[K] L) :
    (fun i => σ (U i)) = U := by
  let a := (P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)⁻¹
  have ha := ((hP σ).inv (c := c)).1
  have hp : GeneralLinearGroup.map (σ : L →+* L) P = a * P := CayleyGaloisTwist.map_eq σ
  change (fun i => (σ : L →+* L) (U i)) = _
  rw [transportedUnit, map_mulVec_fun, c.map_unitOver, galois_comp_algebraMap,
    ← coe_map, map_inv, hp, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  conv_lhs => rw [← ha]
  rw [inv_mulVec_mulVec]

include hP in
private theorem transportedNorm_fixed (σ : L ≃ₐ[K] L) (x : CayleyVector K) :
    σ (N (lift x)) = N (lift x) := by
  let a := (P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)⁻¹
  have ha : IsIsomorphismMatrix φ c c a := (hP σ).inv (c := c)
  have hp : GeneralLinearGroup.map (σ : L →+* L) P = a * P := CayleyGaloisTwist.map_eq σ
  change (σ : L →+* L) (N (lift x)) = _
  have hx : (fun i => (σ : L →+* L) (lift x i)) = (lift x : V) := galois_lift σ x
  rw [transportedNorm_apply, c.map_normOver, map_mulVec_fun,
    galois_comp_algebraMap, hx, ← coe_map, hp, Units.val_mul, ← Matrix.mulVec_mulVec]
  exact ha.normIsometry.map_app _

variable [FiniteDimensional K L] [IsGalois K L]

private def descendMulFun (x y : CayleyVector K) : CayleyVector K := descendVec (M (lift x) (lift y))

private def descendUnit : CayleyVector K := descendVec U

private def descendNormFun (x : CayleyVector K) : K := descendScalar (N (lift x))

include hP in
omit [Infinite K] [Invertible (2 : K)] in
private theorem lift_descendMulFun (x y : CayleyVector K) :
    lift (descendMulFun (c := c) (P := P) x y) = M (lift x) (lift y) :=
  lift_descendVec (fun σ => transportedMul_fixed hP σ x y)

include hP in
omit [Infinite K] [Invertible (2 : K)] in
private theorem lift_descendUnit : lift (descendUnit (c := c) (P := P)) = U :=
  lift_descendVec (fun σ => transportedUnit_fixed hP σ)

include hP in
private theorem algebraMap_descendNormFun (x : CayleyVector K) :
    φ (descendNormFun (c := c) (P := P) x) = N (lift x) :=
  algebraMap_descendScalar fun σ => transportedNorm_fixed hP σ x

include hP in
private theorem algebraMap_descendPolar (x y : CayleyVector K) :
    φ (QuadraticMap.polar (descendNormFun (c := c) (P := P)) x y) =
      QuadraticMap.polar N (lift x) (lift y) := by
  simp only [QuadraticMap.polar, map_sub, algebraMap_descendNormFun hP, lift_add]

private def descendMul : CayleyVector K →ₗ[K] CayleyVector K →ₗ[K] CayleyVector K :=
  LinearMap.mk₂ K (descendMulFun (c := c) (P := P))
    (fun x x' y => lift_injective (L := L) (by
      simp only [lift_add, lift_descendMulFun hP, map_add, LinearMap.add_apply]))
    (fun a x y => lift_injective (L := L) (by
      simp only [lift_smul, lift_descendMulFun hP, map_smul, LinearMap.smul_apply]))
    (fun x y y' => lift_injective (L := L) (by
      simp only [lift_add, lift_descendMulFun hP, map_add]))
    (fun a x y => lift_injective (L := L) (by
      simp only [lift_smul, lift_descendMulFun hP, map_smul]))

private def descendNorm : QuadraticForm K (CayleyVector K) :=
  QuadraticMap.ofPolar (descendNormFun (c := c) (P := P))
    (fun a x => (φ).injective (by
      rw [smul_eq_mul, map_mul, algebraMap_descendNormFun hP, algebraMap_descendNormFun hP,
        lift_smul, QuadraticMap.map_smul, smul_eq_mul, map_mul]))
    (fun x x' y => (φ).injective (by
      simp only [map_add, algebraMap_descendPolar hP, lift_add, QuadraticMap.polar_add_left]))
    (fun a x y => (φ).injective (by
      rw [smul_eq_mul, map_mul, algebraMap_descendPolar hP, algebraMap_descendPolar hP,
        lift_smul, QuadraticMap.polar_smul_left, smul_eq_mul]))

/-- The multiplication, unit and norm transported by the matrix descend to a
  Cayley datum on the original field. -/
def galoisTwist : CayleyDatum K where
  multiplication := descendMul hP
  unit := descendUnit (c := c) (P := P)
  norm := descendNorm hP
  unit_mul x := lift_injective (L := L) (by
    change lift (descendMulFun (c := c) (P := P) (descendUnit (c := c) (P := P)) x) = lift x
    rw [lift_descendMulFun hP, lift_descendUnit hP, transportedMul_apply, transportedUnit,
      mulVec_inv_mulVec]
    change (↑(P⁻¹) : Matrix (Fin 8) (Fin 8) L) *ᵥ (c.extend φ).multiplication (c.extend φ).unit _ = _
    rw [(c.extend φ).unit_mul, inv_mulVec_mulVec])
  mul_unit x := lift_injective (L := L) (by
    change lift (descendMulFun (c := c) (P := P) x (descendUnit (c := c) (P := P))) = lift x
    rw [lift_descendMulFun hP, lift_descendUnit hP, transportedMul_apply, transportedUnit,
      mulVec_inv_mulVec]
    change (↑(P⁻¹) : Matrix (Fin 8) (Fin 8) L) *ᵥ (c.extend φ).multiplication _ (c.extend φ).unit = _
    rw [(c.extend φ).mul_unit, inv_mulVec_mulVec])
  norm_unit := (φ).injective (by
    change φ (descendNormFun (c := c) (P := P) (descendUnit (c := c) (P := P))) = φ 1
    rw [algebraMap_descendNormFun hP, lift_descendUnit hP, transportedNorm_apply, transportedUnit,
      mulVec_inv_mulVec, map_one]
    exact (c.extend φ).norm_unit)
  norm_mul x y := (φ).injective (by
    change φ (descendNormFun (c := c) (P := P) (descendMulFun (c := c) (P := P) x y)) =
      φ (descendNormFun (c := c) (P := P) x * descendNormFun (c := c) (P := P) y)
    rw [map_mul, algebraMap_descendNormFun hP, algebraMap_descendNormFun hP,
      algebraMap_descendNormFun hP, lift_descendMulFun hP,
      transportedNorm_apply, transportedNorm_apply, transportedNorm_apply, transportedMul_apply, mulVec_inv_mulVec]
    exact (c.extend φ).norm_mul _ _)
  polar_nondegenerate x hx := by
    apply lift_injective (L := L)
    apply mulVec_injective P
    rw [show (lift (0 : CayleyVector K) : V) = 0 by funext i; simp [lift], Matrix.mulVec_zero]
    apply (c.extend φ).polar_nondegenerate
    intro w
    let f := ((N).polarBilin (lift x))
    have hf : f = 0 := by
      apply (Pi.basisFun L (Fin 8)).ext
      intro j
      rw [Pi.basisFun_apply, LinearMap.zero_apply, ← lift_single (K := K)]
      change QuadraticMap.polar N (lift x) (lift (Pi.single j 1)) = 0
      rw [← algebraMap_descendPolar hP]
      have h := hx (Pi.single j 1)
      change QuadraticMap.polar (descendNormFun (c := c) (P := P)) x (Pi.single j 1) = 0 at h
      rw [h, map_zero]
    have h := LinearMap.congr_fun hf ((↑(P⁻¹) : Matrix (Fin 8) (Fin 8) L) *ᵥ w)
    change (N).polarBilin _ _ = 0 at h
    rw [transportedNorm, QuadraticMap.polarBilin_comp, LinearMap.compl₁₂_apply, Matrix.mulVecLin_apply,
      Matrix.mulVecLin_apply, mulVec_inv_mulVec] at h
    exact h

/-- The original matrix realizes the descended twist as the original datum
  after extending coefficients to the Galois field. -/
theorem galoisTwist_isIsomorphismMatrix : IsIsomorphismMatrix φ (galoisTwist hP) c P := by
  apply IsIsomorphismMatrix.of_basis
  · change (↑P : Matrix (Fin 8) (Fin 8) L) *ᵥ lift (descendUnit (c := c) (P := P)) = c.unitOver φ
    rw [lift_descendUnit hP, transportedUnit, mulVec_inv_mulVec]
  · intro i j
    let d := galoisTwist hP
    have he := d.map_multiplicationOver_vec (RingHom.id K) φ (Pi.single i 1) (Pi.single j 1)
    rw [d.multiplicationOver_self, RingHom.comp_id] at he
    change lift (descendMulFun (c := c) (P := P) (Pi.single i 1) (Pi.single j 1)) =
      d.multiplicationOver φ (lift (Pi.single i 1)) (lift (Pi.single j 1)) at he
    rw [lift_descendMulFun hP, lift_single, lift_single, transportedMul_apply] at he
    rw [← he, mulVec_inv_mulVec]

end Langlands.GroupScheme.CayleyDatum
