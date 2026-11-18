import Langlands.GroupScheme.Composition.SplitCayleyNormInvariance
import Mathlib.FieldTheory.Galois.Basic

/-! # Galois twists of the split Cayley datum by a fixed change of basis -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix

namespace Langlands.GroupScheme

namespace CayleyGaloisTwist

/-! ### Transport of the Zorn structure along an invertible matrix -/

section Transport

variable {R : Type u} [CommRing R]

/-- The underlying matrix of an invertible matrix after a change of coefficients. -/
theorem coe_map {S : Type u} [CommRing S] (f : R →+* S) (Q : GL (Fin 8) R) :
    ((GeneralLinearGroup.map f Q : GL (Fin 8) S) : Matrix (Fin 8) (Fin 8) S) =
      (Q : Matrix (Fin 8) (Fin 8) R).map f := rfl

theorem inv_mulVec_mulVec (Q : GL (Fin 8) R) (v : Fin 8 → R) :
    ((Q⁻¹ : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R) *ᵥ
      ((Q : Matrix (Fin 8) (Fin 8) R) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_inv_mulVec (Q : GL (Fin 8) R) (v : Fin 8 → R) :
    (Q : Matrix (Fin 8) (Fin 8) R) *ᵥ
      (((Q⁻¹ : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R) *ᵥ v) = v := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]

theorem mulVec_injective (Q : GL (Fin 8) R) {v w : Fin 8 → R}
    (h : (Q : Matrix (Fin 8) (Fin 8) R) *ᵥ v = (Q : Matrix (Fin 8) (Fin 8) R) *ᵥ w) :
    v = w := by
  rw [← inv_mulVec_mulVec Q v, h, inv_mulVec_mulVec]

/-- The Zorn product transported along `Q`, as a bilinear map: `(x, y) ↦ Q⁻¹ ((Q x)(Q y))`. -/
def twistBilin (Q : GL (Fin 8) R) :
    (Fin 8 → R) →ₗ[R] (Fin 8 → R) →ₗ[R] (Fin 8 → R) :=
  ((SplitCayley.mul R).compl₁₂ (Q : Matrix (Fin 8) (Fin 8) R).mulVecLin
    (Q : Matrix (Fin 8) (Fin 8) R).mulVecLin).compr₂
      ((Q⁻¹ : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R).mulVecLin

theorem twistBilin_apply (Q : GL (Fin 8) R) (x y : Fin 8 → R) :
    twistBilin Q x y = ((Q⁻¹ : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R) *ᵥ
      SplitCayley.mul R ((Q : Matrix (Fin 8) (Fin 8) R) *ᵥ x)
        ((Q : Matrix (Fin 8) (Fin 8) R) *ᵥ y) := rfl

/-- The Zorn unit transported along `Q`. -/
def twistUnit (Q : GL (Fin 8) R) : Fin 8 → R :=
  ((Q⁻¹ : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R) *ᵥ SplitCayley.unit R

/-- The Zorn norm transported along `Q`. -/
def twistNorm (Q : GL (Fin 8) R) (x : Fin 8 → R) : R :=
  SplitCayley.norm R ((Q : Matrix (Fin 8) (Fin 8) R) *ᵥ x)

theorem map_mulVec_fun {S : Type u} [CommRing S] (f : R →+* S) (M : Matrix (Fin 8) (Fin 8) R)
    (v : Fin 8 → R) : (fun i => f ((M *ᵥ v) i)) = M.map f *ᵥ (fun i => f (v i)) :=
  funext fun i => RingHom.map_mulVec f M v i

theorem map_unit {S : Type u} [CommRing S] (f : R →+* S) :
    (fun i => f (SplitCayley.unit R i)) = SplitCayley.unit S := by
  funext i
  fin_cases i <;> simp [SplitCayley.unit]

variable {S : Type u} [CommRing S]

theorem twistBilin_map (f : R →+* S) (Q : GL (Fin 8) R) (x y : Fin 8 → R) :
    (fun i => f (twistBilin Q x y i)) =
      twistBilin (GeneralLinearGroup.map f Q) (fun i => f (x i)) (fun i => f (y i)) := by
  rw [twistBilin_apply, twistBilin_apply, map_mulVec_fun, SplitCayley.mul_apply,
    SplitCayley.map_mulFun, map_mulVec_fun, map_mulVec_fun, ← map_inv, coe_map, coe_map]
  rfl

theorem twistUnit_map (f : R →+* S) (Q : GL (Fin 8) R) :
    (fun i => f (twistUnit Q i)) = twistUnit (GeneralLinearGroup.map f Q) := by
  rw [twistUnit, twistUnit, map_mulVec_fun, map_unit, ← map_inv, coe_map]

theorem twistNorm_map (f : R →+* S) (Q : GL (Fin 8) R) (x : Fin 8 → R) :
    f (twistNorm Q x) = twistNorm (GeneralLinearGroup.map f Q) (fun i => f (x i)) := by
  rw [twistNorm, twistNorm, coe_map, ← map_mulVec_fun, SplitCayley.norm_apply,
    SplitCayley.norm_apply]
  simp only [map_sub, map_add, map_mul]

/-- Left multiplication by a matrix preserving the Zorn product does not change the
transported product. -/
theorem twistBilin_mul_left {a : GL (Fin 8) R}
    (ha : ∀ x y, (a : Matrix (Fin 8) (Fin 8) R) *ᵥ SplitCayley.mul R x y =
      SplitCayley.mul R ((a : Matrix (Fin 8) (Fin 8) R) *ᵥ x)
        ((a : Matrix (Fin 8) (Fin 8) R) *ᵥ y))
    (Q : GL (Fin 8) R) (x y : Fin 8 → R) : twistBilin (a * Q) x y = twistBilin Q x y := by
  rw [twistBilin_apply, twistBilin_apply, _root_.mul_inv_rev, Units.val_mul, Units.val_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← ha,
    inv_mulVec_mulVec]

theorem twistUnit_mul_left {a : GL (Fin 8) R}
    (ha : (a : Matrix (Fin 8) (Fin 8) R) *ᵥ SplitCayley.unit R = SplitCayley.unit R)
    (Q : GL (Fin 8) R) : twistUnit (a * Q) = twistUnit Q := by
  rw [twistUnit, twistUnit, _root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  conv_lhs => rw [← ha]
  exact inv_mulVec_mulVec a _

end Transport

/-! ### Descent of Galois-fixed scalars and vectors -/

variable {K L : Type u} [Field K] [Field L] [Algebra K L]

/-- The coordinatewise image of a vector over `K` in `L⁸`. -/
def lift (x : Fin 8 → K) : Fin 8 → L := fun i => algebraMap K L (x i)

theorem lift_add (x y : Fin 8 → K) : (lift (x + y) : Fin 8 → L) = lift x + lift y := by
  funext i; simp [lift]

theorem lift_smul (a : K) (x : Fin 8 → K) :
    (lift (a • x) : Fin 8 → L) = algebraMap K L a • lift x := by
  funext i; simp [lift]

theorem lift_injective : Function.Injective (lift : (Fin 8 → K) → Fin 8 → L) := by
  intro x y h
  funext i
  exact (algebraMap K L).injective (congrFun h i)

theorem lift_single (j : Fin 8) : (lift (Pi.single j 1 : Fin 8 → K) : Fin 8 → L) =
    Pi.single j 1 := by
  funext l
  by_cases hl : l = j
  · subst hl; simp [lift]
  · simp [lift, hl]

theorem galois_lift (σ : L ≃ₐ[K] L) (x : Fin 8 → K) :
    (fun i => σ (lift x i)) = (lift x : Fin 8 → L) := by
  funext i; simp [lift]

/-- A scalar of `L` descended to `K` (meaningful for Galois-fixed scalars). -/
def descendScalar (x : L) : K :=
  Classical.epsilon fun k : K => algebraMap K L k = x

theorem algebraMap_descendScalar [FiniteDimensional K L] [IsGalois K L] {x : L}
    (hx : ∀ σ : L ≃ₐ[K] L, σ x = x) : algebraMap K L (descendScalar x) = x := by
  obtain ⟨k, hk⟩ := (IsGalois.mem_range_algebraMap_iff_fixed x).2 hx
  exact Classical.epsilon_spec (p := fun k : K => algebraMap K L k = x) ⟨k, hk⟩

/-- A vector of `L⁸` descended to `K⁸` coordinatewise. -/
def descendVec (v : Fin 8 → L) : Fin 8 → K := fun i => descendScalar (v i)

theorem lift_descendVec [FiniteDimensional K L] [IsGalois K L] {v : Fin 8 → L}
    (hv : ∀ σ : L ≃ₐ[K] L, (fun i => σ (v i)) = v) : lift (descendVec (K := K) v) = v := by
  funext i
  exact algebraMap_descendScalar fun σ => congrFun (hv σ) i

/-! ### The twisted Cayley datum -/

/-- A change of basis `P` of `L⁸` is a Galois twist of the split datum when every Galois
discrepancy `P σ(P)⁻¹` is an automorphism matrix of the split datum. -/
def IsTwist (P : GL (Fin 8) L) : Prop :=
  ∀ σ : L ≃ₐ[K] L, (CayleyDatum.split K).IsAutomorphismMatrix (algebraMap K L)
    (P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)

variable {P : GL (Fin 8) L}

theorem map_eq (σ : L ≃ₐ[K] L) :
    GeneralLinearGroup.map (σ : L →+* L) P =
      (P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)⁻¹ * P := by
  group

theorem polar_twistNorm (x y : Fin 8 → L) :
    QuadraticMap.polar (twistNorm P) x y =
      QuadraticMap.polar (SplitCayley.norm L) ((P : Matrix (Fin 8) (Fin 8) L) *ᵥ x)
        ((P : Matrix (Fin 8) (Fin 8) L) *ᵥ y) := by
  simp only [QuadraticMap.polar, twistNorm, Matrix.mulVec_add]

variable (P) in
/-- The descended multiplication on `K⁸`. -/
def mulFun (x y : Fin 8 → K) : Fin 8 → K :=
  descendVec (twistBilin P (lift x) (lift y))

variable (P) in
/-- The descended norm on `K⁸`. -/
def normFun (x : Fin 8 → K) : K :=
  descendScalar (twistNorm P (lift x))

variable (K P) in
/-- The descended unit vector. -/
def unitVec : Fin 8 → K := descendVec (twistUnit P)

variable (hP : IsTwist (K := K) P)

include hP

theorem inv_preserves_mul (σ : L ≃ₐ[K] L) (x y : Fin 8 → L) :
    (((P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)⁻¹ : GL (Fin 8) L) :
        Matrix (Fin 8) (Fin 8) L) *ᵥ SplitCayley.mul L x y =
      SplitCayley.mul L
        ((((P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)⁻¹ : GL (Fin 8) L) :
          Matrix (Fin 8) (Fin 8) L) *ᵥ x)
        ((((P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)⁻¹ : GL (Fin 8) L) :
          Matrix (Fin 8) (Fin 8) L) *ᵥ y) := by
  have h := ((hP σ).inv (c := CayleyDatum.split K)).2 x y
  rw [CayleyDatum.split_multiplicationOver, CayleyDatum.split_multiplicationOver] at h
  exact h

theorem inv_preserves_unit (σ : L ≃ₐ[K] L) :
    (((P * (GeneralLinearGroup.map (σ : L →+* L) P)⁻¹)⁻¹ : GL (Fin 8) L) :
        Matrix (Fin 8) (Fin 8) L) *ᵥ SplitCayley.unit L = SplitCayley.unit L := by
  have h := ((hP σ).inv (c := CayleyDatum.split K)).1
  rw [CayleyDatum.split_unitOver] at h
  exact h

theorem twistBilin_fixed (σ : L ≃ₐ[K] L) (x y : Fin 8 → K) :
    (fun i => σ (twistBilin P (lift x) (lift y) i)) = twistBilin P (lift x) (lift y) := by
  have h := twistBilin_map (σ : L →+* L) P (lift x) (lift y)
  have hx := galois_lift σ x
  have hy := galois_lift σ y
  change (fun i => (σ : L →+* L) (twistBilin P (lift x) (lift y) i)) = _
  rw [h]
  change twistBilin (GeneralLinearGroup.map (σ : L →+* L) P) (fun i => σ (lift x i))
    (fun i => σ (lift y i)) = _
  rw [hx, hy, map_eq σ]
  exact twistBilin_mul_left (inv_preserves_mul hP σ) P _ _

theorem twistUnit_fixed (σ : L ≃ₐ[K] L) :
    (fun i => σ (twistUnit P i)) = twistUnit P := by
  have h := twistUnit_map (σ : L →+* L) P
  change (fun i => (σ : L →+* L) (twistUnit P i)) = _
  rw [h, map_eq σ]
  exact twistUnit_mul_left (inv_preserves_unit hP σ) P

theorem twistNorm_fixed (σ : L ≃ₐ[K] L) (x : Fin 8 → K) :
    σ (twistNorm P (lift x)) = twistNorm P (lift x) := by
  have h := twistNorm_map (σ : L →+* L) P (lift x)
  change (σ : L →+* L) (twistNorm P (lift x)) = _
  rw [h]
  change twistNorm (GeneralLinearGroup.map (σ : L →+* L) P) (fun i => σ (lift x i)) = _
  rw [galois_lift σ x, map_eq σ, twistNorm, twistNorm, Units.val_mul,
    ← Matrix.mulVec_mulVec]
  exact CayleyDatum.split_norm_mulVec_eq (algebraMap K L) ((hP σ).inv) _

variable [FiniteDimensional K L] [IsGalois K L]

theorem lift_mulFun (x y : Fin 8 → K) :
    lift (mulFun P x y) = twistBilin P (lift x) (lift y) :=
  lift_descendVec (twistBilin_fixed hP · x y)

theorem algebraMap_normFun (x : Fin 8 → K) :
    algebraMap K L (normFun P x) = twistNorm P (lift x) :=
  algebraMap_descendScalar (twistNorm_fixed hP · x)

theorem algebraMap_polar_normFun (x y : Fin 8 → K) :
    algebraMap K L (QuadraticMap.polar (normFun P) x y) =
      QuadraticMap.polar (SplitCayley.norm L) ((P : Matrix (Fin 8) (Fin 8) L) *ᵥ lift x)
        ((P : Matrix (Fin 8) (Fin 8) L) *ᵥ lift y) := by
  rw [← polar_twistNorm]
  simp only [QuadraticMap.polar, map_sub, algebraMap_normFun hP, lift_add]

theorem lift_unitVec : lift (unitVec K P) = twistUnit P :=
  lift_descendVec (twistUnit_fixed hP)

/-- The descended multiplication as a `K`-bilinear map. -/
def multiplication : (Fin 8 → K) →ₗ[K] (Fin 8 → K) →ₗ[K] (Fin 8 → K) :=
  LinearMap.mk₂ K (mulFun P)
    (fun x x' y => lift_injective (L := L) (by
      rw [lift_add, lift_mulFun hP, lift_mulFun hP, lift_mulFun hP, lift_add, map_add,
        LinearMap.add_apply]))
    (fun a x y => lift_injective (L := L) (by
      rw [lift_smul, lift_mulFun hP, lift_mulFun hP, lift_smul, map_smul,
        LinearMap.smul_apply]))
    (fun x y y' => lift_injective (L := L) (by
      rw [lift_add, lift_mulFun hP, lift_mulFun hP, lift_mulFun hP, lift_add, map_add]))
    (fun a x y => lift_injective (L := L) (by
      rw [lift_smul, lift_mulFun hP, lift_mulFun hP, lift_smul, map_smul]))

/-- The descended norm as a quadratic form. -/
def norm : QuadraticForm K (Fin 8 → K) :=
  QuadraticMap.ofPolar (normFun P)
    (fun a x => (algebraMap K L).injective (by
      rw [algebraMap_normFun hP, smul_eq_mul, map_mul, algebraMap_normFun hP, lift_smul,
        twistNorm, twistNorm, Matrix.mulVec_smul, QuadraticMap.map_smul, smul_eq_mul,
        map_mul]))
    (fun x x' y => (algebraMap K L).injective (by
      rw [map_add, algebraMap_polar_normFun hP, algebraMap_polar_normFun hP,
        algebraMap_polar_normFun hP, lift_add, Matrix.mulVec_add, QuadraticMap.polar_add_left]))
    (fun a x y => (algebraMap K L).injective (by
      rw [smul_eq_mul, map_mul, algebraMap_polar_normFun hP, algebraMap_polar_normFun hP,
        lift_smul, Matrix.mulVec_smul, QuadraticMap.polar_smul_left, smul_eq_mul]))

theorem multiplication_apply (x y : Fin 8 → K) :
    multiplication hP x y = mulFun P x y := rfl

theorem norm_apply (x : Fin 8 → K) : norm hP x = normFun P x := rfl

/-- **The Galois twist of the split Cayley datum** by a change of basis whose Galois
discrepancies are split automorphisms. -/
def datum : CayleyDatum K where
  multiplication := multiplication hP
  unit := unitVec K P
  norm := norm hP
  unit_mul x := lift_injective (L := L) (by
    rw [multiplication_apply, lift_mulFun hP, lift_unitVec hP, twistBilin_apply, twistUnit,
      mulVec_inv_mulVec, SplitCayley.unit_mul, inv_mulVec_mulVec])
  mul_unit x := lift_injective (L := L) (by
    rw [multiplication_apply, lift_mulFun hP, lift_unitVec hP, twistBilin_apply, twistUnit,
      mulVec_inv_mulVec, SplitCayley.mul_unit, inv_mulVec_mulVec])
  norm_unit := (algebraMap K L).injective (by
    rw [norm_apply, algebraMap_normFun hP, lift_unitVec hP, twistNorm, twistUnit,
      mulVec_inv_mulVec, SplitCayley.norm_unit, map_one])
  norm_mul x y := (algebraMap K L).injective (by
    rw [norm_apply, algebraMap_normFun hP, multiplication_apply, lift_mulFun hP, map_mul,
      norm_apply, norm_apply, algebraMap_normFun hP, algebraMap_normFun hP, twistNorm,
      twistBilin_apply, mulVec_inv_mulVec, SplitCayley.norm_mul, twistNorm, twistNorm])
  polar_nondegenerate x hx := by
    apply lift_injective (L := L)
    apply mulVec_injective P
    rw [show (lift (0 : Fin 8 → K) : Fin 8 → L) = 0 by funext i; simp [lift],
      Matrix.mulVec_zero]
    apply SplitCayley.polar_nondegenerate L
    intro w
    let φ : (Fin 8 → L) →ₗ[L] L :=
      (QuadraticMap.polarBilin (SplitCayley.norm L)
        ((P : Matrix (Fin 8) (Fin 8) L) *ᵥ lift x)).comp
        (P : Matrix (Fin 8) (Fin 8) L).mulVecLin
    have hφ : φ = 0 := by
      apply (Pi.basisFun L (Fin 8)).ext
      intro j
      rw [Pi.basisFun_apply, LinearMap.zero_apply, ← lift_single (K := K)]
      change QuadraticMap.polar (SplitCayley.norm L) _ _ = 0
      rw [Matrix.mulVecLin_apply, ← algebraMap_polar_normFun hP]
      have h := hx (Pi.single j 1)
      rw [QuadraticMap.polarBilin_apply_apply] at h
      change QuadraticMap.polar (normFun P) x (Pi.single j 1) = 0 at h
      rw [h, map_zero]
    have h := LinearMap.congr_fun hφ
      (((P⁻¹ : GL (Fin 8) L) : Matrix (Fin 8) (Fin 8) L) *ᵥ w)
    change QuadraticMap.polar (SplitCayley.norm L) _ _ = 0 at h
    rw [Matrix.mulVecLin_apply, mulVec_inv_mulVec] at h
    exact h

/-! ### Comparison of the automorphism equations after extension to `L`-algebras -/

section Comparison

variable {R : Type u} [CommRing R] (f : L →+* R)

theorem algebraMap_structureConstant (i j k : Fin 8) :
    algebraMap K L ((datum hP).structureConstant i j k) =
      twistBilin P (Pi.single j 1) (Pi.single k 1) i := by
  have h := congrFun (lift_mulFun hP (Pi.single j 1) (Pi.single k 1)) i
  rw [lift_single, lift_single] at h
  exact h

omit [Field K] [Algebra K L] hP [FiniteDimensional K L] [IsGalois K L] in
theorem map_single (j : Fin 8) : (fun l => f ((Pi.single j (1 : L) : Fin 8 → L) l)) =
    (Pi.single j 1 : Fin 8 → R) := by
  funext l
  by_cases hl : l = j
  · subst hl; simp
  · simp [hl]

/-- Over any `L`-algebra the extended multiplication of the twisted datum is the Zorn product
transported along the image of `P`. -/
theorem multiplicationOver_eq (x y : Fin 8 → R) :
    (datum hP).multiplicationOver (f.comp (algebraMap K L)) x y =
      twistBilin (GeneralLinearGroup.map f P) x y := by
  funext i
  rw [SplitCayley.bilinear_apply_eq_sum (twistBilin (GeneralLinearGroup.map f P)) x y i,
    CayleyDatum.multiplicationOver]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  congr 2
  rw [RingHom.comp_apply, algebraMap_structureConstant hP]
  have h := congrFun (twistBilin_map f P (Pi.single j 1) (Pi.single k 1)) i
  rw [map_single, map_single] at h
  exact h

theorem unitOver_eq :
    (datum hP).unitOver (f.comp (algebraMap K L)) = twistUnit (GeneralLinearGroup.map f P) := by
  funext i
  rw [CayleyDatum.unitOver, RingHom.comp_apply, ← twistUnit_map f P]
  change f (algebraMap K L (unitVec K P i)) = f (twistUnit P i)
  rw [← congrFun (lift_unitVec hP) i]
  rfl

omit [FiniteDimensional K L] [IsGalois K L] hP in
theorem mulVec_eq_iff (Q : GL (Fin 8) R) (a b : Fin 8 → R) :
    (Q : Matrix (Fin 8) (Fin 8) R) *ᵥ a = b ↔
      a = ((Q⁻¹ : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R) *ᵥ b := by
  constructor
  · rintro rfl
    rw [inv_mulVec_mulVec]
  · rintro rfl
    rw [mulVec_inv_mulVec]

/-- **Comparison of automorphism equations.** Over every `L`-algebra, a matrix `h` is an
automorphism matrix of the twisted datum exactly when its conjugate `Q h Q⁻¹` by the image `Q`
of `P` is an automorphism matrix of the split datum. -/
theorem isAutomorphismMatrix_iff (h : GL (Fin 8) R) :
    (datum hP).IsAutomorphismMatrix (f.comp (algebraMap K L)) h ↔
      (CayleyDatum.split K).IsAutomorphismMatrix (f.comp (algebraMap K L))
        (GeneralLinearGroup.map f P * h * (GeneralLinearGroup.map f P)⁻¹) := by
  set Q := GeneralLinearGroup.map f P
  unfold CayleyDatum.IsAutomorphismMatrix
  rw [unitOver_eq, CayleyDatum.split_unitOver]
  simp only [multiplicationOver_eq, CayleyDatum.split_multiplicationOver, twistBilin_apply,
    twistUnit, Units.val_mul, ← Matrix.mulVec_mulVec]
  apply and_congr
  · rw [mulVec_eq_iff Q, eq_comm]
  · constructor
    · intro hm a b
      have h1 := hm (((Q⁻¹ : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R) *ᵥ a)
        (((Q⁻¹ : GL (Fin 8) R) : Matrix (Fin 8) (Fin 8) R) *ᵥ b)
      rw [mulVec_inv_mulVec, mulVec_inv_mulVec] at h1
      rw [h1, mulVec_inv_mulVec]
    · intro hm x y
      have h1 := hm ((Q : Matrix (Fin 8) (Fin 8) R) *ᵥ x) ((Q : Matrix (Fin 8) (Fin 8) R) *ᵥ y)
      rw [inv_mulVec_mulVec, inv_mulVec_mulVec] at h1
      rw [← h1, inv_mulVec_mulVec]

/-- Conjugation by the image of `P` identifies the automorphism matrices of the twisted datum
with those of the split datum, over every `L`-algebra. -/
def conjEquiv :
    (datum hP).automorphismSubgroup (f.comp (algebraMap K L)) ≃*
      (CayleyDatum.split K).automorphismSubgroup (f.comp (algebraMap K L)) where
  toFun h := ⟨GeneralLinearGroup.map f P * h.1 * (GeneralLinearGroup.map f P)⁻¹,
    (isAutomorphismMatrix_iff hP f h.1).1 h.2⟩
  invFun h := ⟨(GeneralLinearGroup.map f P)⁻¹ * h.1 * GeneralLinearGroup.map f P,
    (isAutomorphismMatrix_iff hP f _).2 (by
      have e : GeneralLinearGroup.map f P *
          ((GeneralLinearGroup.map f P)⁻¹ * h.1 * GeneralLinearGroup.map f P) *
            (GeneralLinearGroup.map f P)⁻¹ = h.1 := by group
      rw [e]
      exact h.2)⟩
  left_inv h := Subtype.ext (by simp only; group)
  right_inv h := Subtype.ext (by simp only; group)
  map_mul' g h := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjEquiv_apply (h : (datum hP).automorphismSubgroup (f.comp (algebraMap K L))) :
    ((conjEquiv hP f h : (CayleyDatum.split K).automorphismSubgroup
        (f.comp (algebraMap K L))) : GL (Fin 8) R) =
      GeneralLinearGroup.map f P * h * (GeneralLinearGroup.map f P)⁻¹ := rfl

theorem conjEquiv_symm_apply
    (h : (CayleyDatum.split K).automorphismSubgroup (f.comp (algebraMap K L))) :
    (((conjEquiv hP f).symm h : (datum hP).automorphismSubgroup
        (f.comp (algebraMap K L))) : GL (Fin 8) R) =
      (GeneralLinearGroup.map f P)⁻¹ * h * GeneralLinearGroup.map f P := rfl

end Comparison

end CayleyGaloisTwist

end Langlands.GroupScheme
