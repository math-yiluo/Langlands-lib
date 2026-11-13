import Langlands.GroupScheme.Reductive.SpecialLinearLieMatrix
import Langlands.GroupScheme.Reductive.GeneralLinearRoots
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.SpecialLinearGeometry

/-! # The diagonal torus of `SL_{n+1}` and its Lie weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.SpecialLinear.FinSucc

variable {n : ℕ}

/-! ### Weights of the diagonal entries -/

section Weights

variable (n) in
/-- The weight of the `p`-th diagonal entry of the diagonal torus of `SL_{n+1}`, in coordinates:
`e_c` at `p = c.castSucc` and `-(e_0 + ⋯ + e_{n-1})` at the last index. -/
def weightCoord (p : Fin (n + 1)) : Fin n → ℤ :=
  fun c => (if p = c.castSucc then 1 else 0) - (if p = Fin.last n then 1 else 0)

theorem weightCoord_apply (p : Fin (n + 1)) (c : Fin n) :
    weightCoord n p c =
      (if p = c.castSucc then 1 else 0) - (if p = Fin.last n then 1 else 0) :=
  rfl

theorem weightCoord_castSucc (a : Fin n) : weightCoord n a.castSucc = Pi.single a 1 := by
  funext c
  rw [weightCoord_apply, ite_eq_right_iff.mpr (fun e => absurd e (Fin.castSucc_lt_last a).ne),
    sub_zero]
  by_cases h : c = a
  · subst h
    rw [ite_eq_left_iff.mpr (fun e => absurd rfl e), Pi.single_eq_same]
  · rw [ite_eq_right_iff.mpr (fun e => absurd (Fin.castSucc_injective _ e).symm h),
      Pi.single_eq_of_ne h]

theorem weightCoord_last : weightCoord n (Fin.last n) = fun _ => -1 := by
  funext c
  simp only [weightCoord_apply, (Fin.castSucc_lt_last c).ne', ite_false, ite_true]
  norm_num

theorem sum_weightCoord (c : Fin n) : ∑ p : Fin (n + 1), weightCoord n p c = 0 := by
  simp only [weightCoord_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, sub_self]

theorem weightCoord_injective : Function.Injective (weightCoord n) := by
  intro p q h
  induction p using Fin.lastCases with
  | last =>
    induction q using Fin.lastCases with
    | last => rfl
    | cast b =>
      have h1 := congrFun h b
      rw [weightCoord_last, weightCoord_castSucc, Pi.single_eq_same] at h1
      norm_num at h1
  | cast a =>
    induction q using Fin.lastCases with
    | last =>
      have h1 := congrFun h a
      rw [weightCoord_last, weightCoord_castSucc, Pi.single_eq_same] at h1
      norm_num at h1
    | cast b =>
      have h1 := congrFun h a
      rw [weightCoord_castSucc, weightCoord_castSucc, Pi.single_eq_same] at h1
      by_contra hab
      rw [Pi.single_eq_of_ne (fun e => hab (by rw [e]))] at h1
      exact one_ne_zero h1

variable {A : Type*} [CommRing A]

/-- The `p`-th diagonal entry `∏_c τ_c ^ w(p)_c` of the diagonal torus of `SL_{n+1}`. -/
def torusEntry (τ : ULift.{u} (Fin n) → Aˣ) (p : Fin (n + 1)) : Aˣ :=
  ∏ c : ULift.{u} (Fin n), τ c ^ weightCoord n p c.down

theorem torusEntry_mul (τ σ : ULift.{u} (Fin n) → Aˣ) (p : Fin (n + 1)) :
    torusEntry (τ * σ) p = torusEntry τ p * torusEntry σ p := by
  rw [torusEntry, torusEntry, torusEntry, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun c _ => mul_zpow _ _ _

theorem torusEntry_one (p : Fin (n + 1)) : torusEntry (1 : ULift.{u} (Fin n) → Aˣ) p = 1 := by
  rw [torusEntry]
  exact Finset.prod_eq_one fun c _ => one_zpow _

omit [CommRing A] in
theorem prod_zpow_eq_zpow_sum {G J : Type*} [CommGroup G] (g : G) (s : Finset J) (f : J → ℤ) :
    ∏ i ∈ s, g ^ f i = g ^ ∑ i ∈ s, f i := by
  induction s using Finset.cons_induction with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, zpow_zero]
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, ih, zpow_add]

theorem prod_torusEntry (τ : ULift.{u} (Fin n) → Aˣ) : ∏ p, torusEntry τ p = 1 := by
  unfold torusEntry
  rw [Finset.prod_comm]
  refine Finset.prod_eq_one fun c _ => ?_
  rw [prod_zpow_eq_zpow_sum, sum_weightCoord, zpow_zero]

theorem map_torusEntry {B : Type*} [CommRing B] (f : A →* B) (τ : ULift.{u} (Fin n) → Aˣ)
    (p : Fin (n + 1)) :
    Units.map f (torusEntry τ p) = torusEntry (fun c => Units.map f (τ c)) p := by
  rw [torusEntry, torusEntry, map_prod]
  exact Finset.prod_congr rfl fun c _ => map_zpow _ _ _

theorem torusEntry_castSucc (τ : ULift.{u} (Fin n) → Aˣ) (a : Fin n) :
    torusEntry τ a.castSucc = τ ⟨a⟩ := by
  rw [torusEntry, weightCoord_castSucc,
    Finset.prod_eq_single (⟨a⟩ : ULift.{u} (Fin n)) (fun c _ hc => ?_) (by simp)]
  · simp
  · rw [Pi.single_eq_of_ne (fun h => hc (ULift.ext _ _ h)), zpow_zero]

theorem torusEntry_mulSingle (c : ULift.{u} (Fin n)) (U : Aˣ) (p : Fin (n + 1)) :
    torusEntry (Pi.mulSingle c U) p = U ^ weightCoord n p c.down :=
  GeneralLinear.prod_mulSingle_zpow (n := Fin n) c U fun d => weightCoord n p d.down

theorem prod_zpow_weightCoord_sub (τ : ULift.{u} (Fin n) → Aˣ) (p q : Fin (n + 1)) :
    ∏ c : ULift.{u} (Fin n), τ c ^ (weightCoord n p - weightCoord n q) c.down =
      torusEntry τ p * (torusEntry τ q)⁻¹ := by
  rw [torusEntry, torusEntry, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Pi.sub_apply, zpow_sub]

/-- The determinant-one diagonal matrix `diag(τ_0, …, τ_{n-1}, (τ_0 ⋯ τ_{n-1})⁻¹)`. -/
def torusMatrix (τ : ULift.{u} (Fin n) → Aˣ) : Matrix.SpecialLinearGroup (Fin (n + 1)) A :=
  ⟨Matrix.diagonal fun p => (torusEntry τ p : A), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, prod_torusEntry, Units.val_one]⟩

theorem coe_torusMatrix (τ : ULift.{u} (Fin n) → Aˣ) :
    (torusMatrix τ : Matrix (Fin (n + 1)) (Fin (n + 1)) A) =
      Matrix.diagonal fun p => (torusEntry τ p : A) :=
  rfl

variable (n A) in
/-- The diagonal matrices of the torus, as a group homomorphism. -/
def torusMatrixHom :
    (ULift.{u} (Fin n) → Aˣ) →* Matrix.SpecialLinearGroup (Fin (n + 1)) A where
  toFun := torusMatrix
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal (fun p => ((torusEntry (1 : ULift.{u} (Fin n) → Aˣ) p : Aˣ) : A)) = 1
    simp only [torusEntry_one, Units.val_one, Matrix.diagonal_one]
  map_mul' τ σ := by
    apply Subtype.ext
    change Matrix.diagonal (fun p => ((torusEntry (τ * σ) p : Aˣ) : A)) =
      Matrix.diagonal (fun p => (torusEntry τ p : A)) *
        Matrix.diagonal (fun p => (torusEntry σ p : A))
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext p
    rw [torusEntry_mul, Units.val_mul]

theorem torusMatrixHom_apply (τ : ULift.{u} (Fin n) → Aˣ) :
    torusMatrixHom n A τ = torusMatrix τ :=
  rfl

/-- In `GL_{n+1}`, the torus matrix is the diagonal matrix of its entries. -/
theorem toGL_torusMatrix (τ : ULift.{u} (Fin n) → Aˣ) :
    Matrix.SpecialLinearGroup.toGL (torusMatrix τ) =
      GeneralLinear.diagonalTorusUnits (Fin (n + 1)) A fun c => torusEntry τ c.down :=
  Units.ext rfl

theorem map_torusMatrix {B : Type*} [CommRing B] (f : A →+* B) (τ : ULift.{u} (Fin n) → Aˣ) :
    Matrix.SpecialLinearGroup.map f (torusMatrix τ) =
      torusMatrix (fun c => Units.map f.toMonoidHom (τ c)) := by
  apply Subtype.ext
  change (torusMatrix τ : Matrix (Fin (n + 1)) (Fin (n + 1)) A).map f = _
  rw [coe_torusMatrix, coe_torusMatrix, Matrix.diagonal_map (map_zero f)]
  congr 1
  funext p
  rw [← map_torusEntry]
  rfl

end Weights

/-! ### The torus -/

section Torus

variable (n) (R : CommRingCat.{u})

/-- The points of the diagonal torus of `SL_{n+1}`: a family `(τ_c)` of units goes to the point
with matrix `diag(τ_0, …, τ_{n-1}, (τ_0 ⋯ τ_{n-1})⁻¹)`. -/
def torusPoints (T : Over (Spec R)) :
    (T ⟶ (splitTorus (Spec R) (ULift.{u} (Fin n))).X) →*
      (T ⟶ (groupScheme (Fin (n + 1)) R).X) :=
  (pointsEquiv (Fin (n + 1)) R T).symm.toMonoidHom.comp
    ((torusMatrixHom n Γ(T.left, ⊤)).comp
      (splitTorus.pointsEquiv (ULift.{u} (Fin n)) T).toMonoidHom)

variable {n R} in
theorem pointsEquiv_torusPoints {T : Over (Spec R)}
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} (Fin n))).X) :
    pointsEquiv (Fin (n + 1)) R T (torusPoints n R T x) =
      torusMatrix (splitTorus.pointsEquiv (ULift.{u} (Fin n)) T x) :=
  MulEquiv.apply_symm_apply _ _

variable {n R} in
theorem torusPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} (Fin n))).X) :
    torusPoints n R T' (a ≫ x) = a ≫ torusPoints n R T x := by
  apply (pointsEquiv (Fin (n + 1)) R T').injective
  rw [pointsEquiv_naturality, pointsEquiv_torusPoints, pointsEquiv_torusPoints,
    splitTorus.pointsEquiv_naturality, map_torusMatrix]
  rfl

/-- The diagonal torus `𝔾_m^n ⟶ SL_{n+1}`, sending `(τ_c)` to
`diag(τ_0, …, τ_{n-1}, (τ_0 ⋯ τ_{n-1})⁻¹)` on points over every test scheme. -/
def diagonalTorus :
    (splitTorus.commGroupScheme (Spec R) (ULift.{u} (Fin n))).toGrp ⟶
      groupScheme (Fin (n + 1)) R :=
  homOfPoints (torusPoints n R) (fun {_ _} a x => torusPoints_naturality a x)

variable {n R}

/-- On points, the diagonal torus sends `(τ_c)` to its torus matrix. -/
theorem pointsEquiv_diagonalTorus {T : Over (Spec R)}
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} (Fin n))).X) :
    pointsEquiv (Fin (n + 1)) R T (x ≫ (diagonalTorus n R).hom.hom) =
      torusMatrix (splitTorus.pointsEquiv (ULift.{u} (Fin n)) T x) := by
  rw [diagonalTorus, comp_homOfPoints, pointsEquiv_torusPoints]

/-- The diagonal torus is injective on points. -/
instance mono_diagonalTorus_hom : Mono (diagonalTorus n R).hom.hom := by
  constructor
  intro Z g h hgh
  apply (splitTorus.pointsEquiv (ULift.{u} (Fin n)) Z).injective
  have h1 := congrArg (pointsEquiv (Fin (n + 1)) R Z) hgh
  rw [pointsEquiv_diagonalTorus, pointsEquiv_diagonalTorus] at h1
  funext c
  have h2 := congrArg (fun m : Matrix.SpecialLinearGroup (Fin (n + 1)) Γ(Z.left, ⊤) =>
    (m : Matrix (Fin (n + 1)) (Fin (n + 1)) Γ(Z.left, ⊤)) c.down.castSucc c.down.castSucc) h1
  simp only [coe_torusMatrix, Matrix.diagonal_apply_eq, torusEntry_castSucc] at h2
  exact Units.ext h2

/-- The coordinates of an affine point of the split torus are the images of its scheme-point
coordinates under the affine comparison of global sections. -/
theorem units_map_pointsEquiv_eq_torusCoords {A : Type u} [CommRing A] [Algebra R A]
    (t : Lie.AffinePoints (splitTorus.commGroupScheme (Spec R) (ULift.{u} (Fin n))).toGrp A) :
    (fun c => Units.map
        (Corepresented.affineSectionsIso (CommAlgCat.of R A)).hom.hom.toRingHom.toMonoidHom
        (splitTorus.pointsEquiv (ULift.{u} (Fin n)) ((algSpec R).obj (op (CommAlgCat.of R A)))
          t c)) =
      GeneralLinear.torusCoords t := by
  funext c
  apply Units.ext
  exact DFunLike.congr_fun (Corepresented.affineSectionsIso_hom_ringHom (CommAlgCat.of R A)) _

/-- An affine point of the diagonal torus, viewed in `GL_{n+1}`, is the diagonal matrix of its
torus entries. -/
theorem affinePointsEquiv_diagonalTorus_inclusion {A : Type u} [CommRing A] [Algebra R A]
    (t : Lie.AffinePoints (splitTorus.commGroupScheme (Spec R) (ULift.{u} (Fin n))).toGrp A) :
    GeneralLinear.affinePointsEquiv (Fin (n + 1)) R (CommAlgCat.of R A)
        (t ≫ (diagonalTorus n R ≫ inclusion (Fin (n + 1)) R).hom.hom) =
      GeneralLinear.diagonalTorusUnits (Fin (n + 1)) A
        (fun c : ULift.{u} (Fin (n + 1)) => torusEntry (GeneralLinear.torusCoords t) c.down) := by
  rw [GeneralLinear.affinePointsEquiv_eq_map_pointsEquiv, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion, pointsEquiv_diagonalTorus, toGL_torusMatrix]
  erw [GeneralLinear.map_diagonalTorusUnits]
  rw [← units_map_pointsEquiv_eq_torusCoords]
  congr 1
  funext c
  exact map_torusEntry _ _ _

end Torus

/-! ### Over a field -/

section Field

variable (n) (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))

/-- The published instance `isAffineHom_groupScheme`, restated for bases `CommRingCat.of k`. -/
instance isAffineHom_groupScheme_of :
    IsAffineHom (groupScheme (Fin (n + 1)) (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme (n := Fin (n + 1)) (R := CommRingCat.of k)

/-- The published `smooth_groupScheme`, as an instance for bases `CommRingCat.of k`. -/
instance smooth_groupScheme_of : Smooth (groupScheme (Fin (n + 1)) (CommRingCat.of k)).X.hom :=
  smooth_groupScheme (Fin (n + 1)) 0 (CommRingCat.of k)

/-- The published `connectedSpace_groupScheme`, as an instance. -/
instance connectedSpace_groupScheme_of :
    ConnectedSpace (groupScheme (Fin (n + 1)) (CommRingCat.of k)).X.left :=
  connectedSpace_groupScheme (Fin (n + 1)) 0 k

instance isAffineHom_diagonalTorusSource : IsAffineHom (𝔻).X.hom :=
  isAffineHom_splitTorus _ _

theorem isSplitTorus_diagonalTorus : IsSplitTorus (𝔻).toGrp :=
  isSplitTorus_splitTorus _

/-- The diagonal torus is a closed subgroup. -/
theorem isClosedSubgroup_diagonalTorus :
    IsClosedSubgroup (diagonalTorus n (CommRingCat.of k)) :=
  IsTorus.isClosedSubgroup_of_mono (IsSplitTorus.isTorus (isSplitTorus_diagonalTorus n k)) _

theorem isSplitSubtorus_diagonalTorus : IsSplitSubtorus (diagonalTorus n (CommRingCat.of k)) :=
  ⟨isSplitTorus_diagonalTorus n k, isClosedSubgroup_diagonalTorus n k⟩

variable {n k}

/-- The value of a character on an affine point of the diagonal torus, in coordinates. -/
theorem characterValue_eq_prod (χ : characterLattice 𝔻) {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (𝔻).toGrp A) :
    Lie.characterValue χ t =
      ∏ c : ULift.{u} (Fin n), GeneralLinear.torusCoords t c ^
        GeneralLinear.characterCoordEquiv (Fin n) k χ c.down := by
  have h := GeneralLinear.characterValue_characterLatticeEquiv_symm
    (splitTorus.characterLatticeEquiv k (ULift.{u} (Fin n)) χ) t
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-- Membership in a weight space of the diagonal torus, entrywise in the matrix coordinates. -/
theorem mem_weightSpace_diagonalTorus_iff
    (X : Additive (lieKernel (groupScheme (Fin (n + 1)) (CommRingCat.of k)) k))
    (χ : characterLattice 𝔻) :
    X ∈ weightSpace (diagonalTorus n (CommRingCat.of k)) χ ↔
      ∀ (A : Type u) [CommRing A] [Algebra k A] (t : Lie.AffinePoints (𝔻).toGrp A)
        (p q : Fin (n + 1)),
        (torusEntry (GeneralLinear.torusCoords t) p : A) * algebraMap k A (lieMatrix X p q) *
            (((torusEntry (GeneralLinear.torusCoords t) q)⁻¹ : Aˣ) : A) =
          (Lie.characterValue χ t : A) * algebraMap k A (lieMatrix X p q) := by
  rw [← lieKernelHomLinear_mem_weightSpace_iff (inclusion (Fin (n + 1)) (CommRingCat.of k)),
    ← pointKernelLinearEquiv_lieMatrix, mem_weightSpace]
  refine forall_congr' fun A => ?_
  refine ⟨fun h _ _ t a b => ?_, fun h _ _ t => ?_⟩
  · have h1 := h t
    rw [GeneralLinear.DualNumber.pointKernelLinearEquiv_naturality,
      GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, ← map_smul,
      EmbeddingLike.apply_eq_iff_eq, affinePointsEquiv_diagonalTorus_inclusion] at h1
    have h2 := congrFun (congrFun h1 a) b
    simpa only [GeneralLinear.coe_diagonalTorusUnits, GeneralLinear.coe_inv_diagonalTorusUnits,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Algebra.ofId_apply] using h2
  · rw [GeneralLinear.DualNumber.pointKernelLinearEquiv_naturality,
      GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, ← map_smul,
      affinePointsEquiv_diagonalTorus_inclusion]
    congr 1
    ext a b
    simpa only [GeneralLinear.coe_diagonalTorusUnits, GeneralLinear.coe_inv_diagonalTorusUnits,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Algebra.ofId_apply] using h t a b

/-- **Weights of the diagonal torus.** An element of the Lie algebra of `SL_{n+1}` lies in the
weight space of `χ` exactly when every nonzero entry of its matrix at `(p, q)` has weight
`χ = w(p) - w(q)`. -/
theorem mem_weightSpace_diagonalTorus_iff_support
    (X : Additive (lieKernel (groupScheme (Fin (n + 1)) (CommRingCat.of k)) k))
    (χ : characterLattice 𝔻) :
    X ∈ weightSpace (diagonalTorus n (CommRingCat.of k)) χ ↔
      ∀ p q : Fin (n + 1), lieMatrix X p q ≠ 0 →
        GeneralLinear.characterCoordEquiv (Fin n) k χ = weightCoord n p - weightCoord n q := by
  rw [mem_weightSpace_diagonalTorus_iff]
  constructor
  · intro hX x y hxy
    funext c
    have h1 := hX k[T;T⁻¹] (GeneralLinear.affineTorusPoint (R := CommRingCat.of k)
      (Pi.mulSingle ⟨c⟩ (Gm.relativeCoordUnit k))) x y
    rw [characterValue_eq_prod, GeneralLinear.torusCoords_affineTorusPoint,
      GeneralLinear.prod_mulSingle_zpow, torusEntry_mulSingle, torusEntry_mulSingle,
      ← zpow_neg, Gm.relativeCoordUnit_zpow_val, Gm.relativeCoordUnit_zpow_val,
      Gm.relativeCoordUnit_zpow_val, ← LaurentPolynomial.C_eq_algebraMap] at h1
    refine (GeneralLinear.exponent_eq_of_C_mul_T hxy ?_).symm
    have h1' : LaurentPolynomial.T (weightCoord n x c) * LaurentPolynomial.C (lieMatrix X x y) *
        LaurentPolynomial.T (-weightCoord n y c) =
        LaurentPolynomial.T (GeneralLinear.characterCoordEquiv (Fin n) k χ c) *
          LaurentPolynomial.C (lieMatrix X x y) := h1
    rw [Pi.sub_apply, sub_eq_add_neg, LaurentPolynomial.T_add]
    linear_combination -h1'
  · intro hsupp A _ _ t x y
    by_cases hxy : lieMatrix X x y = 0
    · rw [hxy, map_zero, mul_zero, zero_mul, mul_zero]
    · have hχ := characterValue_eq_prod χ t
      rw [hsupp x y hxy, prod_zpow_weightCoord_sub] at hχ
      rw [hχ, Units.val_mul]
      ring

end Field

end Langlands.GroupScheme.SpecialLinear.FinSucc
