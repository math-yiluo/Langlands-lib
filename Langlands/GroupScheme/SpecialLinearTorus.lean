import Langlands.GroupScheme.Reductive.SpecialLinear
import Langlands.GroupScheme.Lie.GeneralLinearAdjoint
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Reductive.GeneralLinearRoots
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed
import Langlands.GroupScheme.Torus.SelfCentralizingFromLie
import Langlands.GroupScheme.Lie.SplitTorusCoordinates

/-! # Lie coordinates and the diagonal torus of the split special linear group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.SpecialLinear

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Dual-number determinant-one matrices -/

section DualNumber

open GeneralLinear.DualNumber

variable {A : Type u} [CommRing A]

/-- `det (1 + εY) = 1 + ε tr Y` over the dual numbers. -/
theorem det_one_add_epsilonMatrix (Y : Matrix n n A) :
    (1 + epsilonMatrix Y).det = 1 + TrivSqZeroExt.inr (Matrix.trace Y) := by
  have hY : epsilonMatrix Y =
      (TrivSqZeroExt.inr (1 : A) : DualNumber A) • Y.map (TrivSqZeroExt.inl (M := A)) := by
    refine Matrix.ext fun i j => ?_
    simp only [epsilonMatrix_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.snd_mul]
  rw [hY, Matrix.det_one_add_smul]
  have hsq : (TrivSqZeroExt.inr (1 : A) : DualNumber A) ^ 2 = 0 := by
    rw [pow_two, TrivSqZeroExt.inr_mul_inr]
  rw [hsq, mul_zero, add_zero]
  congr 1
  have htr : Matrix.trace (Y.map (TrivSqZeroExt.inl (M := A))) =
      TrivSqZeroExt.inl (Matrix.trace Y) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.map_apply]
    exact (map_sum (TrivSqZeroExt.inlHom A A) _ _).symm
  rw [htr]
  refine TrivSqZeroExt.ext ?_ ?_ <;> simp [TrivSqZeroExt.snd_mul]

omit [Fintype n] [DecidableEq n] in
theorem epsilonMatrix_eq_zero_iff (Y : Matrix n n A) :
    epsilonMatrix Y = 0 ↔ Y = 0 := by
  constructor
  · intro h
    ext i j
    have h1 := congrArg (fun M : Matrix n n (DualNumber A) => TrivSqZeroExt.snd (M i j)) h
    simpa using h1
  · rintro rfl
    exact epsilonMatrix_zero

/-- `1 + εY` has determinant one exactly when `tr Y = 0`. -/
theorem one_add_epsilonMatrix_det_eq_one_iff (Y : Matrix n n A) :
    (1 + epsilonMatrix Y).det = 1 ↔ Matrix.trace Y = 0 := by
  rw [det_one_add_epsilonMatrix, add_eq_left]
  constructor
  · intro h
    simpa using congrArg TrivSqZeroExt.snd h
  · intro h
    rw [h, TrivSqZeroExt.inr_zero]

end DualNumber

/-! ### Lie coordinates -/

section Lie

open GeneralLinear.DualNumber

variable {R : CommRingCat.{u}} {A : Type u} [CommRing A] [Algebra R A]

/-- On affine points, the inclusion into `GL_n` is the inclusion of matrices. -/
theorem affinePointsEquiv_inclusion (S : CommAlgCat.{u} R)
    (f : (algSpec R).obj (op S) ⟶ (groupScheme n R).X) :
    GeneralLinear.affinePointsEquiv n R S (f ≫ (inclusion n R).hom.hom) =
      Matrix.SpecialLinearGroup.toGL (affinePointsEquiv n R S f) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ f

/-- The matrix coordinates of the Lie algebra of `SL_n`, through the inclusion into `GL_n`
and the published coordinates of the Lie algebra of `GL_n`. -/
def lieMatrix : Additive (lieKernel (groupScheme n R) A) →ₗ[A] Matrix n n A :=
  (pointKernelLinearEquiv (n := n) (R := R) (A := A)).symm.toLinearMap ∘ₗ
    Lie.targetMapLinear (inclusion n R) A

theorem pointKernelLinearEquiv_lieMatrix (X : Additive (lieKernel (groupScheme n R) A)) :
    pointKernelLinearEquiv (lieMatrix X) = Lie.targetMapLinear (inclusion n R) A X :=
  LinearEquiv.apply_symm_apply _ _

/-- The inclusion of `SL_n` into `GL_n` is a monomorphism of schemes. -/
instance mono_inclusion : Mono (inclusion n R).hom.hom := by
  constructor
  intro Z g h hgh
  apply (pointsEquiv n R Z).injective
  have h1 := congrArg (GeneralLinear.pointsEquiv n R Z) hgh
  rw [pointsEquiv_inclusion, pointsEquiv_inclusion] at h1
  apply Subtype.ext
  exact congrArg (fun g : GL n Γ(Z.left, ⊤) => g.val) h1

theorem lieMatrix_injective :
    Function.Injective (lieMatrix (n := n) (R := R) (A := A)) :=
  (pointKernelLinearEquiv (n := n) (R := R) (A := A)).symm.injective.comp
    (Lie.targetMapLinear_injective (inclusion n R) A)

/-- The affine dual-number matrix of an element of the Lie kernel of `SL_n` is `1 + εY` for its
coordinate matrix `Y`. -/
theorem affinePointsEquiv_lieKernel (X : Additive (lieKernel (groupScheme n R) A)) :
    ((affinePointsEquiv n R (CommAlgCat.of R (DualNumber A)) X.toMul.val :
        Matrix.SpecialLinearGroup n (DualNumber A)) : Matrix n n (DualNumber A)) =
      1 + epsilonMatrix (lieMatrix X) := by
  have h1 := pointKernelLinearEquiv_lieMatrix X
  have h2 := congrArg (fun x : Additive (lieKernel (GeneralLinear.groupScheme n R) A) =>
    GeneralLinear.affinePointsEquiv n R (CommAlgCat.of R (DualNumber A)) x.toMul.val) h1
  simp only [pointKernelLinearEquiv_toMul, pointKernelEquiv_val, lieKernelHomLinear_val] at h2
  have h4 := affinePointsEquiv_inclusion (n := n) (R := R) (CommAlgCat.of R (DualNumber A))
    X.toMul.val
  have h5 := pointUnit_matrix (n := n) (R := R) (lieMatrix X)
  have h6 := h4.symm.trans (h2.symm.trans h5)
  exact congrArg (fun g : GL n (DualNumber A) => g.val) h6

/-- The Lie algebra of `SL_n` consists of trace-zero matrices. -/
theorem trace_lieMatrix (X : Additive (lieKernel (groupScheme n R) A)) :
    Matrix.trace (lieMatrix X) = 0 := by
  rw [← one_add_epsilonMatrix_det_eq_one_iff, ← affinePointsEquiv_lieKernel]
  exact (affinePointsEquiv n R (CommAlgCat.of R (DualNumber A)) X.toMul.val).property

/-- Conversely every trace-zero matrix is the coordinate matrix of an element of the Lie algebra
of `SL_n`. -/
theorem exists_lieMatrix_eq (Y : Matrix n n A) (hY : Matrix.trace Y = 0) :
    ∃ X : Additive (lieKernel (groupScheme n R) A), lieMatrix X = Y := by
  let g : Matrix.SpecialLinearGroup n (DualNumber A) :=
    ⟨1 + epsilonMatrix Y, (one_add_epsilonMatrix_det_eq_one_iff Y).mpr hY⟩
  let p := (affinePointsEquiv n R (CommAlgCat.of R (DualNumber A))).symm g
  have hp : p ≫ (inclusion n R).hom.hom = (pointUnit Y : GeneralLinear.DualNumber.AffinePoints
      n R (DualNumber A)) := by
    apply (GeneralLinear.affinePointsEquiv n R (CommAlgCat.of R (DualNumber A))).injective
    rw [affinePointsEquiv_inclusion, pointUnit_matrix]
    apply Units.ext
    change ((affinePointsEquiv n R _ p : Matrix.SpecialLinearGroup n (DualNumber A)) :
      Matrix n n (DualNumber A)) = 1 + epsilonMatrix Y
    rw [MulEquiv.apply_symm_apply]
  have hred : Lie.reduction (groupScheme n R) p = 1 := by
    apply (cancel_mono (inclusion n R).hom.hom).mp
    rw [MonObj.one_comp]
    have h : Lie.reduction (groupScheme n R) p ≫ (inclusion n R).hom.hom =
        Lie.reduction (GeneralLinear.groupScheme n R) (p ≫ (inclusion n R).hom.hom) :=
      Category.assoc _ _ _
    rw [h, hp]
    exact pointReduction_pointUnit Y
  refine ⟨Additive.ofMul ⟨p, hred⟩, ?_⟩
  apply (pointKernelLinearEquiv (n := n) (R := R) (A := A)).injective
  rw [pointKernelLinearEquiv_lieMatrix]
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hp

end Lie

/-! ### Weights of the diagonal torus -/

section Weights

variable (p : n)

/-- The indices other than the pivot `p`; they index the coordinates of the diagonal torus. -/
abbrev OffPivot : Type := {c : n // c ≠ p}

/-- The weight of the diagonal entry `x` of the diagonal torus, in coordinates: `e_x` for
`x ≠ p`, and `-∑_c e_c` at the pivot. -/
def weightCoord (x : n) : OffPivot p → ℤ :=
  if h : x = p then fun _ => -1 else Pi.single ⟨x, h⟩ 1

omit [Fintype n] in
@[simp] theorem weightCoord_pivot : weightCoord p p = fun _ => -1 := by simp [weightCoord]

omit [Fintype n] in
theorem weightCoord_of_ne {x : n} (h : x ≠ p) : weightCoord p x = Pi.single ⟨x, h⟩ 1 := by
  simp [weightCoord, h]

omit [Fintype n] in
@[simp] theorem weightCoord_val (c : OffPivot p) : weightCoord p c.1 = Pi.single c 1 :=
  weightCoord_of_ne p c.2

omit [Fintype n] in
/-- Every weight coordinate is `-1`, `0` or `1`. -/
theorem weightCoord_apply_mem (x : n) (c : OffPivot p) :
    -1 ≤ weightCoord p x c ∧ weightCoord p x c ≤ 1 := by
  by_cases h : x = p
  · subst h
    simp
  · rw [weightCoord_of_ne p h, Pi.single_apply]
    split_ifs <;> omega

/-- The weights of all diagonal entries sum to zero. -/
theorem sum_weightCoord (c : OffPivot p) : ∑ x, weightCoord p x c = 0 := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ p]
  simp [Pi.single_apply]

omit [Fintype n] in
theorem weightCoord_injective : Function.Injective (weightCoord p) := by
  intro x y h
  by_cases hx : x = p <;> by_cases hy : y = p
  · rw [hx, hy]
  · exfalso
    have h1 := congrFun h ⟨y, hy⟩
    simp [hx, weightCoord_of_ne p hy] at h1
  · exfalso
    have h1 := congrFun h ⟨x, hx⟩
    simp [hy, weightCoord_of_ne p hx] at h1
  · have h1 := congrFun h ⟨x, hx⟩
    rw [weightCoord_of_ne p hx, weightCoord_of_ne p hy, Pi.single_eq_same, Pi.single_apply] at h1
    split_ifs at h1 with hxy
    · exact congrArg Subtype.val hxy
    · omega

variable {A : Type*} [CommRing A]

/-- The diagonal entries `∏_c τ_c ^ (weightCoord p x)_c` of the torus point with coordinates `τ`:
`τ_x` for `x ≠ p`, and `(∏_c τ_c)⁻¹` at the pivot. -/
def torusWeights (τ : ULift.{u} (OffPivot p) → Aˣ) (x : n) : Aˣ :=
  ∏ c : ULift.{u} (OffPivot p), τ c ^ weightCoord p x c.down

theorem torusWeights_val (τ : ULift.{u} (OffPivot p) → Aˣ) (c : OffPivot p) :
    torusWeights p τ c.1 = τ ⟨c⟩ := by
  rw [torusWeights, weightCoord_val,
    Finset.prod_eq_single (⟨c⟩ : ULift.{u} (OffPivot p)) (fun d _ hd => ?_) (by simp)]
  · simp
  · rw [Pi.single_eq_of_ne (fun h => hd (ULift.ext _ _ h)), zpow_zero]

theorem torusWeights_pivot (τ : ULift.{u} (OffPivot p) → Aˣ) :
    torusWeights p τ p = (∏ c, τ c)⁻¹ := by
  rw [torusWeights, weightCoord_pivot, ← Finset.prod_inv_distrib]
  simp only [zpow_neg_one]

/-- The diagonal entries multiply to one. -/
theorem prod_torusWeights (τ : ULift.{u} (OffPivot p) → Aˣ) : ∏ x, torusWeights p τ x = 1 := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ p, torusWeights_pivot]
  have h : ∏ i : {i // i ≠ p}, torusWeights p τ i.1 = ∏ c, τ c :=
    Fintype.prod_equiv Equiv.ulift.symm _ _ (fun i => torusWeights_val p τ i)
  rw [h, inv_mul_cancel]

theorem torusWeights_mul (τ σ : ULift.{u} (OffPivot p) → Aˣ) (x : n) :
    torusWeights p (τ * σ) x = torusWeights p τ x * torusWeights p σ x := by
  simp only [torusWeights, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem torusWeights_one (x : n) :
    torusWeights p (1 : ULift.{u} (OffPivot p) → Aˣ) x = 1 := by
  simp [torusWeights]

theorem map_torusWeights {B : Type*} [CommRing B] (f : A →+* B)
    (τ : ULift.{u} (OffPivot p) → Aˣ) (x : n) :
    Units.map f.toMonoidHom (torusWeights p τ x) =
      torusWeights p (fun c => Units.map f.toMonoidHom (τ c)) x := by
  simp only [torusWeights, map_prod, map_zpow]

theorem torusWeights_mulSingle (c : ULift.{u} (OffPivot p)) (U : Aˣ) (x : n) :
    torusWeights p (Pi.mulSingle c U) x = U ^ weightCoord p x c.down :=
  GeneralLinear.prod_mulSingle_zpow (n := OffPivot p) c U fun d => weightCoord p x d.down

theorem prod_zpow_weightCoord_sub (τ : ULift.{u} (OffPivot p) → Aˣ) (x y : n) :
    ∏ c : ULift.{u} (OffPivot p), τ c ^ (weightCoord p x - weightCoord p y) c.down =
      torusWeights p τ x * (torusWeights p τ y)⁻¹ := by
  rw [torusWeights, torusWeights, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Pi.sub_apply, zpow_sub]

variable (A) in
/-- The determinant-one diagonal matrix `diag(torusWeights τ)`. -/
def torusUnits : (ULift.{u} (OffPivot p) → Aˣ) →* Matrix.SpecialLinearGroup n A where
  toFun τ := ⟨Matrix.diagonal fun x => (torusWeights p τ x : A), by
    rw [Matrix.det_diagonal, ← Units.coe_prod, prod_torusWeights, Units.val_one]⟩
  map_one' := by
    apply Subtype.ext
    simp only [torusWeights_one, Units.val_one, Matrix.diagonal_one]
    rfl
  map_mul' τ σ := by
    apply Subtype.ext
    change Matrix.diagonal _ = Matrix.diagonal _ * Matrix.diagonal _
    rw [Matrix.diagonal_mul_diagonal]
    simp only [torusWeights_mul, Units.val_mul]

theorem coe_torusUnits (τ : ULift.{u} (OffPivot p) → Aˣ) :
    ((torusUnits p A τ : Matrix.SpecialLinearGroup n A) : Matrix n n A) =
      Matrix.diagonal fun x => (torusWeights p τ x : A) :=
  rfl

theorem toGL_torusUnits (τ : ULift.{u} (OffPivot p) → Aˣ) :
    Matrix.SpecialLinearGroup.toGL (torusUnits p A τ) =
      GeneralLinear.diagonalTorusUnits n A (fun c : ULift.{u} n => torusWeights p τ c.down) := by
  apply Units.ext
  rfl

theorem map_torusUnits {B : Type*} [CommRing B] (f : A →+* B) (τ : ULift.{u} (OffPivot p) → Aˣ) :
    Matrix.SpecialLinearGroup.map f (torusUnits p A τ) =
      torusUnits p B (fun c => Units.map f.toMonoidHom (τ c)) := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, coe_torusUnits,
    Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs
  · rw [← map_torusWeights]
    rfl
  · exact map_zero f

end Weights

/-! ### The diagonal torus -/

section Torus

variable (p : n) (R : CommRingCat.{u})

/-- The points of the diagonal torus over a test scheme `T`: coordinates `(τ_c)` go to the
determinant-one diagonal matrix `diag(torusWeights τ)`. -/
def diagonalTorusPoints (T : Over (Spec R)) :
    (T ⟶ (splitTorus (Spec R) (ULift.{u} (OffPivot p))).X) →* (T ⟶ (groupScheme n R).X) :=
  (pointsEquiv n R T).symm.toMonoidHom.comp
    ((torusUnits p Γ(T.left, ⊤)).comp
      (splitTorus.pointsEquiv (ULift.{u} (OffPivot p)) T).toMonoidHom)

variable {p R} in
theorem pointsEquiv_diagonalTorusPoints {T : Over (Spec R)}
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} (OffPivot p))).X) :
    pointsEquiv n R T (diagonalTorusPoints p R T x) =
      torusUnits p Γ(T.left, ⊤) (splitTorus.pointsEquiv (ULift.{u} (OffPivot p)) T x) :=
  MulEquiv.apply_symm_apply _ _

variable {p R} in
theorem diagonalTorusPoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} (OffPivot p))).X) :
    diagonalTorusPoints p R T' (a ≫ x) = a ≫ diagonalTorusPoints p R T x := by
  apply (pointsEquiv n R T').injective
  rw [pointsEquiv_naturality, pointsEquiv_diagonalTorusPoints, pointsEquiv_diagonalTorusPoints,
    splitTorus.pointsEquiv_naturality, map_torusUnits]
  rfl

/-- The diagonal torus of `SL_n` of rank `|n| - 1`, with coordinates indexed by the indices other
than the pivot `p`: it sends `(τ_c)` to `diag(τ_c)` with `(∏_c τ_c)⁻¹` at the pivot. -/
def diagonalTorus :
    (splitTorus.commGroupScheme (Spec R) (ULift.{u} (OffPivot p))).toGrp ⟶ groupScheme n R :=
  homOfPoints (diagonalTorusPoints p R) (fun {_ _} a x => diagonalTorusPoints_naturality a x)

variable {p R}

/-- On points, the diagonal torus sends `(τ_c)` to `diag(torusWeights τ)`. -/
theorem pointsEquiv_diagonalTorus {T : Over (Spec R)}
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} (OffPivot p))).X) :
    pointsEquiv n R T (x ≫ (diagonalTorus p R).hom.hom) =
      torusUnits p Γ(T.left, ⊤) (splitTorus.pointsEquiv (ULift.{u} (OffPivot p)) T x) := by
  rw [diagonalTorus, comp_homOfPoints, pointsEquiv_diagonalTorusPoints]

/-- The diagonal torus is injective on points. -/
instance mono_diagonalTorus_hom : Mono (diagonalTorus p R).hom.hom := by
  constructor
  intro Z g h hgh
  apply (splitTorus.pointsEquiv (ULift.{u} (OffPivot p)) Z).injective
  have h1 := congrArg (pointsEquiv n R Z) hgh
  rw [pointsEquiv_diagonalTorus, pointsEquiv_diagonalTorus] at h1
  funext c
  apply Units.ext
  have h2 := congrArg (fun m : Matrix.SpecialLinearGroup n Γ(Z.left, ⊤) =>
    (m : Matrix n n Γ(Z.left, ⊤)) c.down.1 c.down.1) h1
  simpa only [coe_torusUnits, Matrix.diagonal_apply_eq, torusWeights_val] using h2

/-- An affine point of the diagonal torus, viewed in `GL_n`, is the diagonal matrix of its
weights. -/
theorem affinePointsEquiv_diagonalTorus_inclusion {A : Type u} [CommRing A] [Algebra R A]
    (t : Lie.AffinePoints
      (splitTorus.commGroupScheme (Spec R) (ULift.{u} (OffPivot p))).toGrp A) :
    GeneralLinear.affinePointsEquiv n R (CommAlgCat.of R A)
        (t ≫ (diagonalTorus p R ≫ inclusion n R).hom.hom) =
      GeneralLinear.diagonalTorusUnits n A
        (fun c : ULift.{u} n => torusWeights p (GeneralLinear.torusCoords t) c.down) := by
  rw [GeneralLinear.affinePointsEquiv_eq_map_pointsEquiv, Grp.comp_hom_hom, ← Category.assoc,
    pointsEquiv_inclusion, pointsEquiv_diagonalTorus, toGL_torusUnits]
  erw [GeneralLinear.map_diagonalTorusUnits]
  congr 1
  funext c
  refine (map_torusWeights p _ _ _).trans ?_
  congr 1
  funext d
  apply Units.ext
  exact DFunLike.congr_fun
    (Corepresented.affineSectionsIso_hom_ringHom (CommAlgCat.of R A)) _

end Torus

/-! ### Weight spaces over a field -/

section Field

variable (n) (p : n) (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (OffPivot p))

/-- The published instance `isAffineHom_groupScheme`, restated for bases `CommRingCat.of k`. -/
instance isAffineHom_groupScheme_of : IsAffineHom (groupScheme n (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme (n := n) (R := CommRingCat.of k)

/-- The published smoothness of `SL_n` (which needs some index as a pivot), as an instance over
fields for nonempty index types. -/
instance smooth_groupScheme_of [Nonempty n] : Smooth (groupScheme n (CommRingCat.of k)).X.hom :=
  smooth_groupScheme n (Classical.arbitrary n) _

/-- The published connectedness of `SL_n` over a field, as an instance for nonempty index
types. -/
instance connectedSpace_groupScheme_of [Nonempty n] :
    ConnectedSpace (groupScheme n (CommRingCat.of k)).X.left :=
  connectedSpace_groupScheme n (Classical.arbitrary n) k

instance isAffineHom_diagonalTorusSource : IsAffineHom (𝔻).X.hom :=
  isAffineHom_splitTorus _ _

omit [DecidableEq n] in
theorem isSplitTorus_diagonalTorus : IsSplitTorus (𝔻).toGrp :=
  isSplitTorus_splitTorus _

/-- The diagonal torus is a closed subgroup. -/
theorem isClosedSubgroup_diagonalTorus :
    IsClosedSubgroup (diagonalTorus p (CommRingCat.of k)) :=
  have : Nonempty n := ⟨p⟩
  IsTorus.isClosedSubgroup_of_mono (IsSplitTorus.isTorus (isSplitTorus_diagonalTorus n p k)) _

theorem isSplitSubtorus_diagonalTorus : IsSplitSubtorus (diagonalTorus p (CommRingCat.of k)) :=
  ⟨isSplitTorus_diagonalTorus n p k, isClosedSubgroup_diagonalTorus n p k⟩

variable {n p k}

/-- The value of a character on an affine point of the diagonal torus, in coordinates. -/
theorem characterValue_eq_prod (χ : characterLattice 𝔻) {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (𝔻).toGrp A) :
    Lie.characterValue χ t =
      ∏ c : ULift.{u} (OffPivot p), GeneralLinear.torusCoords t c ^
        GeneralLinear.characterCoordEquiv (OffPivot p) k χ c.down := by
  have h := GeneralLinear.characterValue_characterLatticeEquiv_symm
    (splitTorus.characterLatticeEquiv k (ULift.{u} (OffPivot p)) χ) t
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-- Membership in a weight space of the diagonal torus, entrywise in the matrix coordinates. -/
theorem mem_weightSpace_diagonalTorus_iff
    (X : Additive (lieKernel (groupScheme n (CommRingCat.of k)) k)) (χ : characterLattice 𝔻) :
    X ∈ weightSpace (diagonalTorus p (CommRingCat.of k)) χ ↔
      ∀ (A : Type u) [CommRing A] [Algebra k A] (t : Lie.AffinePoints (𝔻).toGrp A) (x y : n),
        (torusWeights p (GeneralLinear.torusCoords t) x : A) * algebraMap k A (lieMatrix X x y) *
            (((torusWeights p (GeneralLinear.torusCoords t) y)⁻¹ : Aˣ) : A) =
          (Lie.characterValue χ t : A) * algebraMap k A (lieMatrix X x y) := by
  rw [← lieKernelHomLinear_mem_weightSpace_iff (inclusion n (CommRingCat.of k)),
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

/-- **Weights of the diagonal torus.** An element of the Lie algebra of `SL_n` lies in the weight
space of `χ` exactly when every nonzero entry of its matrix at `(x, y)` has weight
`χ = w(x) - w(y)`, where `w(x) = e_x` for `x ≠ p` and `w(p) = -∑_c e_c`. -/
theorem mem_weightSpace_diagonalTorus_iff_support
    (X : Additive (lieKernel (groupScheme n (CommRingCat.of k)) k)) (χ : characterLattice 𝔻) :
    X ∈ weightSpace (diagonalTorus p (CommRingCat.of k)) χ ↔
      ∀ x y : n, lieMatrix X x y ≠ 0 →
        GeneralLinear.characterCoordEquiv (OffPivot p) k χ = weightCoord p x - weightCoord p y := by
  rw [mem_weightSpace_diagonalTorus_iff]
  constructor
  · intro hX x y hxy
    funext c
    have h1 := hX k[T;T⁻¹] (GeneralLinear.affineTorusPoint (R := CommRingCat.of k)
      (Pi.mulSingle ⟨c⟩ (Gm.relativeCoordUnit k))) x y
    rw [characterValue_eq_prod, GeneralLinear.torusCoords_affineTorusPoint,
      GeneralLinear.prod_mulSingle_zpow, torusWeights_mulSingle, torusWeights_mulSingle,
      ← zpow_neg, Gm.relativeCoordUnit_zpow_val, Gm.relativeCoordUnit_zpow_val,
      Gm.relativeCoordUnit_zpow_val, ← LaurentPolynomial.C_eq_algebraMap] at h1
    refine (GeneralLinear.exponent_eq_of_C_mul_T hxy ?_).symm
    have h1' : LaurentPolynomial.T (weightCoord p x c) * LaurentPolynomial.C (lieMatrix X x y) *
        LaurentPolynomial.T (-weightCoord p y c) =
        LaurentPolynomial.T (GeneralLinear.characterCoordEquiv (OffPivot p) k χ c) *
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

end Langlands.GroupScheme.SpecialLinear
