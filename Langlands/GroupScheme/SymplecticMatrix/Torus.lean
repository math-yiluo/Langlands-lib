import Langlands.GroupScheme.SymplecticMatrix.LieAlgebra
import Langlands.GroupScheme.Reductive.GeneralLinearRoots
import Langlands.GroupScheme.Torus.UnipotentQuotientClosed

/-! # The diagonal torus of the split symplectic group and its Lie weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.SymplecticMatrix

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### Weights of diagonal matrices -/

section Weights

variable {A : Type*} [CommRing A]

/-- The diagonal entries `t_a` (at `inl a`) and `t_a⁻¹` (at `inr a`) of `diag(t, t⁻¹)`. -/
def torusWeights (τ : ULift.{u} l → Aˣ) : l ⊕ l → Aˣ :=
  Sum.elim (fun a => τ ⟨a⟩) (fun a => (τ ⟨a⟩)⁻¹)

variable (l) in
/-- The weight `e_a` of `inl a` and `-e_a` of `inr a`, in coordinates. -/
def weightCoord : l ⊕ l → l → ℤ :=
  Sum.elim (fun a => Pi.single a 1) (fun a => Pi.single a (-1))

omit [Fintype l] in
@[simp] theorem weightCoord_inl (a : l) : weightCoord l (Sum.inl a) = Pi.single a 1 := rfl

omit [Fintype l] in
@[simp] theorem weightCoord_inr (a : l) : weightCoord l (Sum.inr a) = Pi.single a (-1) := rfl

theorem prod_zpow_single (τ : ULift.{u} l → Aˣ) (a : l) (m : ℤ) :
    ∏ c : ULift.{u} l, τ c ^ (Pi.single a m : l → ℤ) c.down = τ ⟨a⟩ ^ m := by
  rw [Finset.prod_eq_single (⟨a⟩ : ULift.{u} l) (fun c _ hc => ?_) (by simp)]
  · simp
  · rw [Pi.single_eq_of_ne (fun h => hc (ULift.ext _ _ h)), zpow_zero]

theorem torusWeights_eq_prod (τ : ULift.{u} l → Aˣ) (x : l ⊕ l) :
    torusWeights τ x = ∏ c : ULift.{u} l, τ c ^ weightCoord l x c.down := by
  cases x with
  | inl a => rw [weightCoord_inl, prod_zpow_single, zpow_one]; rfl
  | inr a => rw [weightCoord_inr, prod_zpow_single, zpow_neg_one]; rfl

theorem prod_zpow_weightCoord_sub (τ : ULift.{u} l → Aˣ) (x y : l ⊕ l) :
    ∏ c : ULift.{u} l, τ c ^ (weightCoord l x - weightCoord l y) c.down =
      torusWeights τ x * (torusWeights τ y)⁻¹ := by
  rw [torusWeights_eq_prod, torusWeights_eq_prod, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [Pi.sub_apply, zpow_sub]

theorem torusWeights_mulSingle (c : ULift.{u} l) (U : Aˣ) (x : l ⊕ l) :
    torusWeights (Pi.mulSingle c U) x = U ^ weightCoord l x c.down := by
  rw [torusWeights_eq_prod]
  exact GeneralLinear.prod_mulSingle_zpow (n := l) c U fun d => weightCoord l x d.down

omit [Fintype l] in
theorem weightCoord_injective : Function.Injective (weightCoord l) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl b =>
      have h1 := congrFun h a
      simp only [weightCoord_inl, Pi.single_eq_same] at h1
      by_contra hab
      rw [Pi.single_eq_of_ne (fun e => hab (congrArg Sum.inl e))] at h1
      exact one_ne_zero h1
    | inr b =>
      have h1 := congrFun h a
      simp only [weightCoord_inl, weightCoord_inr, Pi.single_eq_same, Pi.single_apply] at h1
      split_ifs at h1
      omega
  | inr a =>
    cases y with
    | inl b =>
      have h1 := congrFun h a
      simp only [weightCoord_inl, weightCoord_inr, Pi.single_eq_same, Pi.single_apply] at h1
      split_ifs at h1
    | inr b =>
      have h1 := congrFun h a
      simp only [weightCoord_inr, Pi.single_eq_same] at h1
      by_contra hab
      rw [Pi.single_eq_of_ne (fun e => hab (congrArg Sum.inr e))] at h1
      omega

end Weights

/-! ### The torus -/

section Torus

variable (l) (R : CommRingCat.{u})

/-- The diagonal torus `t ↦ diag(t, t⁻¹)` of `Sp_{2l}`: the diagonal torus of `GL_l` followed by
the Levi embedding. -/
def diagonalTorus :
    (splitTorus.commGroupScheme (Spec R) (ULift.{u} l)).toGrp ⟶ groupScheme l R :=
  GeneralLinear.diagonalTorus l R ≫ leviMap R

variable {l R}

omit [Fintype l] in
/-- The inverse of `diag(tᵢ)` is `diag(tᵢ⁻¹)`; the published `coe_inv_diagonalTorusUnits` carries an
unused base ring, so it is restated here. -/
theorem coe_inv_diagonalTorusUnits {n : Type} [Fintype n] [DecidableEq n] {A : Type*} [CommRing A]
    (τ : ULift.{u} n → Aˣ) :
    (((GeneralLinear.diagonalTorusUnits n A τ)⁻¹ : GL n A) : Matrix n n A) =
      Matrix.diagonal fun i => (((τ ⟨i⟩)⁻¹ : Aˣ) : A) :=
  rfl

/-- On affine points, the Levi embedding is the Levi block matrix. -/
theorem affinePointsEquiv_leviMap (S : CommAlgCat.{u} R)
    (f : (algSpec R).obj (op S) ⟶ (GeneralLinear.groupScheme l R).X) :
    affinePointsEquiv l R S (f ≫ (leviMap R).hom.hom) =
      leviHom S (GeneralLinear.affinePointsEquiv l R S f) :=
  Corepresented.groupSchemeMap_affinePoints _ _ _ f

theorem levi_diagonalTorusUnits {A : Type*} [CommRing A] (τ : ULift.{u} l → Aˣ) :
    levi (GeneralLinear.diagonalTorusUnits l A τ) =
      Matrix.diagonal fun x => (torusWeights τ x : A) := by
  rw [levi, GeneralLinear.coe_diagonalTorusUnits, coe_inv_diagonalTorusUnits,
    Matrix.diagonal_transpose, Matrix.fromBlocks_diagonal]
  congr 1
  funext x
  cases x <;> rfl

/-- An affine point of the diagonal torus, viewed in `GL_{l ⊕ l}`, is the diagonal matrix of its
weights. -/
theorem affinePointsEquiv_diagonalTorus_inclusion {A : Type u} [CommRing A] [Algebra R A]
    (t : Lie.AffinePoints (splitTorus.commGroupScheme (Spec R) (ULift.{u} l)).toGrp A) :
    GeneralLinear.affinePointsEquiv (l ⊕ l) R (CommAlgCat.of R A)
        (t ≫ (diagonalTorus l R ≫ inclusion l R).hom.hom) =
      GeneralLinear.diagonalTorusUnits (l ⊕ l) A
        (fun c : ULift.{u} (l ⊕ l) => torusWeights (GeneralLinear.torusCoords t) c.down) := by
  have h1 := affinePointsEquiv_inclusion (l := l) (R := R) (CommAlgCat.of R A)
    (t ≫ (diagonalTorus l R).hom.hom)
  have h2 := affinePointsEquiv_leviMap (l := l) (R := R) (CommAlgCat.of R A)
    (t ≫ (GeneralLinear.diagonalTorus l R).hom.hom)
  have h3 := GeneralLinear.affinePointsEquiv_comp_diagonalTorus (n := l) (R := R) (A := A) t
  have e1 : t ≫ (diagonalTorus l R ≫ inclusion l R).hom.hom =
      (t ≫ (diagonalTorus l R).hom.hom) ≫ (inclusion l R).hom.hom := by
    rw [Grp.comp_hom_hom, Category.assoc]
  have e2 : t ≫ (diagonalTorus l R).hom.hom =
      (t ≫ (GeneralLinear.diagonalTorus l R).hom.hom) ≫ (leviMap R).hom.hom := by
    rw [diagonalTorus, Grp.comp_hom_hom, Category.assoc]
  rw [e1, h1, e2, h2, h3]
  apply Units.ext
  change levi _ = _
  rw [levi_diagonalTorusUnits, GeneralLinear.coe_diagonalTorusUnits]

/-- On points, the diagonal torus sends `(tᵢ)` to `diag(t, t⁻¹)`. -/
theorem pointsEquiv_diagonalTorus {T : Over (Spec R)}
    (x : T ⟶ (splitTorus (Spec R) (ULift.{u} l)).X) :
    pointsEquiv l R T (x ≫ (diagonalTorus l R).hom.hom) =
      leviHom _ (GeneralLinear.diagonalTorusUnits l Γ(T.left, ⊤)
        (splitTorus.pointsEquiv (ULift.{u} l) T x)) := by
  rw [diagonalTorus, Grp.comp_hom_hom, ← Category.assoc, pointsEquiv_leviMap,
    GeneralLinear.pointsEquiv_diagonalTorus]

/-- The diagonal torus is injective on points. -/
instance mono_diagonalTorus_hom : Mono (diagonalTorus l R).hom.hom := by
  constructor
  intro Z g h hgh
  apply (splitTorus.pointsEquiv (ULift.{u} l) Z).injective
  have h1 := congrArg (pointsEquiv l R Z) hgh
  rw [pointsEquiv_diagonalTorus, pointsEquiv_diagonalTorus] at h1
  funext c
  apply Units.ext
  have h2 := congrArg (fun m : Matrix.symplecticGroup l Γ(Z.left, ⊤) =>
    (m : Matrix (l ⊕ l) (l ⊕ l) Γ(Z.left, ⊤)) (Sum.inl c.down) (Sum.inl c.down)) h1
  simpa only [coe_leviHom, levi_diagonalTorusUnits, Matrix.diagonal_apply_eq, torusWeights,
    Sum.elim_inl] using h2

end Torus

section Field

variable (l) (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- The published instance `isAffineHom_groupScheme`, restated for bases `CommRingCat.of k`, which
instance search does not find. -/
instance isAffineHom_groupScheme_of : IsAffineHom (groupScheme l (CommRingCat.of k)).X.hom :=
  isAffineHom_groupScheme (l := l) (R := CommRingCat.of k)

/-- The published instance `smooth_groupScheme`, restated for bases `CommRingCat.of k`. -/
instance smooth_groupScheme_of : Smooth (groupScheme l (CommRingCat.of k)).X.hom :=
  smooth_groupScheme l (CommRingCat.of k)

omit [DecidableEq l] in
instance isAffineHom_diagonalTorusSource : IsAffineHom (𝔻).X.hom :=
  isAffineHom_splitTorus _ _

omit [DecidableEq l] in
theorem isSplitTorus_diagonalTorus : IsSplitTorus (𝔻).toGrp :=
  isSplitTorus_splitTorus _

/-- The diagonal torus is a closed subgroup. -/
theorem isClosedSubgroup_diagonalTorus :
    IsClosedSubgroup (diagonalTorus l (CommRingCat.of k)) :=
  IsTorus.isClosedSubgroup_of_mono (IsSplitTorus.isTorus (isSplitTorus_diagonalTorus l k)) _

theorem isSplitSubtorus_diagonalTorus : IsSplitSubtorus (diagonalTorus l (CommRingCat.of k)) :=
  ⟨isSplitTorus_diagonalTorus l k, isClosedSubgroup_diagonalTorus l k⟩

variable {l k}

omit [DecidableEq l] in
/-- The value of a character on an affine point of the diagonal torus, in coordinates. -/
theorem characterValue_eq_prod (χ : characterLattice 𝔻) {A : Type u} [CommRing A] [Algebra k A]
    (t : Lie.AffinePoints (𝔻).toGrp A) :
    Lie.characterValue χ t =
      ∏ c : ULift.{u} l, GeneralLinear.torusCoords t c ^
        GeneralLinear.characterCoordEquiv l k χ c.down := by
  have h := GeneralLinear.characterValue_characterLatticeEquiv_symm
    (splitTorus.characterLatticeEquiv k (ULift.{u} l) χ) t
  rw [AddEquiv.symm_apply_apply] at h
  exact h

/-- Membership in a weight space of the diagonal torus, entrywise in the matrix coordinates. -/
theorem mem_weightSpace_diagonalTorus_iff
    (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k)) (χ : characterLattice 𝔻) :
    X ∈ weightSpace (diagonalTorus l (CommRingCat.of k)) χ ↔
      ∀ (A : Type u) [CommRing A] [Algebra k A] (t : Lie.AffinePoints (𝔻).toGrp A)
        (x y : l ⊕ l),
        (torusWeights (GeneralLinear.torusCoords t) x : A) * algebraMap k A (lieMatrix X x y) *
            (((torusWeights (GeneralLinear.torusCoords t) y)⁻¹ : Aˣ) : A) =
          (Lie.characterValue χ t : A) * algebraMap k A (lieMatrix X x y) := by
  rw [← lieKernelHomLinear_mem_weightSpace_iff (inclusion l (CommRingCat.of k)),
    ← pointKernelLinearEquiv_lieMatrix, mem_weightSpace]
  refine forall_congr' fun A => ?_
  refine ⟨fun h _ _ t a b => ?_, fun h _ _ t => ?_⟩
  · have h1 := h t
    rw [GeneralLinear.DualNumber.pointKernelLinearEquiv_naturality,
      GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, ← map_smul,
      EmbeddingLike.apply_eq_iff_eq, affinePointsEquiv_diagonalTorus_inclusion] at h1
    have h2 := congrFun (congrFun h1 a) b
    simpa only [GeneralLinear.coe_diagonalTorusUnits, coe_inv_diagonalTorusUnits,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Algebra.ofId_apply] using h2
  · rw [GeneralLinear.DualNumber.pointKernelLinearEquiv_naturality,
      GeneralLinear.DualNumber.adjoint_pointKernelLinearEquiv, ← map_smul,
      affinePointsEquiv_diagonalTorus_inclusion]
    congr 1
    ext a b
    simpa only [GeneralLinear.coe_diagonalTorusUnits, coe_inv_diagonalTorusUnits,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Algebra.ofId_apply] using h t a b

/-- **Weights of the diagonal torus.** An element of the Lie algebra of `Sp` lies in the weight
space of `χ` exactly when every nonzero entry of its matrix at `(x, y)` has weight
`χ = w(x) - w(y)`, where `w(inl a) = e_a` and `w(inr a) = -e_a`. -/
theorem mem_weightSpace_diagonalTorus_iff_support
    (X : Additive (lieKernel (groupScheme l (CommRingCat.of k)) k)) (χ : characterLattice 𝔻) :
    X ∈ weightSpace (diagonalTorus l (CommRingCat.of k)) χ ↔
      ∀ x y : l ⊕ l, lieMatrix X x y ≠ 0 →
        GeneralLinear.characterCoordEquiv l k χ = weightCoord l x - weightCoord l y := by
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
    have h1' : LaurentPolynomial.T (weightCoord l x c) * LaurentPolynomial.C (lieMatrix X x y) *
        LaurentPolynomial.T (-weightCoord l y c) =
        LaurentPolynomial.T (GeneralLinear.characterCoordEquiv l k χ c) *
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

end Langlands.GroupScheme.SymplecticMatrix
