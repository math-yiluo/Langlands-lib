import Langlands.GroupScheme.OrthogonalMatrix.LieAlgebra
import Langlands.GroupScheme.SymplecticMatrix.Torus

/-! # The diagonal torus of the split orthogonal group and its Lie weights

The diagonal torus `t ↦ diag(t, t⁻¹)` of the split orthogonal group is the diagonal torus of
`GL_l` followed by the Levi embedding. The pure matrix facts about the weights `torusWeights`
and `weightCoord` are those of the published symplectic model and are reused from there.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj LaurentPolynomial

namespace Langlands.GroupScheme.OrthogonalMatrix

open SymplecticMatrix (torusWeights weightCoord weightCoord_inl weightCoord_inr
  prod_zpow_weightCoord_sub torusWeights_mulSingle coe_inv_diagonalTorusUnits
  levi_diagonalTorusUnits)

variable {l : Type} [Fintype l] [DecidableEq l]

/-! ### The torus -/

section Torus

variable (l) (R : CommRingCat.{u})

/-- The diagonal torus `t ↦ diag(t, t⁻¹)` of `O_{2l}`: the diagonal torus of `GL_l` followed by
the Levi embedding. -/
def diagonalTorus :
    (splitTorus.commGroupScheme (Spec R) (ULift.{u} l)).toGrp ⟶ groupScheme l R :=
  GeneralLinear.diagonalTorus l R ≫ leviMap R

variable {l R}

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
  change SymplecticMatrix.levi _ = _
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
  have h2 := congrArg (fun m : orthogonalGroup l Γ(Z.left, ⊤) =>
    (m : Matrix (l ⊕ l) (l ⊕ l) Γ(Z.left, ⊤)) (Sum.inl c.down) (Sum.inl c.down)) h1
  simpa only [coe_leviHom, levi_diagonalTorusUnits, Matrix.diagonal_apply_eq, torusWeights,
    Sum.elim_inl] using h2

end Torus

section Field

variable (l) (k : Type u) [Field k]

local notation "𝔻" => splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)

/-- The diagonal torus is a closed subgroup. -/
theorem isClosedSubgroup_diagonalTorus :
    IsClosedSubgroup (diagonalTorus l (CommRingCat.of k)) :=
  IsTorus.isClosedSubgroup_of_mono
    (IsSplitTorus.isTorus (SymplecticMatrix.isSplitTorus_diagonalTorus l k)) _

theorem isSplitSubtorus_diagonalTorus : IsSplitSubtorus (diagonalTorus l (CommRingCat.of k)) :=
  ⟨SymplecticMatrix.isSplitTorus_diagonalTorus l k, isClosedSubgroup_diagonalTorus l k⟩

variable {l k}

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

/-- **Weights of the diagonal torus.** An element of the Lie algebra of `O_{2l}` lies in the
weight space of `χ` exactly when every nonzero entry of its matrix at `(x, y)` has weight
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
    rw [SymplecticMatrix.characterValue_eq_prod, GeneralLinear.torusCoords_affineTorusPoint,
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
    · have hχ := SymplecticMatrix.characterValue_eq_prod χ t
      rw [hsupp x y hxy, prod_zpow_weightCoord_sub] at hχ
      rw [hχ, Units.val_mul]
      ring

end Field

end Langlands.GroupScheme.OrthogonalMatrix
