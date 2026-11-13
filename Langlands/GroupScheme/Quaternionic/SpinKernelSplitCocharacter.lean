import Langlands.GroupScheme.Quaternionic.SpinKernelSplitReduction
import Langlands.GroupScheme.Quaternionic.SplittingChart
import Langlands.GroupScheme.Quaternionic.SymplecticReductive
import Langlands.Algebra.ReducedNormFiniteChart

/-! # A split cocharacter in the original quaternionic spin cover -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic.SpinKernel

open FirstKindInvolution Langlands.CentralSimple

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
  {L : Type u} [Field L] [Algebra K L]
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin 2) (Fin 2) L)

section Coefficients

variable (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
  [IsScalarTower K L R]

/-- The inverse chart of the determinant-one diagonal matrix. -/
def splitDiagonalUnits : Rˣ →* (R ⊗[K] D)ˣ :=
  (Units.map (chartR e R).symm.toMonoidHom).comp
    (Matrix.SpecialLinearGroup.toGL.comp BinaryAction.diagonalSL)

omit [FiniteDimensional K D] [Algebra.IsCentral K D] in
@[simp] theorem chartR_splitDiagonalUnits (t : Rˣ) :
    chartR e R (splitDiagonalUnits e R t : R ⊗[K] D) =
      !![(t : R), 0; 0, (t⁻¹ : Rˣ)] := by
  change chartR e R ((chartR e R).symm (BinaryAction.diagonalSL t : Matrix _ _ R)) = _
  rw [RingEquiv.apply_symm_apply, BinaryAction.diagonalSL_val]

/-- The diagonal has canonical reduced norm one over every coefficient algebra. -/
def splitNormOneDiagonal : Rˣ →* reducedNormOne K D R :=
  (splitDiagonalUnits e R).codRestrict (reducedNormOne K D R) (fun t => by
    rw [mem_reducedNormOne, reducedNorm_eq_det_fintype K D e R]
    change (chartR e R (splitDiagonalUnits e R t : R ⊗[K] D)).det = 1
    rw [chartR_splitDiagonalUnits]
    simp [Matrix.det_fin_two])

@[simp] theorem splitNormOneDiagonal_val (t : Rˣ) :
    (splitNormOneDiagonal e R t).val = splitDiagonalUnits e R t := rfl

@[simp] theorem chartR_splitNormOneDiagonal (t : Rˣ) :
    chartR e R ((splitNormOneDiagonal e R t).val : R ⊗[K] D) =
      !![(t : R), 0; 0, (t⁻¹ : Rˣ)] :=
  chartR_splitDiagonalUnits e R t

/-- At square roots of one the split diagonal is the original scalar unit. -/
theorem splitNormOneDiagonal_root (t : Rˣ) (ht : t * t = 1) :
    (splitNormOneDiagonal e R t).val = normCoverScalarUnits K D R t := by
  apply Units.ext
  apply (chartR e R).injective
  rw [chartR_splitNormOneDiagonal, normCoverScalarUnits_val, chartR_tmul]
  have he1 : e ((1 : L) ⊗ₜ[K] (1 : D)) = 1 := e.map_one
  rw [he1]
  have hi : t⁻¹ = t := inv_eq_of_mul_eq_one_left ht
  rw [hi]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {R}

/-- The split norm-one diagonal respects arbitrary maps of coefficient algebras. -/
theorem splitNormOneDiagonal_naturality
    {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra L R']
    [IsScalarTower K L R'] (f : R →ₐ[L] R') (t : Rˣ) :
    Units.map (Algebra.TensorProduct.map (f.restrictScalars K) (AlgHom.id K D)).toMonoidHom
        (splitNormOneDiagonal e R t).val =
      (splitNormOneDiagonal e R'
        (Units.map f.toRingHom.toMonoidHom t)).val := by
  apply Units.ext
  apply (chartR e R').injective
  change chartR e R'
    (Algebra.TensorProduct.map (f.restrictScalars K) (AlgHom.id K D)
      ((splitNormOneDiagonal e R t).val : R ⊗[K] D)) = _
  rw [chartR_naturality, chartR_splitNormOneDiagonal, chartR_splitNormOneDiagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Multiplying by the scalar unit gives the diagonal with entries `t²,1`. -/
theorem chartR_scalar_mul_splitNormOneDiagonal (t : Rˣ) :
    chartR e R
      ((normCoverScalarUnits K D R t * (splitNormOneDiagonal e R t).val : (R ⊗[K] D)ˣ) :
        R ⊗[K] D) = !![(t : R) ^ 2, 0; 0, 1] := by
  rw [Units.val_mul, _root_.map_mul, chartR_splitNormOneDiagonal,
    normCoverScalarUnits_val, chartR_tmul]
  have he1 : e ((1 : L) ⊗ₜ[K] (1 : D)) = 1 := e.map_one
  rw [he1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, pow_two]

end Coefficients

section BinaryCocharacter

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

/-- Split diagonal points of the original binary product, viewed over `K`. -/
def splitBinaryPoints (U : Over (Spec (CommRingCat.of L))) :
    (U ⟶ (Gm (Spec (CommRingCat.of L))).X) →*
      ((Over.map (scalarBaseMap K L)).obj U ⟶
        (BinaryScheme.groupScheme (K := K) (D := D)).X) :=
  (BinaryScheme.pointsEquiv _).symm.toMonoidHom.comp
    ((BinaryAction.diagonalSL.prod (splitNormOneDiagonal e (restrictedSections K L U))).comp
      (Gm.pointsEquiv (Spec (CommRingCat.of L)) U).toMonoidHom)

@[simp] theorem splitBinaryPoints_coordinates (U : Over (Spec (CommRingCat.of L)))
    (z : U ⟶ (Gm (Spec (CommRingCat.of L))).X) :
    BinaryScheme.pointsEquiv _ (splitBinaryPoints e U z) =
      (BinaryAction.diagonalSL (Gm.pointsEquiv _ U z),
        splitNormOneDiagonal e (restrictedSections K L U) (Gm.pointsEquiv _ U z)) :=
  (BinaryScheme.pointsEquiv _).apply_symm_apply _

/-- The split binary points respect all relative test restrictions. -/
theorem splitBinaryPoints_naturality {U U' : Over (Spec (CommRingCat.of L))}
    (j : U' ⟶ U) (z : U ⟶ (Gm (Spec (CommRingCat.of L))).X) :
    splitBinaryPoints e U' (j ≫ z) =
      (Over.map (scalarBaseMap K L)).map j ≫ splitBinaryPoints e U z := by
  apply (BinaryScheme.pointsEquiv _).injective
  rw [splitBinaryPoints_coordinates]
  apply Prod.ext
  · change BinaryAction.diagonalSL (Gm.pointsEquiv _ U' (j ≫ z)) =
      SpecialLinear.pointsEquiv (Fin 2) (CommRingCat.of K) _
        (((Over.map (scalarBaseMap K L)).map j ≫ splitBinaryPoints e U z) ≫ fst _ _)
    rw [Category.assoc, SpecialLinear.pointsEquiv_naturality]
    change BinaryAction.diagonalSL (Gm.pointsEquiv _ U' (j ≫ z)) =
      Matrix.SpecialLinearGroup.map j.left.appTop.hom
        (BinaryScheme.pointsEquiv _ (splitBinaryPoints e U z)).1
    rw [splitBinaryPoints_coordinates, Gm.pointsEquiv_naturality]
    apply Matrix.SpecialLinearGroup.ext
    intro i k
    fin_cases i <;> fin_cases k <;> simp [Matrix.SpecialLinearGroup.map]
  · change splitNormOneDiagonal e (restrictedSections K L U')
        (Gm.pointsEquiv _ U' (j ≫ z)) =
      CentralSimpleUnits.normOnePointsEquiv K D _
        (((Over.map (scalarBaseMap K L)).map j ≫ splitBinaryPoints e U z) ≫ snd _ _)
    rw [Category.assoc, CentralSimpleUnits.normOnePointsEquiv_naturality]
    change splitNormOneDiagonal e (restrictedSections K L U')
        (Gm.pointsEquiv _ U' (j ≫ z)) =
      CentralSimpleUnits.normOneUnitsRestrict K D _
        (BinaryScheme.pointsEquiv _ (splitBinaryPoints e U z)).2
    rw [splitBinaryPoints_coordinates, Gm.pointsEquiv_naturality]
    apply Subtype.ext
    let f : restrictedSections K L U →ₐ[L] restrictedSections K L U' :=
      { ((algΓ (CommRingCat.of K)).map
          ((Over.map (scalarBaseMap K L)).map j)).unop.hom.toRingHom with
        commutes' := fun c => ((algΓ (CommRingCat.of L)).map j).unop.hom.commutes c }
    exact (splitNormOneDiagonal_naturality e f (Gm.pointsEquiv _ U z)).symm

/-- The same binary points as points of the base-changed original product. -/
def splitBinaryBaseChangePoints (U : Over (Spec (CommRingCat.of L))) :
    (U ⟶ (Gm (Spec (CommRingCat.of L))).X) →*
      (U ⟶ ((GroupScheme.baseChange (scalarBaseMap K L)).obj
        (BinaryScheme.groupScheme (K := K) (D := D))).X) :=
  (baseChangePointsEquiv (scalarBaseMap K L) _ U).symm.toMonoidHom.comp
    (splitBinaryPoints e U)

theorem splitBinaryBaseChangePoints_naturality
    {U U' : Over (Spec (CommRingCat.of L))}
    (j : U' ⟶ U) (z : U ⟶ (Gm (Spec (CommRingCat.of L))).X) :
    splitBinaryBaseChangePoints e U' (j ≫ z) =
      j ≫ splitBinaryBaseChangePoints e U z := by
  apply (baseChangePointsEquiv (scalarBaseMap K L) _ U').injective
  rw [baseChangePointsEquiv_naturality]
  simp only [splitBinaryBaseChangePoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, splitBinaryPoints_naturality]

/-- The binary cocharacter is obtained from its natural family on every test scheme. -/
def splitBinaryCocharacter :
    (Gm (Spec (CommRingCat.of L))).toGrp ⟶
      (GroupScheme.baseChange (scalarBaseMap K L)).obj
        (BinaryScheme.groupScheme (K := K) (D := D)) :=
  homOfPoints (splitBinaryBaseChangePoints e) (splitBinaryBaseChangePoints_naturality e)

@[simp] theorem splitBinaryCocharacter_points (U : Over (Spec (CommRingCat.of L)))
    (z : U ⟶ (Gm (Spec (CommRingCat.of L))).X) :
    baseChangePointsEquiv (scalarBaseMap K L) _ U
        (z ≫ (splitBinaryCocharacter e).hom.hom) =
      splitBinaryPoints e U z := by
  rw [splitBinaryCocharacter,
    comp_homOfPoints _ (splitBinaryBaseChangePoints_naturality e)]
  exact (baseChangePointsEquiv _ _ _).apply_symm_apply _

/-- On square roots of one the split binary point is the original binary diagonal. -/
theorem splitBinaryPoints_root (hdim : Module.finrank K D = 4)
    (U : Over (Spec (CommRingCat.of L)))
    (z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1}) :
    splitBinaryPoints e U z.val =
      binaryRootPointsEquiv (scalarBaseMap K L) U z ≫
        (BinaryKernel.diagonal hdim).hom.hom := by
  apply (BinaryScheme.pointsEquiv _).injective
  rw [splitBinaryPoints_coordinates]
  change _ = BinaryScheme.pointsEquiv _
    (((BinaryKernel.rootsPointsEquiv _).symm
      (squareRootCoordinates (scalarBaseMap K L) U z)) ≫
        (BinaryKernel.diagonal hdim).hom.hom)
  rw [BinaryKernel.diagonal_root_coordinates]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    rw [BinaryKernel.rootScalarNormOne_val]
    apply splitNormOneDiagonal_root
    simpa only [_root_.map_mul, _root_.map_one] using
      congrArg (Gm.pointsEquiv (Spec (CommRingCat.of L)) U) z.2

end BinaryCocharacter

section SpinCocharacter

attribute [local instance] restrictedSectionsAlgebra restrictedSectionsScalarTower

variable [Infinite K] (σ : FirstKindInvolution K D)
  (hdim : Module.finrank K D = 4) (hsym : Module.finrank K σ.symmetricSubspace = 3)
  {n : Type} [Fintype n] [DecidableEq n]
  {q : σ.QuadraticForms n} {v w : n → D} (h : σ.IsHyperbolicPair q v w)
  {S : GroupScheme (Spec (CommRingCat.of K))}
  {π : S ⟶ σ.isometryGroup q}
  (hπ : σ.IsSpinCover q π)
  (hsc : CentralSimpleUnits.DegreeTwoNormOneSimplyConnectedStatement.{u})

/-- The split cocharacter in the supplied spin group, through the original binary lift. -/
def splitSpinCocharacter :
    (Gm (Spec (CommRingCat.of L))).toGrp ⟶
      (GroupScheme.baseChange (scalarBaseMap K L)).obj S :=
  splitBinaryCocharacter e ≫
    (GroupScheme.baseChange (scalarBaseMap K L)).map
      (BinarySpinLift.productHom σ hdim hsym h hπ hsc)

/-- The spin cocharacter is the combined binary lift on all relative test schemes. -/
theorem splitSpinCocharacter_points (U : Over (Spec (CommRingCat.of L)))
    (z : U ⟶ (Gm (Spec (CommRingCat.of L))).X) :
    baseChangePointsEquiv (scalarBaseMap K L) S U
        (z ≫ (splitSpinCocharacter e σ hdim hsym h hπ hsc).hom.hom) =
      splitBinaryPoints e U z ≫
        (BinarySpinLift.productHom σ hdim hsym h hπ hsc).hom.hom := by
  rw [splitSpinCocharacter, Grp.comp_hom_hom, ← Category.assoc,
    baseChangePointsEquiv_comp, splitBinaryCocharacter_points]

/-- Square roots of one recover the original diagonal spin morphism on every test. -/
theorem splitSpinCocharacter_root (U : Over (Spec (CommRingCat.of L)))
    (z : {z : U ⟶ (Gm (Spec (CommRingCat.of L))).X // z * z = 1}) :
    baseChangePointsEquiv (scalarBaseMap K L) S U
        (z.val ≫ (splitSpinCocharacter e σ hdim hsym h hπ hsc).hom.hom) =
      binaryRootPointsEquiv (scalarBaseMap K L) U z ≫
        (BinarySpinLift.diagonalSpin σ hdim hsym h hπ hsc).hom.hom := by
  rw [splitSpinCocharacter_points, splitBinaryPoints_root, BinarySpinLift.diagonalSpin,
    Grp.comp_hom_hom, Category.assoc]

/-- The projected cocharacter has the original ambient hyperbolic Levi action. -/
theorem splitSpinCocharacter_ambient_points (U : Over (Spec (CommRingCat.of L)))
    (z : U ⟶ (Gm (Spec (CommRingCat.of L))).X) :
    HyperbolicScheme.matrixPointsEquiv n ((Over.map (scalarBaseMap K L)).obj U)
      (baseChangePointsEquiv (scalarBaseMap K L) (σ.isometryGroup q) U
          ((z ≫ (splitSpinCocharacter e σ hdim hsym h hπ hsc).hom.hom) ≫
            ((GroupScheme.baseChange (scalarBaseMap K L)).map π).hom.hom) ≫
        (σ.isometryGroupι q).hom.hom) =
      HyperbolicScheme.extendUnits h (restrictedSections K L U)
        (BinaryAction.hyperbolicLevi (σ.baseChange (restrictedSections K L U))
          (normCoverScalarUnits K D (restrictedSections K L U) (Gm.pointsEquiv _ U z) *
            (splitNormOneDiagonal e (restrictedSections K L U)
              (Gm.pointsEquiv _ U z)).val)) := by
  rw [baseChangePointsEquiv_comp, splitSpinCocharacter_points,
    BinarySpinLift.productHom_ambient_points]
  change HyperbolicScheme.extendUnits h (restrictedSections K L U)
    (BinaryAction.normOneAction σ hdim hsym (restrictedSections K L U)
      (BinaryScheme.pointsEquiv _ (splitBinaryPoints e U z))) = _
  rw [splitBinaryPoints_coordinates]
  exact congrArg (HyperbolicScheme.extendUnits h (restrictedSections K L U))
    (BinarySpinLift.diagonal_normOne_action σ hdim hsym (restrictedSections K L U)
      (Gm.pointsEquiv _ U z)
      (splitNormOneDiagonal e (restrictedSections K L U) (Gm.pointsEquiv _ U z)))

end SpinCocharacter

end Langlands.GroupScheme.Quaternionic.SpinKernel
