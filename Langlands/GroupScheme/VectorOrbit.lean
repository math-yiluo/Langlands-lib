import Langlands.GroupScheme.MatrixRepresentation
import Langlands.GroupScheme.VectorGroupQuotient
import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.SchemeActionOfPointLaws

/-! # Actual affine vector actions and coordinate-vector orbit maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.GroupScheme.VectorOrbit

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} {n : ℕ}
    (ρ : MatrixRepresentation G (Fin n))

/-- The action of a matrix representation on the actual vector group, on any test. -/
def pointAction (T : Over (Spec R)) (g : T ⟶ G.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    T ⟶ (VectorGroup.groupScheme R n).X :=
  (VectorGroup.coordinates R n T).symm (Multiplicative.ofAdd
    ((ρ.pointMatrix T g : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) *ᵥ
      (VectorGroup.coordinates R n T v).toAdd))

theorem coordinates_pointAction (T : Over (Spec R)) (g : T ⟶ G.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    (VectorGroup.coordinates R n T (pointAction ρ T g v)).toAdd =
      (ρ.pointMatrix T g : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) *ᵥ
        (VectorGroup.coordinates R n T v).toAdd := by
  rw [pointAction, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem pointAction_naturality {T W : Over (Spec R)} (f : W ⟶ T)
    (g : T ⟶ G.X) (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    f ≫ pointAction ρ T g v = pointAction ρ W (f ≫ g) (f ≫ v) := by
  apply VectorGroup.points_ext
  intro i
  rw [VectorGroup.coordinates_comp, coordinates_pointAction,
    coordinates_pointAction, VectorGroup.coordinates_comp,
    MatrixRepresentation.pointMatrix_naturality]
  exact f.left.appTop.hom.map_mulVec _ _ i

theorem pointAction_one (T : Over (Spec R))
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    pointAction ρ T 1 v = v := by
  apply VectorGroup.points_ext
  intro i
  rw [coordinates_pointAction, map_one, Matrix.GeneralLinearGroup.coe_one,
    Matrix.one_mulVec]

theorem pointAction_mul (T : Over (Spec R)) (g h : T ⟶ G.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    pointAction ρ T (g * h) v = pointAction ρ T g (pointAction ρ T h v) := by
  apply VectorGroup.points_ext
  intro i
  rw [coordinates_pointAction, coordinates_pointAction, coordinates_pointAction,
    map_mul, Matrix.GeneralLinearGroup.coe_mul, Matrix.mulVec_mulVec]

theorem pointAction_mul_right (T : Over (Spec R)) (g : T ⟶ G.X)
    (v w : T ⟶ (VectorGroup.groupScheme R n).X) :
    pointAction ρ T g (v * w) = pointAction ρ T g v * pointAction ρ T g w := by
  apply VectorGroup.points_ext
  intro i
  rw [coordinates_pointAction, VectorGroup.coordinates_mul,
    VectorGroup.coordinates_mul, coordinates_pointAction, coordinates_pointAction,
    Matrix.mulVec_add]

/-- An actual automorphic action realizing the coefficient matrices on all tests. -/
def automorphicAction : AutomorphicAction G (VectorGroup.groupScheme R n) :=
  AutomorphicAction.ofPoints (pointAction ρ) (pointAction_naturality ρ)
    (pointAction_one ρ) (pointAction_mul ρ) (pointAction_mul_right ρ)

theorem automorphicAction_act {T : Over (Spec R)} (g : T ⟶ G.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    (automorphicAction ρ).act g v = pointAction ρ T g v :=
  AutomorphicAction.ofPoints_act _ (pointAction_naturality ρ)
    (pointAction_one ρ) (pointAction_mul ρ) (pointAction_mul_right ρ) g v

/-- The same action as the standard categorical scheme-action structure. -/
@[instance_reducible]
def schemeAction : SchemeAction G (VectorGroup.groupScheme R n).X :=
  schemeActionOfPointLaws (automorphicAction ρ).hom
    (automorphicAction ρ).one_left (automorphicAction ρ).mul_left

theorem schemeAction_act {T : Over (Spec R)} (g : T ⟶ G.X)
    (v : T ⟶ (VectorGroup.groupScheme R n).X) :
    (schemeAction ρ).act g v = pointAction ρ T g v :=
  automorphicAction_act ρ g v

variable (R n)

/-- The constant coordinate vector `e_j` as an actual point on every scheme test. -/
def coordinatePoint (j : Fin n) (T : Over (Spec R)) :
    T ⟶ (VectorGroup.groupScheme R n).X :=
  (VectorGroup.coordinates R n T).symm
    (Multiplicative.ofAdd (Pi.single j (1 : Γ(T.left, ⊤))))

theorem coordinates_coordinatePoint (j : Fin n) (T : Over (Spec R)) :
    (VectorGroup.coordinates R n T (coordinatePoint R n j T)).toAdd =
      Pi.single j 1 := by
  rw [coordinatePoint, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem coordinatePoint_naturality (j : Fin n) {T W : Over (Spec R)} (f : W ⟶ T) :
    f ≫ coordinatePoint R n j T = coordinatePoint R n j W := by
  apply VectorGroup.points_ext
  intro i
  rw [VectorGroup.coordinates_comp, coordinates_coordinatePoint, coordinates_coordinatePoint]
  by_cases h : i = j
  · subst i
    simp
  · simp [Pi.single_eq_of_ne h]

variable {R n}

/-- The actual affine orbit map of a coordinate vector. -/
def orbitMap (j : Fin n) : G.X ⟶ (VectorGroup.groupScheme R n).X :=
  (schemeAction ρ).act (𝟙 G.X)
    (toUnit G.X ≫ coordinatePoint R n j (𝟙_ (Over (Spec R))))

/-- The orbit map is exactly matrix multiplication by the coordinate vector on every test. -/
theorem coordinates_comp_orbitMap (j : Fin n) (T : Over (Spec R)) (g : T ⟶ G.X) :
    (VectorGroup.coordinates R n T (g ≫ orbitMap ρ j)).toAdd =
      (ρ.pointMatrix T g : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) *ᵥ Pi.single j 1 := by
  rw [orbitMap, SchemeAction.naturality, Category.comp_id, schemeAction_act,
    coordinates_pointAction, ← Category.assoc, coordinatePoint_naturality,
    coordinates_coordinatePoint]

/-- Equality of vector translates is fixedness under the right difference. -/
theorem translates_eq_iff {A : Type u} [CommRing A] (M N : GL (Fin n) A)
    (v : Fin n → A) :
    (M : Matrix (Fin n) (Fin n) A) *ᵥ v =
        (N : Matrix (Fin n) (Fin n) A) *ᵥ v ↔
      ((M⁻¹ * N : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) *ᵥ v = v := by
  constructor
  · intro h
    have e := congrArg (fun w => (M⁻¹ : GL (Fin n) A).val *ᵥ w) h
    simpa only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec] using e.symm
  · intro h
    have e := congrArg (fun w => M.val *ᵥ w) h
    simpa only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul,
      mul_inv_cancel_left] using e.symm

/-- The fibers on all scheme tests are the coordinate-vector stabilizer tests. -/
theorem orbitMap_fibers (j : Fin n) (T : Over (Spec R)) (g h : T ⟶ G.X) :
    g ≫ orbitMap ρ j = h ≫ orbitMap ρ j ↔
      (ρ.pointMatrix T (g⁻¹ * h) : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) *ᵥ
        Pi.single j 1 = Pi.single j 1 := by
  have heq : g ≫ orbitMap ρ j = h ≫ orbitMap ρ j ↔
      (ρ.pointMatrix T g : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) *ᵥ Pi.single j 1 =
        (ρ.pointMatrix T h : Matrix (Fin n) (Fin n) Γ(T.left, ⊤)) *ᵥ Pi.single j 1 := by
    constructor
    · intro e
      simpa only [coordinates_comp_orbitMap] using
        congrArg (fun w => (VectorGroup.coordinates R n T w).toAdd) e
    · intro e
      exact VectorGroup.points_ext (by simpa only [coordinates_comp_orbitMap] using congrFun e)
  rw [heq, translates_eq_iff, map_mul, map_inv]

end Langlands.GroupScheme.VectorOrbit
