import Langlands.GroupScheme.Reductive.UnipotentQuotient
import Langlands.GroupScheme.Multiplicative

/-! # Restriction of a representation to split invariant coordinates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The coordinate inclusion is invariant on every test scheme. The supplied
retraction gives the coordinates of the induced action. -/
def IsStableCoordinates (ρ : MatrixRepresentation G n)
    (B : Matrix n m R) (C : Matrix m n R) : Prop :=
  ∀ (T : Over (Spec R)) (x : T ⟶ G.X),
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T) =
      B.map (scalarMap T) *
        (C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
          B.map (scalarMap T))

variable (ρ : MatrixRepresentation G n) (B : Matrix n m R) (C : Matrix m n R)
  (hCB : C * B = 1) (hstable : ρ.IsStableCoordinates B C)

/-- The induced matrix homomorphism in the chosen split coordinates. -/
def coordinateMatrixHom (T : Over (Spec R)) :
    (T ⟶ G.X) →* Matrix m m Γ(T.left, ⊤) where
  toFun x := C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
    B.map (scalarMap T)
  map_one' := by
    rw [map_one, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one, ← Matrix.map_mul,
      hCB, Matrix.map_one _ (map_zero _) (map_one _)]
  map_mul' x y := by
    rw [map_mul, Matrix.GeneralLinearGroup.coe_mul]
    calc
      _ = C.map (scalarMap T) *
          ((ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
            ((ρ.pointMatrix T y : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T))) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hstable T y]; simp only [Matrix.mul_assoc]

/-- The induced invertible matrix is natural in the relative test scheme. -/
theorem coordinateMatrixHom_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    (coordinateMatrixHom ρ B C hCB hstable T' (a ≫ x)) =
      (coordinateMatrixHom ρ B C hCB hstable T x).map a.left.appTop.hom := by
  change C.map (scalarMap T') * (ρ.pointMatrix T' (a ≫ x) : Matrix n n Γ(T'.left, ⊤)) *
    B.map (scalarMap T') =
      (C.map (scalarMap T) * (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) *
        B.map (scalarMap T)).map a.left.appTop.hom
  rw [pointMatrix_naturality, Matrix.map_mul, Matrix.map_mul]
  change C.map (scalarMap T') *
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)).map a.left.appTop.hom *
      B.map (scalarMap T') = _
  have hB : B.map (scalarMap T') =
      (B.map (scalarMap T)).map a.left.appTop.hom := by
    ext i j
    exact (scalarMap_naturality a _).symm
  have hC : C.map (scalarMap T') =
      (C.map (scalarMap T)).map a.left.appTop.hom := by
    ext i j
    exact (scalarMap_naturality a _).symm
  rw [hB, hC]

/-- Pointwise restriction in the chosen invariant coordinates. -/
def coordinatePoints (T : Over (Spec R)) :
    (T ⟶ G.X) →* (T ⟶ (GeneralLinear.groupScheme m R).X) :=
  (GeneralLinear.pointsEquiv m R T).symm.toMonoidHom.comp
    (coordinateMatrixHom ρ B C hCB hstable T).toHomUnits

/-- The restricted points commute with every relative test map. -/
theorem coordinatePoints_naturality {T T' : Over (Spec R)} (a : T' ⟶ T)
    (x : T ⟶ G.X) :
    coordinatePoints ρ B C hCB hstable T' (a ≫ x) =
      a ≫ coordinatePoints ρ B C hCB hstable T x := by
  apply (GeneralLinear.pointsEquiv m R T').injective
  rw [GeneralLinear.pointsEquiv_naturality]
  simp only [coordinatePoints, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  change (coordinateMatrixHom ρ B C hCB hstable T').toHomUnits (a ≫ x) =
    Matrix.GeneralLinearGroup.map a.left.appTop.hom
      ((coordinateMatrixHom ρ B C hCB hstable T).toHomUnits x)
  apply Units.ext
  exact coordinateMatrixHom_naturality ρ B C hCB hstable a x

/-- An actual group-scheme representation on the split invariant coordinates. -/
def restrictCoordinates : MatrixRepresentation G m :=
  homOfPoints (coordinatePoints ρ B C hCB hstable)
    (coordinatePoints_naturality ρ B C hCB hstable)

/-- The restricted representation has the stated coordinate matrix on all tests. -/
theorem restrictCoordinates_pointMatrix (T : Over (Spec R)) (x : T ⟶ G.X) :
    (restrictCoordinates ρ B C hCB hstable).pointMatrix T x =
      (coordinateMatrixHom ρ B C hCB hstable T).toHomUnits x := by
  rw [pointMatrix_apply, restrictCoordinates, comp_homOfPoints]
  exact (GeneralLinear.pointsEquiv m R T).apply_symm_apply _

/-- The coordinate inclusion intertwines the actual restricted and ambient actions. -/
theorem restrictCoordinates_intertwines (T : Over (Spec R)) (x : T ⟶ G.X) :
    (ρ.pointMatrix T x : Matrix n n Γ(T.left, ⊤)) * B.map (scalarMap T) =
      B.map (scalarMap T) *
        ((restrictCoordinates ρ B C hCB hstable).pointMatrix T x : Matrix m m Γ(T.left, ⊤)) := by
  rw [restrictCoordinates_pointMatrix]
  exact hstable T x

/-- A fixed vector for the restriction gives an actual fixed vector in the ambient coordinates. -/
theorem isFixedVector_mulVec_restrictCoordinates {v : m → R}
    (hv : (restrictCoordinates ρ B C hCB hstable).IsFixedVector v) :
    ρ.IsFixedVector (B *ᵥ v) := by
  intro T x
  have hvec : (fun i => scalarMap T ((B *ᵥ v) i)) =
      B.map (scalarMap T) *ᵥ (fun i => scalarMap T (v i)) := by
    funext i
    exact (scalarMap T).map_mulVec B v i
  rw [hvec, Matrix.mulVec_mulVec, restrictCoordinates_intertwines ρ B C hCB hstable,
    ← Matrix.mulVec_mulVec, hv T x]

include hCB in
omit [DecidableEq n] in
/-- The inclusion is injective because it has the supplied left inverse. -/
theorem coordinateInclusion_injective : Function.Injective (B.mulVec) := by
  intro v w h
  have h' := congrArg (C.mulVec) h
  simpa only [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] using h'

end Langlands.GroupScheme.MatrixRepresentation
