import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.SchemeActionOfPointLaws
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # The actual affine-space action of a matrix representation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable (n : Type) (R : CommRingCat.{u})

/-- Affine coordinate space of a finite coefficient representation. -/
def coefficientSpace : Over (Spec R) :=
  Over.mk (AffineSpace (ULift.{u} n) (Spec R) ↘ Spec R)

instance instSchemeAction1 : IsAffine (coefficientSpace n R).left := by
  dsimp [coefficientSpace]
  infer_instance

variable {n R}

/-- The vector of coordinates of an actual affine-space point. -/
def coefficientCoordinates {T : Over (Spec R)} (x : T ⟶ coefficientSpace n R) :
    n → Γ(T.left, ⊤) :=
  fun i => x.left.appTop (AffineSpace.coord (Spec R) (ULift.up i))

/-- The actual affine-space point with a specified vector of global coordinates. -/
def coefficientPoint (T : Over (Spec R)) (v : n → Γ(T.left, ⊤)) :
    T ⟶ coefficientSpace n R :=
  Over.homMk (AffineSpace.homOfVector T.hom (fun i : ULift.{u} n => v i.down))
    (AffineSpace.homOfVector_over _ _)

@[simp] theorem coefficientCoordinates_coefficientPoint
    (T : Over (Spec R)) (v : n → Γ(T.left, ⊤)) :
    coefficientCoordinates (coefficientPoint T v) = v := by
  funext i
  exact AffineSpace.homOfVector_appTop_coord _ _ (ULift.up i)

/-- Coordinates detect equality on every scheme test. -/
theorem coefficientCoordinates_injective (T : Over (Spec R)) :
    Function.Injective (coefficientCoordinates (T := T) (n := n)) := by
  intro x y h
  apply Over.OverMorphism.ext
  apply AffineSpace.hom_ext
  · exact (Over.w x).trans (Over.w y).symm
  · intro i
    exact congrFun h i.down

@[simp] theorem coefficientPoint_coefficientCoordinates
    {T : Over (Spec R)} (x : T ⟶ coefficientSpace n R) :
    coefficientPoint T (coefficientCoordinates x) = x := by
  apply coefficientCoordinates_injective
  exact coefficientCoordinates_coefficientPoint _ _

/-- Points of the actual affine space are precisely coordinate vectors. -/
def coefficientPointEquiv (T : Over (Spec R)) :
    (T ⟶ coefficientSpace n R) ≃ (n → Γ(T.left, ⊤)) where
  toFun := coefficientCoordinates
  invFun := coefficientPoint T
  left_inv := coefficientPoint_coefficientCoordinates
  right_inv := coefficientCoordinates_coefficientPoint T

/-- Pullback of points pulls back every coordinate by the actual map on sections. -/
theorem coefficientCoordinates_comp {T T' : Over (Spec R)} (b : T' ⟶ T)
    (x : T ⟶ coefficientSpace n R) :
    coefficientCoordinates (b ≫ x) = fun i => b.left.appTop (coefficientCoordinates x i) := rfl

/-- The structure-ring maps commute with actual scheme pullback. -/
theorem scalarMap_comp {T T' : Over (Spec R)} (b : T' ⟶ T) (r : R) :
    b.left.appTop (scalarMap T r) = scalarMap T' r := by
  change (((Scheme.ΓSpecIso R).inv ≫ T.hom.appTop) ≫ b.left.appTop) r = _
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, Over.w b]
  rfl

/-- A base vector determines its constant rational point in affine space. -/
def constantCoefficientPoint (v : n → R) :
    Over.mk (𝟙 (Spec R)) ⟶ coefficientSpace n R :=
  coefficientPoint _ (fun i => scalarMap _ (v i))

/-- Constant vectors pull back to the scalar image of their coordinates. -/
theorem coefficientCoordinates_constant {T : Over (Spec R)}
    (b : T ⟶ Over.mk (𝟙 (Spec R))) (v : n → R) :
    coefficientCoordinates (b ≫ constantCoefficientPoint v) =
      fun i => scalarMap T (v i) := by
  rw [coefficientCoordinates_comp]
  simp only [constantCoefficientPoint, coefficientCoordinates_coefficientPoint,
    scalarMap_comp]

variable [Fintype n] [DecidableEq n] {G : GroupScheme (Spec R)}

/-- The universal matrix-vector product defines an actual scheme morphism. -/
def coefficientActionHom (ρ : MatrixRepresentation G n) :
    G.X ⊗ coefficientSpace n R ⟶ coefficientSpace n R :=
  coefficientPoint (G.X ⊗ coefficientSpace n R)
    ((ρ.pointMatrix _ (fst G.X (coefficientSpace n R)) :
        Matrix n n Γ((G.X ⊗ coefficientSpace n R).left, ⊤)) *ᵥ
      coefficientCoordinates (snd G.X (coefficientSpace n R)))

/-- On every scheme test the action morphism is the original matrix action. -/
theorem coefficientCoordinates_actionHom (ρ : MatrixRepresentation G n)
    {T : Over (Spec R)} (g : T ⟶ G.X) (x : T ⟶ coefficientSpace n R) :
    coefficientCoordinates (lift g x ≫ ρ.coefficientActionHom) =
      (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ coefficientCoordinates x := by
  rw [coefficientCoordinates_comp]
  simp only [coefficientActionHom, coefficientCoordinates_coefficientPoint]
  have hg := ρ.pointMatrix_naturality (lift g x) (fst G.X (coefficientSpace n R))
  simp only [lift_fst] at hg
  rw [hg]
  have hx : coefficientCoordinates x =
      fun i => (lift g x).left.appTop
        (coefficientCoordinates (snd G.X (coefficientSpace n R)) i) := by
    simpa only [coefficientCoordinates_comp, lift_snd] using
      (coefficientCoordinates_comp (lift g x)
        (snd G.X (coefficientSpace n R)))
  rw [hx]
  funext i
  exact (lift g x).left.appTop.hom.map_mulVec _ _ i

/-- The actual affine-space action associated to a matrix representation. -/
@[instance_reducible]
def schemeAction (ρ : MatrixRepresentation G n) :
    SchemeAction G (coefficientSpace n R) :=
  schemeActionOfPointLaws ρ.coefficientActionHom
    (by
      intro T x
      apply coefficientCoordinates_injective
      rw [coefficientCoordinates_actionHom, map_one,
        Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec])
    (by
      intro T g h x
      apply coefficientCoordinates_injective
      rw [coefficientCoordinates_actionHom, coefficientCoordinates_actionHom,
        coefficientCoordinates_actionHom, map_mul, Matrix.GeneralLinearGroup.coe_mul,
        Matrix.mulVec_mulVec])

/-- Coordinates of the categorical action are the given matrix-vector product. -/
@[simp] theorem coefficientCoordinates_act (ρ : MatrixRepresentation G n)
    {T : Over (Spec R)} (g : T ⟶ G.X) (x : T ⟶ coefficientSpace n R) :
    coefficientCoordinates (ρ.schemeAction.act g x) =
      (ρ.pointMatrix T g : Matrix n n Γ(T.left, ⊤)) *ᵥ coefficientCoordinates x :=
  ρ.coefficientCoordinates_actionHom g x

/-- The original all-test fixed-vector condition is actual scheme-action fixedness. -/
theorem isFixedVector_iff_isFixed (ρ : MatrixRepresentation G n) (v : n → R) :
    ρ.IsFixedVector v ↔ ρ.schemeAction.IsFixed (constantCoefficientPoint v) := by
  constructor
  · intro hv T b g
    apply coefficientCoordinates_injective
    rw [coefficientCoordinates_act, coefficientCoordinates_constant]
    exact hv T g
  · intro hv T g
    have h := congrArg coefficientCoordinates (hv T (toUnit T) g)
    simpa only [coefficientCoordinates_act, coefficientCoordinates_constant] using h

end Langlands.GroupScheme.MatrixRepresentation
