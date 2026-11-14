import Langlands.AlgebraicGeometry.LocalSectionBasis
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof
import Mathlib.LinearAlgebra.Matrix.Basis

/-! # Determinant line bundles from actual finite local frames -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.DeterminantFrames

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules}
  {ι I : Type u} [Fintype I] {T : ι → X.Opens}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i)) I ≅ M.over (T i))

local instance : DecidableEq I := Classical.decEq I

/-- The actual frame of sections on an open inside the `i`-th frame chart. -/
def basis (i : ι) {U : X.Opens} (h : U ≤ T i) :
    Module.Basis I Γ(X, U) Γ(M, U) :=
  localSectionBasis (e i) (Over.mk (homOfLE h))

/-- Change of coordinates between the two actual local frames. -/
def matrix (i j : ι) {U : X.Opens} (hi : U ≤ T i) (hj : U ≤ T j) :
    Matrix I I Γ(X, U) :=
  (basis e i hi).toMatrix (basis e j hj)

@[simp]
lemma matrix_self (i : ι) {U : X.Opens} (h : U ≤ T i) :
    matrix e i i h h = 1 :=
  Module.Basis.toMatrix_self _

lemma matrix_mul (i j k : ι) {U : X.Opens}
    (hi : U ≤ T i) (hj : U ≤ T j) (hk : U ≤ T k) :
    matrix e i j hi hj * matrix e j k hj hk = matrix e i k hi hk :=
  Module.Basis.toMatrix_mul_toMatrix _ _ _

/-- Change-of-frame matrices restrict along the actual structure-sheaf maps. -/
lemma matrix_restrict (i j : ι) {U V : X.Opens}
    (hi : U ≤ T i) (hj : U ≤ T j) (h : V ≤ U) :
    (matrix e i j hi hj).map (X.presheaf.map (homOfLE h).op) =
      matrix e i j (h.trans hi) (h.trans hj) := by
  ext a b
  change X.presheaf.map (homOfLE h).op
      ((basis e i hi).repr (basis e j hj b) a) =
    (basis e i (h.trans hi)).repr (basis e j (h.trans hj) b) a
  calc
    _ = (basis e i (h.trans hi)).repr
        (M.presheaf.map (homOfLE h).op (basis e j hj b)) a :=
      (localSectionBasis_repr_restrict (e i)
        (Over.homMk (homOfLE h) :
          Over.mk (homOfLE (h.trans hi)) ⟶ Over.mk (homOfLE hi)) _ a).symm
    _ = _ := congrArg (fun s => (basis e i (h.trans hi)).repr s a)
      (localSectionBasis_restrict (e j)
        (Over.homMk (homOfLE h) :
          Over.mk (homOfLE (h.trans hj)) ⟶ Over.mk (homOfLE hj)) b)

/-- The determinant of a change of frame is a unit, with the reverse change as inverse. -/
def unit (i j : ι) {U : X.Opens} (hi : U ≤ T i) (hj : U ≤ T j) :
    (Γ(X, U))ˣ where
  val := (matrix e i j hi hj).det
  inv := (matrix e j i hj hi).det
  val_inv := by rw [← Matrix.det_mul, matrix_mul, matrix_self, Matrix.det_one]
  inv_val := by rw [← Matrix.det_mul, matrix_mul, matrix_self, Matrix.det_one]

@[simp]
lemma unit_val (i j : ι) {U : X.Opens} (hi : U ≤ T i) (hj : U ≤ T j) :
    (unit e i j hi hj : Γ(X, U)) = (matrix e i j hi hj).det := rfl

lemma unit_restrict (i j : ι) {U V : X.Opens}
    (hi : U ≤ T i) (hj : U ≤ T j) (h : V ≤ U) :
    X.presheaf.map (homOfLE h).op (unit e i j hi hj : Γ(X, U)) =
      (unit e i j (h.trans hi) (h.trans hj) : Γ(X, V)) := by
  simp only [unit_val, RingHom.map_det]
  exact congrArg Matrix.det (matrix_restrict e i j hi hj h)

/-- The determinant transition function on each pairwise overlap. -/
def cocycle (i j : ι) : (Γ(X, T i ⊓ T j))ˣ :=
  unit e i j inf_le_left inf_le_right

/-- The determinant transition functions satisfy the actual triple-overlap cocycle law. -/
lemma isCocycle : CocycleGluing.IsCocycle (cocycle e) := by
  intro i j k
  unfold cocycle
  rw [unit_restrict, unit_restrict, unit_restrict]
  simp only [unit_val]
  rw [← Matrix.det_mul, matrix_mul]

/-- The actual line bundle glued from determinants of the supplied local frames. -/
def lineBundle (hT : (⨆ i, T i) = ⊤) : LineBundle X :=
  ⟨CocycleGluing.glued (cocycle e),
    CocycleGluing.isLocallyFreeRankOne_glued (cocycle e) hT (isCocycle e)⟩

end Langlands.AlgebraicGeometry.Picard.DeterminantFrames
