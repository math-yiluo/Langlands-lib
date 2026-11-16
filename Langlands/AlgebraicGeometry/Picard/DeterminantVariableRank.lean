import Langlands.AlgebraicGeometry.LocalSectionBasis
import Langlands.AlgebraicGeometry.Picard.CocycleLineBundleProof
import Langlands.LinearAlgebra.FiniteBasisDeterminant

/-! # Determinant lines from local frames of variable finite rank -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames

open Langlands.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {ι : Type u} {T : ι → X.Opens}
  {n : ι → ℕ}
  (e : ∀ i, SheafOfModules.free (R := X.ringCatSheaf.over (T i))
    (ULift.{u} (Fin (n i))) ≅ M.over (T i))

/-- Actual section bases indexed by the finite rank of each chart. -/
def basis (i : ι) {U : X.Opens} (hi : U ≤ T i) :
    Module.Basis (Fin (n i)) Γ(X, U) Γ(M, U) :=
  (localSectionBasis (e i) (Over.mk (homOfLE hi))).reindex Equiv.ulift

@[simp]
lemma basis_apply (i : ι) {U : X.Opens} (hi : U ≤ T i) (a : Fin (n i)) :
    basis e i hi a = localSectionBasis (e i) (Over.mk (homOfLE hi)) ⟨a⟩ :=
  (localSectionBasis (e i) (Over.mk (homOfLE hi))).reindex_apply Equiv.ulift a

lemma basis_restrict (i : ι) {U V : X.Opens} (hi : U ≤ T i) (h : V ≤ U)
    (a : Fin (n i)) :
    M.presheaf.map (homOfLE h).op (basis e i hi a) =
      basis e i (h.trans hi) a := by
  simp only [basis_apply]
  exact localSectionBasis_restrict (e i)
    (Over.homMk (homOfLE h) :
      Over.mk (homOfLE (h.trans hi)) ⟶ Over.mk (homOfLE hi)) _

lemma basis_repr_restrict (i : ι) {U V : X.Opens}
    (hi : U ≤ T i) (h : V ≤ U) (s : Γ(M, U)) (a : Fin (n i)) :
    (basis e i (h.trans hi)).repr (M.presheaf.map (homOfLE h).op s) a =
      X.presheaf.map (homOfLE h).op ((basis e i hi).repr s a) := by
  simp only [basis, Module.Basis.repr_reindex_apply]
  exact localSectionBasis_repr_restrict (e i)
    (Over.homMk (homOfLE h) :
      Over.mk (homOfLE (h.trans hi)) ⟶ Over.mk (homOfLE hi)) _ _

/-- The mixed determinant transition unit of the actual two section bases. -/
def unit (i j : ι) {U : X.Opens} (hi : U ≤ T i) (hj : U ≤ T j) :
    (Γ(X, U))ˣ :=
  Langlands.LinearAlgebra.FiniteBasisDeterminant.unit (basis e i hi) (basis e j hj)

@[simp]
lemma unit_self (i : ι) {U : X.Opens} (hi : U ≤ T i) :
    unit e i i hi hi = 1 :=
  Langlands.LinearAlgebra.FiniteBasisDeterminant.unit_self _

lemma unit_mul (i j k : ι) {U : X.Opens}
    (hi : U ≤ T i) (hj : U ≤ T j) (hk : U ≤ T k) :
    unit e i j hi hj * unit e j k hj hk = unit e i k hi hk :=
  Langlands.LinearAlgebra.FiniteBasisDeterminant.unit_mul _ _ _

/-- Mixed determinant units commute with restriction of actual sections. -/
lemma unit_restrict (i j : ι) {U V : X.Opens}
    (hi : U ≤ T i) (hj : U ≤ T j) (h : V ≤ U) :
    X.presheaf.map (homOfLE h).op (unit e i j hi hj : Γ(X, U)) =
      (unit e i j (h.trans hi) (h.trans hj) : Γ(X, V)) := by
  apply Langlands.LinearAlgebra.FiniteBasisDeterminant.map_unit
  intro a b
  rw [← basis_repr_restrict e i hi h, basis_restrict e j hj h]

/-- Transition functions for determinant lines on the pairwise overlaps. -/
def cocycle (i j : ι) : (Γ(X, T i ⊓ T j))ˣ :=
  unit e i j inf_le_left inf_le_right

lemma isCocycle : CocycleGluing.IsCocycle (cocycle e) := by
  intro i j k
  unfold cocycle
  rw [unit_restrict, unit_restrict, unit_restrict]
  exact congrArg Units.val (unit_mul e i j k _ _ _)

/-- The actual determinant line glued from frames of variable finite rank. -/
def lineBundle (hT : (⨆ i, T i) = ⊤) : LineBundle X :=
  ⟨CocycleGluing.glued (cocycle e),
    CocycleGluing.isLocallyFreeRankOne_glued (cocycle e) hT (isCocycle e)⟩

end Langlands.AlgebraicGeometry.Picard.VariableDeterminantFrames
