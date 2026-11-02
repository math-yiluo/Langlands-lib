import Langlands.GroupScheme.Rational.RelativeRoots
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-! # Real character and cocharacter spaces of actual group schemes -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped TensorProduct

namespace Langlands.GroupScheme.RealTorusSpace

private def extend {M P : Type*} [AddCommGroup M] [AddCommGroup P] [Module ℝ P]
    (f : M →ₗ[ℤ] P) : ℝ ⊗[ℤ] M →ₗ[ℝ] P :=
  AlgebraTensorModule.lift (LinearMap.toSpanSingleton ℝ (M →ₗ[ℤ] P) f)

private theorem extend_tmul {M P : Type*} [AddCommGroup M] [AddCommGroup P] [Module ℝ P]
    (f : M →ₗ[ℤ] P) (r : ℝ) (x : M) : extend f (r ⊗ₜ[ℤ] x) = r • f x := rfl

private def extendHom {M P : Type*} [AddCommGroup M] [AddCommGroup P] [Module ℝ P] :
    (M →ₗ[ℤ] P) →ₗ[ℤ] (ℝ ⊗[ℤ] M →ₗ[ℝ] P) where
  toFun := extend
  map_add' f g := AlgebraTensorModule.ext fun r x => by
    simp only [extend_tmul, LinearMap.add_apply, smul_add]
  map_smul' z f := AlgebraTensorModule.ext fun r x => by
    simp only [extend_tmul, LinearMap.smul_apply, RingHom.id_apply]
    exact smul_comm r z (f x)

variable {k : Type u} [Field k]

/-- The real cocharacter space of the actual commutative group scheme. -/
abbrev V (T : CommGroupScheme (Spec (CommRingCat.of k))) : Type u :=
  ℝ ⊗[ℤ] cocharacterLattice T

/-- The real character space of the actual commutative group scheme. -/
abbrev Vstar (T : CommGroupScheme (Spec (CommRingCat.of k))) : Type u :=
  ℝ ⊗[ℤ] characterLattice T

variable (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- Evaluation of an integral character on the real cocharacter space. -/
def eval (χ : characterLattice T) : V T →ₗ[ℝ] ℝ :=
  extend ((Int.castAddHom ℝ).toIntLinearMap.comp (latticePairing T χ))

@[simp] theorem eval_tmul (χ : characterLattice T) (s : ℝ) (ν : cocharacterLattice T) :
    eval T χ (s ⊗ₜ[ℤ] ν) = s * (latticePairing T χ ν : ℝ) := rfl

private def evalLattice : characterLattice T →ₗ[ℤ] (V T →ₗ[ℝ] ℝ) :=
  extendHom.comp ((latticePairing T).compr₂ (Int.castAddHom ℝ).toIntLinearMap)

/-- The real bilinear scalar extension of the actual integer lattice pairing. -/
def pair : Vstar T →ₗ[ℝ] V T →ₗ[ℝ] ℝ :=
  extend (evalLattice T)

@[simp] theorem pair_tmul_tmul (r s : ℝ) (χ : characterLattice T)
    (ν : cocharacterLattice T) :
    pair T (r ⊗ₜ[ℤ] χ) (s ⊗ₜ[ℤ] ν) = r * s * (latticePairing T χ ν : ℝ) := by
  change r * (s * (latticePairing T χ ν : ℝ)) = _
  rw [mul_assoc]

/-- The functional of a character is its pairing with the image `1 ⊗ χ`. -/
theorem eval_eq_pair (χ : characterLattice T) : eval T χ = pair T (1 ⊗ₜ[ℤ] χ) := by
  apply AlgebraTensorModule.ext
  intro s ν
  simp

/-- An actual relative root is evaluated through its underlying actual character. -/
def rootEval {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (α : relativeRoots i) : V T →ₗ[ℝ] ℝ :=
  eval T α.1

@[simp] theorem rootEval_apply {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (α : relativeRoots i) (v : V T) :
    rootEval T i α v = eval T α.1 v := rfl

end Langlands.GroupScheme.RealTorusSpace
