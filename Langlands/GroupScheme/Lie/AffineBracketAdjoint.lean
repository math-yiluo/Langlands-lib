import Langlands.GroupScheme.Lie.AffineBracketMatrix
import Langlands.GroupScheme.Lie.AdjointDominance
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # The differential of the actual adjoint representation and the bracket -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Lie

attribute [local instance 100] LieRing.ofAssociativeRing

section Ring

variable {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffineHom G.X.hom]
    {d : ℕ} (c : FiniteCoordinates G d)

/-- The actual adjoint differential in finite tangent coordinates, bundled as a Lie action. -/
def adjointDifferentialLieHom : Additive (lieKernel G R) →ₗ⁅R⁆ Module.End R (Fin d → R) :=
  (lieEquivMatrix' (R := R) (n := Fin d)).symm.toLieHom.comp
    ((adjointRepresentation c).kernelDifferentialLieHom R)

@[simp] theorem adjointDifferentialLieHom_toLinearMap :
    (adjointDifferentialLieHom c).toLinearMap = adjointDifferentialFamily c := rfl

variable {n : Type} [Fintype n] [DecidableEq n]

/-- A faithful matrix realization identifies the actual adjoint differential
with the Lie bracket on the original tangent carrier. -/
theorem adjointDifferentialLieHom_apply_bracket_of_mono
    (ρ : MatrixRepresentation G n) (hρ : Mono ρ.hom.hom) (X Y : Additive (lieKernel G R)) :
    adjointDifferentialLieHom c X (c.equiv (.of R R) Y) = c.equiv (.of R R) ⁅X, Y⁆ := by
  change adjointDifferentialFamily c X (c.equiv (.of R R) Y) = c.equiv (.of R R) ⁅X, Y⁆
  apply (c.equiv (.of R R)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply kernelDifferential_injective (A := R) ρ hρ
  exact (kernelDifferential_adjointDifferentialFamily c ρ Y.toMul X.toMul).trans
    (ρ.kernelDifferential_commutator R X Y).symm

end Ring

section Field

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] {d : ℕ}

local instance : LieRing (Additive (lieKernel G (CommRingCat.of k))) :=
  instAffineKernelLieRing (R := CommRingCat.of k) (A := CommRingCat.of k) G

/-- Over a field, affine finite type supplies the faithful matrix realization needed
for the adjoint differential comparison. -/
theorem adjointDifferentialLieHom_apply_bracket (c : FiniteCoordinates G d)
    (X Y : Additive (lieKernel G (CommRingCat.of k))) :
    adjointDifferentialLieHom c X
        (c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k)) Y) =
      c.equiv (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))
        (⁅X, Y⁆ : Additive (lieKernel G (CommRingCat.of k))) := by
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  exact adjointDifferentialLieHom_apply_bracket_of_mono c ρ hρ.mono_overHom X Y

end Field

end Langlands.GroupScheme.Lie
