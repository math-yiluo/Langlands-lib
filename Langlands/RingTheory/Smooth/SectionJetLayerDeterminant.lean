import Langlands.RingTheory.Smooth.SectionJetLayerNaturality
import Langlands.LinearAlgebra.HomogeneousPolynomialDeterminant

/-! # Actual augmentation-layer determinant transitions -/

noncomputable section

universe u v w

namespace Algebra.SectionJet.Coordinates

open MvPolynomial
open Langlands.GroupScheme.CoordinateWeights

open Langlands.LinearAlgebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    {ε : A →ₐ[R] R} {σ : Type w} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
/-- The linear forms defining cotangent basis change are the columns of the
actual basis transition matrix. -/
theorem linearForm_basis_repr
    (b b' : Module.Basis σ R (RingHom.ker ε).Cotangent) (j : σ) :
    linearForm (b.repr (b' j)) = HomogeneousPolynomial.column (b.toMatrix b') j := by
  rw [linearForm, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_fintype (b.repr (b' j))
    (fun i (r : R) => r • (X i : MvPolynomial σ R)) (fun i => zero_smul R _)]
  simp only [HomogeneousPolynomial.column, Module.Basis.toMatrix_apply, smul_eq_C_mul]

omit [DecidableEq σ] in
theorem cotangentBasisChange_eq_action
    (b b' : Module.Basis σ R (RingHom.ker ε).Cotangent) (d : ℕ) :
    cotangentBasisChange b b' d = HomogeneousPolynomial.action (b.toMatrix b') d := by
  apply LinearMap.ext
  intro p
  apply Subtype.ext
  change aeval (fun j => linearForm (b.repr (b' j))) p.val =
    aeval (HomogeneousPolynomial.column (b.toMatrix b')) p.val
  rw [show (fun j => linearForm (b.repr (b' j))) = HomogeneousPolynomial.column (b.toMatrix b') from
    funext (linearForm_basis_repr b b')]

variable [FormallySmooth R A]

/-- The actual layer basis obtained by evaluating homogeneous monomials in lifts
of a specified actual cotangent basis. -/
def layerBasis (z : σ → A) (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, AugmentedAlgebra.classMap ε (z s) = b s) (n : ℕ) :
    Module.Basis (HomogeneousPolynomial.MonomialIndex σ (n + 1)) R (Layer ε n) :=
  (HomogeneousPolynomial.monomialBasis σ (n + 1) R).map (homogeneousEquivLayer z b hz hzb n)

/-- The transition matrix of the actual layer bases is the homogeneous
representation of the actual cotangent transition matrix. -/
theorem layerBasis_toMatrix
    (z : σ → A) (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, AugmentedAlgebra.classMap ε (z s) = b s)
    (z' : σ → A) (b' : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz' : ∀ s, ε (z' s) = 0)
    (hzb' : ∀ s, AugmentedAlgebra.classMap ε (z' s) = b' s) (n : ℕ) :
    (layerBasis z b hz hzb n).toMatrix (layerBasis z' b' hz' hzb' n) =
      HomogeneousPolynomial.representation (b.toMatrix b') (n + 1) := by
  ext e f
  rw [Module.Basis.toMatrix_apply]
  have hvector : layerBasis z' b' hz' hzb' n f =
      homogeneousEquivLayer z b hz hzb n
        (HomogeneousPolynomial.action (b.toMatrix b') (n + 1) (HomogeneousPolynomial.monomialBasis σ (n + 1) R f)) := by
    change homogeneousToLayer z' hz' n (HomogeneousPolynomial.monomialBasis σ (n + 1) R f) =
      homogeneousToLayer z hz n
        (HomogeneousPolynomial.action (b.toMatrix b') (n + 1) (HomogeneousPolynomial.monomialBasis σ (n + 1) R f))
    rw [← cotangentBasisChange_eq_action]
    exact (homogeneousToLayer_cotangentBasisChange
      z b hz hzb z' b' hz' hzb' n _).symm
  rw [hvector]
  change (HomogeneousPolynomial.monomialBasis σ (n + 1) R).repr
      ((homogeneousEquivLayer z b hz hzb n).symm
        (homogeneousEquivLayer z b hz hzb n
          (HomogeneousPolynomial.action (b.toMatrix b') (n + 1) (HomogeneousPolynomial.monomialBasis σ (n + 1) R f)))) e = _
  rw [LinearEquiv.symm_apply_apply, HomogeneousPolynomial.representation, LinearMap.toMatrix_apply]

/-- The determinant of the actual layer transition is the corresponding positive
natural power of the actual cotangent transition determinant. -/
theorem layerBasis_toMatrix_det
    (z : σ → A) (b : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz : ∀ s, ε (z s) = 0)
    (hzb : ∀ s, AugmentedAlgebra.classMap ε (z s) = b s)
    (z' : σ → A) (b' : Module.Basis σ R (RingHom.ker ε).Cotangent)
    (hz' : ∀ s, ε (z' s) = 0)
    (hzb' : ∀ s, AugmentedAlgebra.classMap ε (z' s) = b' s) (n : ℕ) :
    ((layerBasis z b hz hzb n).toMatrix (layerBasis z' b' hz' hzb' n)).det =
      (b.toMatrix b').det ^ HomogeneousPolynomial.exponent σ (n + 1) := by
  rw [layerBasis_toMatrix, HomogeneousPolynomial.det_representation]

end Algebra.SectionJet.Coordinates
