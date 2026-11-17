import Langlands.GroupScheme.InnerAutomorphism
import Langlands.GroupScheme.Torus.RelativeAdjointWeights
import Langlands.GroupScheme.Lie.ElementCentralizer
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.Rational.CrossTorusLieTransport

/-! # Differentials of actual inner automorphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
  [IsAffineHom G.X.hom]

/-- The actual differential equivalence induced by a base-section inner
automorphism, on every coefficient algebra. -/
def Lie.innerDifferentialEquiv
    (g : Over.mk (𝟙 (Spec R)) ⟶ G.X)
    (A : Type u) [CommRing A] [Algebra R A] :
    Additive (lieKernel G A) ≃ₗ[A] Additive (lieKernel G A) :=
  Lie.targetEquiv (G.innerIso g) A

/-- The differential of an actual inner automorphism is the actual adjoint
action of the same base section on every coefficient algebra. -/
theorem Lie.targetMapLinear_innerIso
    (g : Over.mk (𝟙 (Spec R)) ⟶ G.X)
    (A : Type u) [CommRing A] [Algebra R A]
    (X : Additive (lieKernel G A)) :
    Lie.targetMapLinear (G.innerIso g).hom A X =
      adjoint G A (G.constantPoint g _) X := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [lieKernelTargetLinear_val, G.comp_innerIso_hom, adjoint_val]
  rw [Lie.constant, Lie.affineMap_apply, G.constantPoint_naturality]

@[simp] theorem Lie.innerDifferentialEquiv_apply
    (g : Over.mk (𝟙 (Spec R)) ⟶ G.X)
    (A : Type u) [CommRing A] [Algebra R A]
    (X : Additive (lieKernel G A)) :
    Lie.innerDifferentialEquiv G g A X =
      adjoint G A (G.constantPoint g _) X :=
  Lie.targetMapLinear_innerIso G g A X

namespace splitTorus

variable {G} {I : Type u} [Fintype I]
  (i : splitTorus (Spec R) I ⟶ G) (m : I → ℤ)

/-- A torus base section acts on a relative exponent weight vector by its
actual exponent value, with no field or nonzero-ring premise. -/
theorem targetMapLinear_innerIso_weight
    (t : Over.mk (𝟙 (Spec R)) ⟶ (splitTorus (Spec R) I).X)
    (Y : exponentWeightSpace I G i m) :
    Lie.targetMapLinear (G.innerIso (t ≫ i.hom.hom)).hom R Y.val =
      (exponentValue I
        (algebraPointsEquiv I R ((splitTorus (Spec R) I).constantPoint t _))
        (Multiplicative.ofAdd m) : R) • Y.val := by
  rw [Lie.targetMapLinear_innerIso]
  have hself : lieKernelMapLinear G (Algebra.ofId R R) Y.val = Y.val := by
    change Additive.ofMul (lieKernelMap G (Algebra.ofId R R) Y.val.toMul) = Y.val
    have hi : Algebra.ofId R R = AlgHom.id R R := Subsingleton.elim _ _
    rw [hi, lieKernelMap_id]
    rfl
  have h := Y.property R
    (algebraPointsEquiv I R ((splitTorus (Spec R) I).constantPoint t _))
  rw [MulEquiv.symm_apply_apply, hself] at h
  exact h

variable {H : GroupScheme (Spec R)} [IsAffineHom H.X.hom]
  (f : H ⟶ G)

/-- An actual torus point with inverse character value removes a supplied
unit discrepancy in the actual differential. -/
theorem targetMapLinear_correct_unit
    (X : Additive (lieKernel H R)) (Y : exponentWeightSpace I G i m)
    (c : Rˣ)
    (hc : Lie.targetMapLinear f R X = (c : R) • Y.val)
    (t : Over.mk (𝟙 (Spec R)) ⟶ (splitTorus (Spec R) I).X)
    (ht : exponentValue I
      (algebraPointsEquiv I R ((splitTorus (Spec R) I).constantPoint t _))
      (Multiplicative.ofAdd m) = c⁻¹) :
    Lie.targetMapLinear (f ≫ (G.innerIso (t ≫ i.hom.hom)).hom) R X = Y.val := by
  rw [Lie.targetMapLinear_comp, LinearMap.comp_apply, hc, map_smul,
    targetMapLinear_innerIso_weight, ht, smul_smul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

end splitTorus

end Langlands.GroupScheme
