import Langlands.GroupScheme.IdentityJetAffineGenerators
import Langlands.AlgebraicGeometry.Modules.StabilizedSectionGenerators

/-! # Actual global ambient generators of identity jets -/

noncomputable section

universe u

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.GroupScheme.IdentityJet

open AffineCoordinates Corepresented
open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.Scheme.Modules

variable {R : CommRingCat.{u}} {S : Scheme.{u}}
  (G : GroupScheme (Spec R)) [IsAffine G.X.left]
  (b : S ⟶ Spec R) {H : GroupScheme S} [IsAffineHom H.X.hom]
  (h : H ⟶ (GroupScheme.baseChange b).obj G)

/-- The fixed ambient truncated coordinates give an actual global R-linear jet family. -/
def ambientGlobalGenerator (n : ℕ) :
    (algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)) →ₗ[R]
      (relativeGlobalSections b).obj (module H n) where
  toFun := fun z => ambientQuotientCoordinates G b h n z
  map_add' := fun x y => (ambientQuotientCoordinates G b h n).map_add x y
  map_smul' r z := by
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
    change jetCoordinateMap H (ambientProjection G b h) n ⊤ (r • c) =
      (projection H n).app ⊤ (b.appTop ((Scheme.ΓSpecIso R).inv r)) *
        jetCoordinateMap H (ambientProjection G b h) n ⊤ c
    rw [Algebra.smul_def, map_mul, jetCoordinateMap_eq, ambient_coordinateMap_algebraMap]
    rw [show b.appLE ⊤ ⊤ (by simp) = b.appTop from
      Scheme.Hom.appLE_eq_app b (U := ⊤)]
    rfl

@[simp]
theorem ambientGlobalGenerator_apply (n : ℕ)
    (z : algebra G ⧸ augIdeal (corepresentation G) ^ (n + 1)) :
    (show Γ(module H n, ⊤) from ambientGlobalGenerator G b h n z) =
      ambientQuotientCoordinates G b h n z := rfl

/-- Extending the actual global family over an affine open gives the existing
actual ambient tensor map. -/
theorem globalFamilyTensorMap_ambientGlobalGenerator (n : ℕ) (U : S.affineOpens) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom b U
    globalFamilyTensorMap b (module H n) (ambientGlobalGenerator G b h n) U =
      ambientTensorCoordinates G b h n U := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom b U
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul a c => rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

end Langlands.GroupScheme.IdentityJet
