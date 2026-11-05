import Langlands.Cohomology.RightDerivedLinear
import Langlands.AlgebraicGeometry.ModuleLinear
import Langlands.AlgebraicGeometry.Modules.DerivedSections

/-! # Base-linear action on actual relative cohomology -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {X : Scheme.{u}} {R : CommRingCat.{u}} (p : X ⟶ Spec R)

/-- Relative global sections respect the actual base-linear sheaf morphisms. -/
theorem relativeGlobalSections_linear :
    letI := Langlands.Scheme.Modules.linearOverBase p
    (relativeGlobalSections p).Linear R := by
  let := Langlands.Scheme.Modules.linearOverBase p
  refine ⟨fun f r => ?_⟩
  ext x
  change Langlands.Scheme.Modules.restrictScalar ⊤
    (Langlands.Scheme.Modules.scalarsFromBase p r) • f.app ⊤ x =
      Langlands.Scheme.Modules.scalarsFromBase p r • f.app ⊤ x
  congr 1
  simp [Langlands.Scheme.Modules.restrictScalar]

/-- Actual relative cohomology respects scalar multiplication of sheaf maps. -/
theorem relativeCohomology_linear (n : ℕ) :
    letI := Langlands.Scheme.Modules.linearOverBase p
    (relativeCohomology p n).Linear R := by
  let := Langlands.Scheme.Modules.linearOverBase p
  let := relativeGlobalSections_linear p
  exact Langlands.Cohomology.rightDerived_linear (relativeGlobalSections p) n

/-- The actual relative-cohomology action on a hom space as a base-linear map. -/
def relativeCohomologyHomLinearMap (n : ℕ) {M N : X.Modules} :
    letI := Langlands.Scheme.Modules.linearOverBase p
    (M ⟶ N) →ₗ[R]
      ((relativeCohomology p n).obj M ⟶ (relativeCohomology p n).obj N) := by
  letI := Langlands.Scheme.Modules.linearOverBase p
  letI := relativeGlobalSections_linear p
  exact Langlands.Cohomology.rightDerivedHomLinearMap (relativeGlobalSections p) n

@[simp]
lemma relativeCohomologyHomLinearMap_apply (n : ℕ) {M N : X.Modules} (a : M ⟶ N) :
    relativeCohomologyHomLinearMap p n a = (relativeCohomology p n).map a := rfl

/-- Multiplication by a base scalar on an actual sheaf map induces that scalar
on actual relative cohomology. -/
lemma relativeCohomology_map_scalarHom (n : ℕ) {M N : X.Modules}
    (r : R) (a : M ⟶ N) :
    (relativeCohomology p n).map
        (Langlands.Scheme.Modules.scalarHom (Langlands.Scheme.Modules.scalarsFromBase p r) a) =
      r • (relativeCohomology p n).map a := by
  let := Langlands.Scheme.Modules.linearOverBase p
  let := relativeCohomology_linear p n
  exact (relativeCohomology p n).map_smul r a

end Langlands.AlgebraicGeometry.Modules.DerivedSections
