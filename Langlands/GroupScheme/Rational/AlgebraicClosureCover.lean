import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Algebraic-closure covers of field-valued tests -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.QuasiSplitRegularConjugate

/-- The algebraic closure of `L`, as a cover of `Spec L` over `K`. -/
def algebraicClosureCoverPoint (K L : Type u) [Field K] [Field L] [Algebra K L] :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L)))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L)))) (by
    change Spec.map (CommRingCat.ofHom (algebraMap L (AlgebraicClosure L))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure L)))
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq K L (AlgebraicClosure L)])

end Langlands.GroupScheme.QuasiSplitRegularConjugate
