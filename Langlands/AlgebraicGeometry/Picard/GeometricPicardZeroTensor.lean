import Langlands.AlgebraicGeometry.Picard.GeometricPicardZero
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor

/-! # Tensor preserves translation invariance and geometric Picard zero -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LineBundle

open Langlands.Scheme.Modules

variable (preservation : pullbackTensorComparisonIsIsoStatement.{u})
variable {X Y : Scheme.{u}}

/-- Tensoring actual line-bundle isomorphisms. -/
def tensorIso {L L' M M' : LineBundle X} (e : L ≅ L') (d : M ≅ M') :
    tensor preservation L M ≅ tensor preservation L' M' := by
  rw [← tensorFunctor_obj preservation L M, ← tensorFunctor_obj preservation L' M']
  exact (tensorFunctor preservation X).mapIso (e.prod d)

/-- The fixed canonical tensor comparison on a pair of line bundles. -/
def pullbackTensorObjIso (f : X ⟶ Y) (L M : LineBundle Y) :
    (pullback f).obj (tensor preservation L M) ≅
      tensor preservation ((pullback f).obj L) ((pullback f).obj M) := by
  letI := preservation f
  exact ObjectProperty.isoMk _
    ((asIso (pullbackTensorComparison f)).app (L.obj, M.obj))

end Langlands.AlgebraicGeometry.Picard.LineBundle

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

variable (preservation : Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (G : GroupScheme S)

include preservation in
/-- Tensor of two translation-invariant line bundles is translation invariant. -/
lemma isTranslationInvariant_tensor {L M : LineBundle G.X.left}
    (hL : IsTranslationInvariant G L) (hM : IsTranslationInvariant G M) :
    IsTranslationInvariant G (LineBundle.tensor preservation L M) := by
  intro x
  obtain ⟨e⟩ := hL x
  obtain ⟨d⟩ := hM x
  exact ⟨LineBundle.pullbackTensorObjIso preservation (translation G x).left L M ≪≫
    LineBundle.tensorIso preservation e d⟩

end Langlands.GroupScheme

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

variable (preservation : Langlands.Scheme.Modules.pullbackTensorComparisonIsIsoStatement.{u})
variable {S : Scheme.{u}} (A : AbelianScheme S)

include preservation in
/-- The geometric-fibre Picard-zero condition is closed under the actual sheaf tensor. -/
lemma isGeometricallyPicardZero_tensor {L M : LineBundle A.X.left}
    (hL : IsGeometricallyPicardZero A L) (hM : IsGeometricallyPicardZero A M) :
    IsGeometricallyPicardZero A (LineBundle.tensor preservation L M) := by
  intro K _ _ s
  exact GroupScheme.isTranslationInvariant_of_iso _
    (LineBundle.pullbackTensorObjIso preservation (pullback.fst A.X.hom s) L M).symm
    (GroupScheme.isTranslationInvariant_tensor preservation _ (hL K s) (hM K s))

end Langlands.AbelianScheme
