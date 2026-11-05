import Langlands.GroupScheme.IntegralModel.BaseChange
import Langlands.GroupScheme.IntegralModel.CompactPoints
import Langlands.Global.AdelicLevelModelPoints
import Langlands.Global.IntegralFiniteAdeles

/-! # Arithmetic integral models on actual finite completions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Global.IntegralModelCompletions

open Langlands.GroupScheme

variable (F : Type u) [Field F] [NumberField F]
  (S : Finset (FinitePlace F)) (v : {v : FinitePlace F // v ∉ S})

/-- The published S-integer action on the actual completed integer ring. -/
def integerMap : (S : Set (FinitePlace F)).integer F →+* v.1.adicCompletionIntegers F :=
  @algebraMap _ _ _ _
    (inferInstanceAs (Algebra ((S : Set (FinitePlace F)).integer F)
      (NumberFieldLevelFactor F S (.inr (.inr v)))))

@[simp] theorem integerMap_coe (x : (S : Set (FinitePlace F)).integer F) :
    (integerMap F S v x : FiniteCompletion F v.1) =
      algebraMap F (FiniteCompletion F v.1) x.val := rfl

local instance : Algebra ((S : Set (FinitePlace F)).integer F)
    (v.1.adicCompletionIntegers F) := (integerMap F S v).toAlgebra

local instance : Algebra ((S : Set (FinitePlace F)).integer F)
    (FiniteCompletion F v.1) :=
  ((algebraMap F (FiniteCompletion F v.1)).comp
    (algebraMap ((S : Set (FinitePlace F)).integer F) F)).toAlgebra

local instance : SMul ((S : Set (FinitePlace F)).integer F) F :=
  (inferInstance : Algebra ((S : Set (FinitePlace F)).integer F) F).toSMul

local instance : SMul ((S : Set (FinitePlace F)).integer F) (FiniteCompletion F v.1) :=
  (inferInstance : Algebra ((S : Set (FinitePlace F)).integer F)
    (FiniteCompletion F v.1)).toSMul

local instance : IsScalarTower ((S : Set (FinitePlace F)).integer F)
    (v.1.adicCompletionIntegers F) (FiniteCompletion F v.1) :=
  IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace F)).integer F)
    (S := v.1.adicCompletionIntegers F) (A := FiniteCompletion F v.1) fun _ => rfl

local instance : IsScalarTower ((S : Set (FinitePlace F)).integer F)
    F (FiniteCompletion F v.1) :=
  IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace F)).integer F)
    (S := F) (A := FiniteCompletion F v.1) fun _ => rfl

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)

/-- A supplied S-integer model specialized to the canonical completed integers. -/
def model : IntegralModel (v.1.adicCompletionIntegers F) (FiniteCompletion F v.1)
    ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G) :=
  M.baseChange (v.1.adicCompletionIntegers F) (FiniteCompletion F v.1)

/-- The underlying model is exactly the actual pullback along the published inclusion. -/
theorem model_group :
    (model F S v M).group =
      (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (integerMap F S v)))).obj
        M.group := rfl

/-- Smoothness is preserved in every completion outside the supplied finite set. -/
theorem isSmooth_model (hM : M.IsSmooth) : (model F S v M).IsSmooth :=
  M.isSmooth_baseChange _ _ hM

/-- Actual arithmetic section restriction commutes with the specified generic evaluation. -/
theorem model_integralPointMap (x : M.integralSections) :
    (model F S v M).integralPointMap
        (baseChangeSectionHom (Spec.map (CommRingCat.ofHom (integerMap F S v))) M.group x) =
      baseChangeSectionHom (Spec.algebraMap F (FiniteCompletion F v.1)) G
        (M.integralPointMap x) :=
  M.baseChange_integralPointMap _ _ x

local instance coefficientPointTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1))) :=
  G.affinePointsTopologicalSpace _

/-- The local model's actual image in the original coefficient-point carrier. -/
def subgroup : Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1))) :=
  (model F S v M).coefficientIntegralPoints F (FiniteCompletion F v.1)

/-- Over the actual compact completed integer ring, the model image is compact. -/
theorem isCompact_subgroup [IsAffine G.X.left] :
    IsCompact (subgroup F S v M :
      Set (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1)))) := by
  let : CompactSpace (v.1.adicCompletionIntegers F) :=
    isCompact_iff_compactSpace.mp (isCompact_adicCompletionIntegers F v.1)
  exact (model F S v M).isCompact_coefficientIntegralPoints F
    (FiniteCompletion F v.1) continuous_subtype_val

end Langlands.Global.IntegralModelCompletions
