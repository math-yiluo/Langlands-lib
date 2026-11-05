import Langlands.Global.IntegralModelComparison
import Langlands.Global.FiniteCompletionIntegers

/-! # Arithmetic model images using canonical local-field integers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj Pointwise ValuativeRel

namespace Langlands.Global.IntegralModelCompletions

open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable (F : Type u) [Field F] [NumberField F]
  (S : Finset (FinitePlace F)) (v : {v : FinitePlace F // v ∉ S})

local instance completionValuativeRel : ValuativeRel (FiniteCompletion F v.1) :=
  FiniteCompletion.valuativeRel v.1

/-- The original S-integer inclusion, with values in the canonical local integers. -/
def canonicalIntegerMap :
    (S : Set (FinitePlace F)).integer F →+* 𝒪[FiniteCompletion F v.1] :=
  (FiniteCompletion.canonicalIntegersEquiv v.1).symm.toRingHom.comp (integerMap F S v)

@[simp] theorem canonicalIntegerMap_coe (x : (S : Set (FinitePlace F)).integer F) :
    (canonicalIntegerMap F S v x : FiniteCompletion F v.1) =
      algebraMap F (FiniteCompletion F v.1) x.val :=
  rfl

local instance : Algebra ((S : Set (FinitePlace F)).integer F)
    𝒪[FiniteCompletion F v.1] := (canonicalIntegerMap F S v).toAlgebra

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
    𝒪[FiniteCompletion F v.1] (FiniteCompletion F v.1) :=
  IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace F)).integer F)
    (S := 𝒪[FiniteCompletion F v.1]) (A := FiniteCompletion F v.1) fun _ => rfl

local instance : IsScalarTower ((S : Set (FinitePlace F)).integer F)
    F (FiniteCompletion F v.1) :=
  IsScalarTower.of_algebraMap_eq (R := (S : Set (FinitePlace F)).integer F)
    (S := F) (A := FiniteCompletion F v.1) fun _ => rfl

/-- The canonical integer ring as the actual S-integer subalgebra of the completion. -/
def canonicalIntegerSubalgebra :
    Subalgebra ((S : Set (FinitePlace F)).integer F) (FiniteCompletion F v.1) where
  __ := 𝒪[FiniteCompletion F v.1]
  algebraMap_mem' r := (canonicalIntegerMap F S v r).property

private instance :
    IsFractionRing (canonicalIntegerSubalgebra F S v) (FiniteCompletion F v.1) :=
  inferInstanceAs (IsFractionRing 𝒪[FiniteCompletion F v.1] (FiniteCompletion F v.1))

variable {G : GroupScheme (Spec (CommRingCat.of F))}
  (M : IntegralModel ((S : Set (FinitePlace F)).integer F) F G)

/-- Specialize the supplied arithmetic model to the canonical local-field integers. -/
def canonicalModel : IntegralModel 𝒪[FiniteCompletion F v.1] (FiniteCompletion F v.1)
    ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G) :=
  M.baseChange 𝒪[FiniteCompletion F v.1] (FiniteCompletion F v.1)

/-- Its group is the actual pullback along the original S-integer inclusion. -/
theorem canonicalModel_group :
    (canonicalModel F S v M).group =
      (GroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (canonicalIntegerMap F S v)))).obj M.group :=
  rfl

/-- Smoothness of the supplied model is preserved. -/
theorem isSmooth_canonicalModel (hM : M.IsSmooth) :
    (canonicalModel F S v M).IsSmooth :=
  M.isSmooth_baseChange _ _ hM

/-- The canonical-integer model's image lies on the original coefficient-point carrier. -/
def canonicalSubgroup :
    Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1))) :=
  (canonicalModel F S v M).coefficientIntegralPoints F (FiniteCompletion F v.1)

/-- Canonical and original completed integers give exactly the same actual image. -/
theorem canonicalSubgroup_eq_subgroup :
    canonicalSubgroup F S v M = subgroup F S v M := by
  ext p
  have h := M.mem_baseChange_subalgebra_coefficientIntegralPoints_iff
    (FiniteCompletion F v.1) (canonicalIntegerSubalgebra F S v) p
  change p ∈ canonicalSubgroup F S v M ↔ _
  rw [mem_subgroup_iff F S v M]
  exact h.trans (forall_congr' fun a =>
    FiniteCompletion.mem_canonicalIntegers_iff v.1 _)

local instance canonicalCoefficientPointTopology :
    TopologicalSpace (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1))) :=
  G.affinePointsTopologicalSpace _

private instance canonicalGenericAffine [IsAffine G.X.left] :
    IsAffine
      ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G).X.left := by
  change IsAffine (Limits.pullback G.X.hom (Spec.algebraMap F (FiniteCompletion F v.1)))
  infer_instance

local instance canonicalGenericPointTopology [IsAffine G.X.left] :
    TopologicalSpace
      (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G)) :=
  rationalPointTopology (FiniteCompletion F v.1) _

/-- Compact maximality of the canonical model image transfers to the arithmetic image. -/
theorem subgroup_maximal_of_canonicalModel [IsAffine G.X.left]
    (hmax : ∀ L : Subgroup (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G)),
      IsCompact (L : Set (rationalPoints
        ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).obj G))) →
        (canonicalModel F S v M).integralPoints ≤ L →
          L = (canonicalModel F S v M).integralPoints) :
    ∀ L : Subgroup (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1))),
      IsCompact (L :
        Set (G.affinePoints (CommAlgCat.of F (FiniteCompletion F v.1)))) →
        subgroup F S v M ≤ L → L = subgroup F S v M := by
  rw [← canonicalSubgroup_eq_subgroup F S v M]
  exact (canonicalModel F S v M).coefficientIntegralPoints_maximal
    F (FiniteCompletion F v.1) hmax

/-- The literal parabolic-left covering transfers from the canonical model image. -/
theorem subgroup_covering_of_canonicalModel
    {P : GroupScheme (Spec (CommRingCat.of F))} (p : P ⟶ G)
    (hcover :
      Set.range
          (rationalPoints.map
            ((GroupScheme.baseChange (Spec.algebraMap F (FiniteCompletion F v.1))).map p)) *
        ((canonicalModel F S v M).integralPoints : Set _) = Set.univ) :
    Set.range (P.affinePointsTarget p (CommAlgCat.of F (FiniteCompletion F v.1))) *
      (subgroup F S v M : Set _) = Set.univ := by
  rw [← canonicalSubgroup_eq_subgroup F S v M]
  exact (canonicalModel F S v M).coefficientIntegralPoints_covering
    F (FiniteCompletion F v.1) p hcover

end Langlands.Global.IntegralModelCompletions
