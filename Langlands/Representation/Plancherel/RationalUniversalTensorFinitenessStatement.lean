import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedModels
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Projective

/-! Renard VI.8.1 on the literal universal tensor and all rational norms. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe uG uI uV u

section FixedMap

variable {L : Type uG} [Group L] [TopologicalSpace L]
  {I : Type uI} (ν : I → (L →* ℝ≥0ˣ)) (hν : ∀ i, Continuous (ν i))
  {E : Type uV} [AddCommGroup E] [Module ℂ E]
  (σ : Representation ℂ L E) (J : Subgroup L) (hJ : IsCompact (J : Set L))

local instance tensorFixedAddCommGroup (V : Type*) [AddCommGroup V] [Module ℂ V] :
    AddCommGroup (unramifiedRegularFunctions ν ⊗[ℂ] V) := TensorProduct.addCommGroup

/-- The canonical tensor of the original fixed-space inclusion, with codomain
in the fixed submodule of the actual universal action. -/
def universalTensorFixedInclusion :
    unramifiedRegularFunctions ν ⊗[ℂ] fixedVectors σ J →ₗ[unramifiedRegularFunctions ν]
      fixedVectors (universalUnramifiedRepresentation ν σ) J :=
  ((fixedVectors σ J).subtype.baseChange (unramifiedRegularFunctions ν)).codRestrict
    (fixedVectors (universalUnramifiedRepresentation ν σ) J) (by
      intro t
      induction t using TensorProduct.inductionOn with
      | tmul b v =>
        intro j
        change universalUnramifiedRepresentation ν σ (j : L) (b ⊗ₜ[ℂ] (v : E)) = _
        have hj : (j : L) ∈ commonNormKernel ν := by
          apply (mem_commonNormKernel ν _).mpr
          intro i
          exact RankinSelberg.LastRowReduction.eq_one_of_isCompact (ν i) (hν i) J hJ j.property
        rw [universalUnramifiedRepresentation_tmul,
          unramifiedEvaluationRegular_eq_one_of_mem_commonNormKernel ν hj, one_mul]
        exact congrArg (fun w : E => b ⊗ₜ[ℂ] w) (v.property j)
      | add t s ht hs =>
        simpa only [map_add] using Submodule.add_mem _ ht hs)

end FixedMap

namespace RationalNormalized

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)

local instance finitenessAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance finitenessPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X
local instance finitenessTensorAddCommGroup (E : Type*) [AddCommGroup E] [Module ℂ E] :
    AddCommGroup (RegularAlgebra r ⊗[ℂ] E) := TensorProduct.addCommGroup

variable {E : Type uV} [AddCommGroup E] [Module ℂ E]
  (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E)

/-- Flatness is a conclusion on the literal tensor, not a field in model data. -/
def UniversalTensorFlatness (_σ : Representation ℂ (parabolicLeviPointSubgroup p l) E) : Prop :=
  Module.Flat (RegularAlgebra r) (RegularAlgebra r ⊗[ℂ] E)

/-- The actual B-linear compact-fixed inclusion for all rational-character norms. -/
abbrev tensorFixedInclusion (J : Subgroup (parabolicLeviPointSubgroup p l))
    (hJ : IsCompact (J : Set (parabolicLeviPointSubgroup p l))) :=
  universalTensorFixedInclusion (parabolicLeviRationalNormCharacters r)
    (continuous_parabolicLeviRationalNormCharacters r) σ J hJ

/-- The comparison is in the claimed direction; its inverse is the concrete
inclusion b tensor v ↦ b tensor v into the actual universal fixed submodule. -/
def UniversalTensorFixedComparison (J : Subgroup (parabolicLeviPointSubgroup p l))
    (hJ : IsCompact (J : Set (parabolicLeviPointSubgroup p l))) : Prop :=
  ∃ e : fixedVectors (universalRepresentation r σ) J ≃ₗ[RegularAlgebra r]
      RegularAlgebra r ⊗[ℂ] fixedVectors σ J,
    e.symm.toLinearMap = tensorFixedInclusion r σ J hJ

/-- Finite projectivity of the compact-open fixed B-module of the actual action. -/
def UniversalTensorFixedFiniteProjectivity
    (J : OpenSubgroup (parabolicLeviPointSubgroup p l)) : Prop :=
  Module.Finite (RegularAlgebra r) (fixedVectors (universalRepresentation r σ) J.toSubgroup) ∧
  Module.Projective (RegularAlgebra r) (fixedVectors (universalRepresentation r σ) J.toSubgroup)

/-- Source-sized conclusions for one admissible complex Levi representation. -/
def UniversalTensorFiniteness : Prop :=
  UniversalTensorFlatness r σ ∧
    ∀ (J : OpenSubgroup (parabolicLeviPointSubgroup p l))
      (hJ : IsCompact (J : Set (parabolicLeviPointSubgroup p l))),
      UniversalTensorFixedComparison r σ J.toSubgroup hJ ∧
      UniversalTensorFixedFiniteProjectivity r σ J

/-- Renard VI.8.1 example and finite-projectivity criterion, on actual rational
points, with independent representation-carrier universe. -/
def RationalUniversalTensorFinitenessStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (M P : GroupScheme (Spec (CommRingCat.of F))) [IsAffine M.X.left]
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      (p : P ⟶ G) (l : M ⟶ P) (a : A.toGrp ⟶ M)
      (r : ParabolicRootPresentation p l a)
      (E : Type uV) [AddCommGroup E] [Module ℂ E]
      (σ : Representation ℂ (parabolicLeviPointSubgroup p l) E),
      IsAdmissible σ → UniversalTensorFiniteness r σ

end RationalNormalized
end Langlands.Plancherel
