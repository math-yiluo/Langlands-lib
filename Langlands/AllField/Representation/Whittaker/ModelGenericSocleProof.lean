import Langlands.Representation.Whittaker.ModelGenericSocleProof
import Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorStatement
import Langlands.AllField.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
import Langlands.AllField.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllField.Representation.CuspidalSupport.JacquetSubquotientProof
import Langlands.AllField.Representation.CuspidalSupport.TotalConjugatingCountStatement
import Langlands.AllField.Representation.Geometric.GeometricLemmaStatement
import Langlands.AllField.Representation.Induction.SingleBlockSupplement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankSpecializationInputs
import Langlands.AllField.Representation.Unramified.SphericalConstituentExistenceProof
import Langlands.AllField.Representation.Whittaker.ModelGenericSocleStatement
/-!
# The actual irreducible generic socle of a Whittaker coefficient model

The coefficient model of a representation of Whittaker type is a quotient of
it, hence admissible of finite length. Evaluation at the identity is nonzero
on every nonzero invariant subspace of this function model, and the model's
functional space is at most one-dimensional. Exactness of the functional
functor then forbids two nonzero invariant subspaces with zero intersection,
so the unique atom is the least nonzero subrepresentation.
-/

noncomputable section

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding ModelGenericSocleStatement modelGenericSocle
open Langlands.AllField.Whittaker

open Langlands.HarmonicAnalysis hiding padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis

universe uF uG uV uW

section Algebraic


end Algebraic

section Smooth


end Smooth

/-- The coefficient model of a representation of Whittaker type has a least
nonzero subrepresentation; it is irreducible and of full Whittaker type. -/
theorem modelGenericSocle : ModelGenericSocleStatement.{uF,uV} := by
  intro F _ _ _ _
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  intro ψ n V _ _ σ hσ ℓ hℓ
  let := T.generalLinearTopologicalGroup (n + 1)
  intro M
  let U := GeneralLinear.upperUnipotent (n + 1) F
  let θ := standardCharacter ψ n
  let W := (glCoefficientModel ψ n σ ℓ).toSubmodule
  let j : M.IntertwiningMap (functionRepresentation U θ) :=
    { toLinearMap := W.subtype
      isIntertwining' := fun _ => rfl }
  obtain ⟨v, hv⟩ : ∃ v : V, ℓ.val v ≠ 0 := by
    by_contra! h
    exact hℓ (LinearMap.ext h)
  have hmv : modelMap σ ℓ v ≠ 0 := by
    intro h
    apply hv
    have h1 : ((modelMap σ ℓ v).val).val 1 = 0 := by
      rw [h]
      rfl
    change ℓ.val (σ 1 v) = 0 at h1
    rwa [map_one, Module.End.one_apply] at h1
  have : Nontrivial W := ⟨⟨modelMap σ ℓ v, 0, hmv⟩⟩
  exact exists_least_subrepresentation_of_functionModel (X := W)
    (Langlands.AllField.RankinSelberg.UnequalRankAssembly.generalLinear_compactOpen_cofinal F T n) U
    (Langlands.AllField.GeneralLinear.upperUnipotent_isLimitOfCompactSubgroups F T (n + 1)) θ
    (Langlands.AllField.RankinSelberg.UnequalRankAssembly.character_locallyConstant_of_whittakerType F T n θ σ hσ)
    hσ.1 (Langlands.AllField.RankinSelberg.UnequalRankAssembly.finiteLength_of_whittakerType F T n θ σ hσ) hσ.2.2
    M (modelMap σ ℓ) (modelMap_surjective σ ℓ) j Subtype.val_injective

end Langlands.AllField.Whittaker
