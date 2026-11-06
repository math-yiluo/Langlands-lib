import Langlands.LocalFactor.CommonClosure
import Langlands.Weil.Local.IntermediateWeil
import Langlands.Weil.Local.IrreducibleReductionProof
import Langlands.Weil.Representation.FiniteIndexRestrictionSemisimplicityProof

/-!
# Irreducible finite-image reduction in the prescribed common closure
-/

noncomputable section

universe uG uH uV uF

namespace Langlands.FiniteRepresentation

set_option backward.isDefEq.respectTransparency false in
/-- Surjective precomposition preserves irreducibility because it preserves
exactly the invariant subspaces on the original carrier. -/
theorem isIrreducible_restrict_of_surjective
    {G : Type uG} {H : Type uH} [Group G] [Group H]
    (φ : H →* G) (hφ : Function.Surjective φ)
    (A : FiniteRepresentation.{0, uG, uV} ℂ G) (hA : A.IsIrreducible) :
    (restrict φ A).IsIrreducible := by
  have hr : Set.range (restrict φ A).representation = Set.range A.representation :=
    hφ.range_comp A.representation
  exact (Weil.FiniteIndexRestrictionSemisimplicity.subrepresentationOrderIsoOfRangeEq
    (restrict φ A).representation A.representation hr).isSimpleOrder_iff.mpr hA

end Langlands.FiniteRepresentation

namespace Langlands.LocalFactor.CommonClosure

open Weil.Local FiniteRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The inverse of the intermediate-Weil equivalence as a continuous homomorphism
from the prescribed fixing subgroup to the standalone local Weil group. -/
def toIntermediateLocalWeil (E : Extension F) :
    weilSubgroup F E →ₜ* localWeilGroup (E.asPadicField (p := p)) where
  toMonoidHom := (intermediateWeilEquiv F E).symm.toMulEquiv.toMonoidHom
  continuous_toFun := (intermediateWeilEquiv F E).symm.continuous

set_option backward.isDefEq.respectTransparency false in
/-- Every actual continuous irreducible on the prescribed fixing subgroup is
an actual continuous-character twist of a continuous finite-image representation.
The statement uses the given subgroup topology and an independent carrier universe. -/
theorem irreducible_finiteImage_twist (E : Extension F)
    (A : FiniteRepresentation.{0, uF, uV} ℂ (weilSubgroup F E))
    (hc : A.IsContinuous) (hi : A.IsIrreducible) :
    ∃ (χ : weilSubgroup F E →ₜ* ℂˣ)
      (B : FiniteRepresentation.{0, uF, uV} ℂ (weilSubgroup F E)),
      B.IsContinuous ∧ B.HasFiniteImage ∧
        Nonempty (FiniteRepresentation.Equiv A
          (FiniteRepresentation.twist χ.toMonoidHom B)) := by
  let e : localWeilGroup E.asPadicField ≃ₜ* weilSubgroup F E :=
    intermediateWeilEquiv F E
  let A' := restrict e.toMulEquiv.toMonoidHom A
  have hc' : A'.IsContinuous :=
    isContinuous_restrict _ e.continuous hc
  have hi' : A'.IsIrreducible :=
    isIrreducible_restrict_of_surjective _ e.surjective A hi
  obtain ⟨z, B, hBc, _, hBf, _, ⟨he⟩⟩ :=
    ((localWeilIrreducibleReductionFor E.asPadicField) A' hc' hi').1
  let B' := restrict e.symm.toMulEquiv.toMonoidHom B
  let ei := toIntermediateLocalWeil F E
  let χ := (localUnramifiedCharacter E.asPadicField z).comp ei
  refine ⟨χ, B', isContinuous_restrict _ e.symm.continuous hBc, ?_, ?_⟩
  · exact hBf.subset (Set.range_comp_subset_range e.symm B.representation)
  · refine ⟨{ toLinearEquiv := he.toLinearEquiv, isIntertwining' := ?_ }⟩
    intro g
    ext v
    have h := congrArg (fun f => f v) (he.isIntertwining' (e.symm g))
    change he (A.representation (e (e.symm g)) v) =
      ((FiniteRepresentation.twist χ.toMonoidHom B').representation g) (he v) at h
    simpa [FiniteRepresentation.twist, FiniteRepresentation.restrict,
      B', LinearMap.comp_apply, e.apply_symm_apply] using! h

end Langlands.LocalFactor.CommonClosure
