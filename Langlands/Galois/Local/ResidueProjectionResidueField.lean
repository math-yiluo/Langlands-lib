import Langlands.Galois.Local.AbsoluteDefinitions

/-!
# The residue projection of a separable closure: the residue field

For a nonarchimedean local field `K` of either characteristic and a separable
closure `Ω` of `K`, the residue field of the integers `SepClosed.closureIntegers K Ω`
is, through `SepClosed.residueAlgebra K Ω`, an algebraic closure of `𝓀[K]`, and the
comparison `SepClosed.residueClosureEquiv K Ω` with `AlgebraicClosure 𝓀[K]` sends the
residue of the image of `a ∈ 𝒪[K]` to the image of the residue of `a`.

These are the seventh and eighth clauses of `ResidueProjectionProperties K Ω`
(`Galois/Local/ResidueProjectionStatement.lean`).
-/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.LocalGalois.SepClosed

universe uK uΩ

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local instance rpResidueFieldIsAlgebraic : Algebra.IsAlgebraic K Ω :=
    Algebra.IsSeparable.isAlgebraic K Ω
local instance rpResidueFieldNormedField : NontriviallyNormedField K := localNormedField K
local instance rpResidueFieldUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance rpResidueFieldComplete : CompleteSpace K := localNormedField_complete K

/-- For a separable closure `Ω` of `K`, the residue field of the integers of `Ω`, with the
`𝓀[K]`-algebra structure `residueAlgebra K Ω`, is an algebraic closure of `𝓀[K]`. -/
theorem residueAlgebra_isAlgClosure :
    letI := residueAlgebra K Ω
    IsAlgClosure 𝓀[K] (ResidueField (closureIntegers K Ω)) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  let := residueAlgebra K Ω
  have : Algebra.IsIntegral 𝓀[K] (ResidueField (closureIntegers K Ω)) :=
    ⟨fun x => (isIntegral_algEquiv (residueClosureAlgEquiv K Ω)).mp
      (Algebra.IsIntegral.isIntegral (residueClosureAlgEquiv K Ω x))⟩
  exact
    { isAlgClosed := (residue_isAlgClosure K Ω).isAlgClosed
      isAlgebraic := inferInstance }

/-- The comparison `residueClosureEquiv K Ω` sends the residue of the image in the integers of
`Ω` of an element `a` of `𝒪[K]` to the image in `AlgebraicClosure 𝓀[K]` of the residue of
`a`. -/
theorem residueClosureEquiv_residue_integerMap (a : 𝒪[K]) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    residueClosureEquiv K Ω (residue _ (integerMap K Ω a)) =
      algebraMap 𝓀[K] (AlgebraicClosure 𝓀[K]) (residue 𝒪[K] a) := by
  have h : algebraMap (ResidueField (baseIntegers K)) (ResidueField (closureIntegers K Ω))
      ((localResidueEquiv K).symm (residue 𝒪[K] a)) =
        residue _ (integerMap K Ω a) := rfl
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  rw [← h, residueClosureEquiv_base, RingEquiv.apply_symm_apply]

end Langlands.LocalGalois.SepClosed
