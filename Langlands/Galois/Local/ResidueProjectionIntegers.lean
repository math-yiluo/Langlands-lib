import Langlands.Galois.Local.AbsoluteDefinitions

/-!
# The residue projection of a separable closure: the valuation and the integers

For a nonarchimedean local field `K` of either characteristic and a separable
closure `Ω` of `K`, the integers `SepClosed.closureIntegers K Ω` of `Ω` are the
elements of `Ω` that are integral over `𝒪[K]`, and the valuation
`SepClosed.closureValuation K Ω` is invariant under `Ω ≃ₐ[K] Ω`.

These are the fifth and sixth clauses of `ResidueProjectionProperties K Ω`
(`Galois/Local/ResidueProjectionStatement.lean`).
-/

noncomputable section

open ValuativeRel IsLocalRing
open scoped NNReal

namespace Langlands.LocalGalois.SepClosed

universe uK uΩ

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local instance rpIntegersIsAlgebraic : Algebra.IsAlgebraic K Ω :=
    Algebra.IsSeparable.isAlgebraic K Ω
local instance rpIntegersNormedField : NontriviallyNormedField K := localNormedField K
local instance rpIntegersUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance rpIntegersComplete : CompleteSpace K := localNormedField_complete K

/-- An element of a separable closure `Ω` of `K` is integral over `𝒪[K]` exactly when it
lies in the integers `closureIntegers K Ω` of `Ω`. -/
theorem isIntegral_iff_mem_closureIntegers (x : Ω) :
    IsIntegral 𝒪[K] x ↔ x ∈ closureIntegers K Ω := by
  let e := RingEquiv.subringCongr (localNormedField_integer K)
  have hi : IsIntegral (baseIntegers K) x ↔ IsIntegral 𝒪[K] x :=
    e.isIntegral_iff (by ext y; rfl) x
  exact hi.symm.trans (integral_iff_mem_spectralIntegers K Ω x)

/-- The valuation `closureValuation K Ω` of a separable closure `Ω` of `K` is invariant under
every `K`-automorphism of `Ω`. -/
theorem closureValuation_algEquiv_apply (σ : Ω ≃ₐ[K] Ω) (x : Ω) :
    closureValuation K Ω (AlgEquiv.toAlgHom σ x) = closureValuation K Ω x := by
  apply NNReal.eq
  exact (spectralNorm_eq_of_equiv σ x).symm

end Langlands.LocalGalois.SepClosed
