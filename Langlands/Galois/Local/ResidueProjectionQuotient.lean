import Langlands.Galois.Local.ResidueProjectionInertia

/-!
# The residue projection of a separable closure: the quotient by inertia

For a nonarchimedean local field `K` of either characteristic and a separable
closure `Ω` of `K`, the quotient of `Ω ≃ₐ[K] Ω` by the inertia subgroup
`SepClosed.absoluteInertia K Ω` is isomorphic, as a topological group, to the absolute
Galois group of the residue field `𝓀[K]`, by an isomorphism that sends the class of `σ`
to `SepClosed.absoluteResidueHom K Ω σ`.

This is the twenty-first clause of `ResidueProjectionProperties K Ω`
(`Galois/Local/ResidueProjectionStatement.lean`).
-/

noncomputable section

open ValuativeRel IsLocalRing

namespace Langlands.LocalGalois.SepClosed

universe uK uΩ

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]

local instance rpQuotientIsAlgebraic : Algebra.IsAlgebraic K Ω :=
    Algebra.IsSeparable.isAlgebraic K Ω
local instance rpQuotientNormedField : NontriviallyNormedField K := localNormedField K
local instance rpQuotientUltrametric : IsUltrametricDist K := localNormedField_ultrametric K
local instance rpQuotientComplete : CompleteSpace K := localNormedField_complete K
local instance rpQuotientResidueFinite : Finite (ResidueField (baseIntegers K)) :=
    localResidue_finite K

/-- The quotient of `Ω ≃ₐ[K] Ω` by the inertia subgroup `absoluteInertia K Ω` is isomorphic,
as a topological group, to the absolute Galois group of `𝓀[K]`. It is induced by the residue
homomorphism `absoluteResidueHom K Ω` (`absoluteResidueQuotientEquiv_apply`). -/
def absoluteResidueQuotientEquiv :
    ((Ω ≃ₐ[K] Ω) ⧸ absoluteInertia K Ω) ≃ₜ* Field.absoluteGaloisGroup 𝓀[K] :=
  (residueQuotientEquiv K Ω).trans (residueTransportEquiv K Ω)

/-- `absoluteResidueQuotientEquiv K Ω` sends the class of `σ` to
`absoluteResidueHom K Ω σ`. -/
theorem absoluteResidueQuotientEquiv_apply (σ : Ω ≃ₐ[K] Ω) :
    haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
    absoluteResidueQuotientEquiv K Ω (QuotientGroup.mk σ) = absoluteResidueHom K Ω σ :=
  rfl

end Langlands.LocalGalois.SepClosed
