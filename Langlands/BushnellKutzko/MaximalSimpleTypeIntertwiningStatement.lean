import Langlands.BushnellKutzko.SimpleTypes

/-! # Intertwining of maximal simple types (BK93 (5.5.11), printed p. 185; pp. 200, 203; V4) -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV uW

/-- **BK93 (5.5.11) in the maximal case, V4.** Let `(J, λ)` be a simple type.
(a) If it is of kind (a), exhibited by a simple stratum `[𝔄, n, 0, β]` with
`e(𝔅_β | 𝔬_E) = 1`, then every `x ∈ E^×`, `E = F[β]`, normalizes `J` and `λ`, and
`I_G(λ) = E^× J`. (b) If it is of kind (b), exhibited by `𝔄` with `e(𝔄 | 𝔬_F) = 1`, then
`I_G(λ) = F^× J`. -/
def MaximalSimpleTypeIntertwiningStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (J : Subgroup (Module.End F V)ˣ) (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ J W),
      (∀ (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice),
        IsSimpleTypeData ψF S q 1 ρ →
          let Eunits : Set (Module.End F V)ˣ :=
            {x | (x : Module.End F V) ∈ elementAlgebra S.b}
          (∀ x ∈ Eunits, IsPairIsomorphic (conjRepresentation x ρ) ρ) ∧
          representationSelfIntertwining ρ = Eunits * (J : Set (Module.End F V)ˣ)) ∧
      ∀ L : LatticeChain 𝒪[F] F V, IsLevelZeroSimpleTypeData L 1 ρ →
        representationSelfIntertwining ρ =
          Set.range (Units.map (algebraMap F (Module.End F V)).toMonoidHom) *
            (J : Set (Module.End F V)ˣ)

end Langlands.BushnellKutzko
