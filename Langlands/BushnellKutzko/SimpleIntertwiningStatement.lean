import Langlands.BushnellKutzko.PureSimpleStratum
import Langlands.BushnellKutzko.FormalIntertwining

/-! # Intertwining of a simple stratum (BK93 (1.5.8), p. 44; T4) -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uO uK uV uF

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- The image of `Bˣ` in `Aˣ`, for the centralizer `B` of `β`. -/
def centralizerUnits (β : Module.End K V) : Set (Module.End K V)ˣ :=
  {g | β * (g : Module.End K V) = (g : Module.End K V) * β}

namespace Stratum

/-- The factor `1 + 𝔔^{−(r+k)}𝔑_k` in BK93 (1.5.8).
In the scalar case `k₀ = −∞`, the factor is `{1}`. -/
def simpleIntertwiningNeighborhood (S : Stratum O K V) : Set (Module.End K V)ˣ :=
  {g | (criticalExponent S.chain S.b = ⊥ ∧ g = 1) ∨
    ∃ k : ℤ, criticalExponent S.chain S.b = (k : WithBot ℤ) ∧
      (g : Module.End K V) - 1 ∈
        centralizerLattice S.chain S.b (-(S.r + k)) * adjointLattice S.chain S.b k}

end Stratum

/-- **BK93 (1.5.8), printed p. 44 (T4).** The full formal intertwining set of
a simple stratum is `(1 + 𝔔^{−(r+k)}𝔑_k) Bˣ (1 + 𝔔^{−(r+k)}𝔑_k)`. -/
def SimpleIntertwiningStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (S : Stratum 𝒪[F] F V),
    S.IsSimple →
      S.formalSelfIntertwining =
        S.simpleIntertwiningNeighborhood * centralizerUnits S.b *
          S.simpleIntertwiningNeighborhood

end Langlands.BushnellKutzko
