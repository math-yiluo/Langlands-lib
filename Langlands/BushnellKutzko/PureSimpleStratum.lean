import Langlands.BushnellKutzko.Stratum
import Langlands.BushnellKutzko.AdjointCriticalExponent
import Langlands.BushnellKutzko.SubfieldIntegers

/-! # Pure and simple strata (BK93 (1.5.5), printed p. 43) -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- The actual generated algebra `K[β]` in `End_K(V)`. -/
abbrev elementAlgebra (β : Module.End K V) : Subalgebra K (Module.End K V) :=
  Algebra.adjoin K ({β} : Set (Module.End K V))

namespace Stratum

/-- A pure stratum: the generated algebra is a field whose units normalize
the order, and `v_𝔄(b) = −n` (BK93 (1.5.5)(i)–(iii), p. 43). -/
def IsPure (S : Stratum O K V) : Prop :=
  (∃ h : IsField (elementAlgebra S.b),
    letI := h.toField
    ∀ a : (elementAlgebra S.b)ˣ,
      subfieldUnits K (elementAlgebra S.b) V a ∈ S.chain.stabilizer) ∧
  S.chain.valuation S.b = (-S.n : WithTop ℤ)

/-- A simple stratum: pure and `r < −k₀(b,𝔄)` (BK93 (1.5.5)(iv), p. 43).
The inequality is expressed as `k₀ < −r`, including `k₀ = −∞`. -/
def IsSimple (S : Stratum O K V) : Prop :=
  S.IsPure ∧ criticalExponent S.chain S.b < ((-S.r : ℤ) : WithBot ℤ)

end Stratum

end Langlands.BushnellKutzko
