import Langlands.BushnellKutzko.TameCorestriction

/-! # Tame corestriction existence and lattice images

Bushnell–Kutzko 1993, (1.3.2)–(1.3.4), printed pp. 28–29; T1.
-/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV uE

/-- **BK93 (1.3.2)–(1.3.4), pp. 28–29 (T1).** Tame corestrictions exist, differ
by a unit of `𝔬_E`, and send every `𝔓^n` onto `𝔓^n ∩ B`. -/
def TameCorestrictionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (V : Type uV) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (E : Type uE) [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V],
    Nonempty (TameCorestriction 𝒪[F] F E V) ∧
    (∀ s t : TameCorestriction 𝒪[F] F E V,
      ∃ u : (subfieldIntegers F E)ˣ, ∀ x : Module.End F V,
        t x = ((u : subfieldIntegers F E) : E) • s x) ∧
    (∀ (s : TameCorestriction 𝒪[F] F E V) (𝓛 : LatticeChain 𝒪[F] F V),
      (∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛.stabilizer) →
      ∀ n : ℤ, s '' (𝓛.endFiltration n : Set (Module.End F V)) =
        {b : Module.End E V | b.restrictScalars F ∈ 𝓛.endFiltration n})

end Langlands.BushnellKutzko
