import Langlands.BushnellKutzko.DerivedStratum

/-! # Defining sequences (BK93 (2.4.2), printed pp. 65–66) -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

namespace Stratum

/-- For every tame corestriction relative to the actual generated field of `S`,
the derived stratum for the perturbation `b` exists and is equivalent to a
simple stratum over that field. Internal notation for (2.4.2)(vi). -/
def HasSimpleDerivedStratum (S : Stratum O K V) (b : Module.End K V) : Prop :=
  ∀ h : IsField (elementAlgebra S.b),
    letI := h.toField
    ∀ s : TameCorestriction O K (elementAlgebra S.b) V,
      S.DerivedEquivalentToSimple (elementAlgebra S.b) b s

/-- A family of simple strata `[𝔄,n,r_i,γ_i]`, `0 ≤ i ≤ s`, satisfying
all six conditions of BK93 (2.4.2), pp. 65–66, for the pure stratum `S`. -/
def IsDefiningSequence (S : Stratum O K V) {s : ℕ}
    (q : Fin (s + 1) → Stratum O K V) : Prop :=
  S.IsPure ∧
  (∀ i, (q i).chain.order = S.chain.order ∧ (q i).n = S.n ∧ (q i).IsSimple) ∧
  (q 0).Equivalent S ∧ (q 0).r = S.r ∧
  StrictMono (fun i => (q i).r) ∧
  (∀ i : Fin s,
    criticalExponent S.chain (q i.castSucc).b = ((-(q i.succ).r : ℤ) : WithBot ℤ) ∧
    (q i.succ).b - (q i.castSucc).b ∈ S.chain.endFiltration (-(q i.succ).r)) ∧
  (criticalExponent S.chain (q (Fin.last s)).b = ((-S.n : ℤ) : WithBot ℤ) ∨
    criticalExponent S.chain (q (Fin.last s)).b = ⊥) ∧
  (∀ i : Fin s,
    (q i.succ).HasSimpleDerivedStratum ((q i.castSucc).b - (q i.succ).b))

end Stratum

end Langlands.BushnellKutzko
