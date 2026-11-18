import Langlands.BushnellKutzko.UnitFiltration

/-! # Adjoint lattices and the critical exponent

Bushnell–Kutzko 1993, (1.4.1), (1.4.3), (1.4.5)–(1.4.6), printed pp. 35–36.
-/

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uK uV

variable (O : Type uO) {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- The adjoint map `a_β(x) = βx − xβ` (BK93 (1.4.1), p. 35). -/
def adjointMap (β : Module.End K V) : Module.End K V →ₗ[O] Module.End K V :=
  LinearMap.mulLeft O β - LinearMap.mulRight O β

variable {O}

/-- `𝔑_k(β,𝔄) = {x ∈ 𝔄 : a_β(x) ∈ 𝔓^k}` (BK93 (1.4.3), p. 36). -/
def adjointLattice (𝓛 : LatticeChain O K V) (β : Module.End K V) (k : ℤ) :
    Submodule O (Module.End K V) :=
  𝓛.endFiltration 0 ⊓ (𝓛.endFiltration k).comap (adjointMap O β)

/-- The intersection `𝔓^k ∩ B`, where `B` is the centralizer of `β`.
For `E = K[β]` a field normalized by the order, this is `𝔔^k` by the published
subfield-order statement; `k = 0` gives `𝔅`. -/
def centralizerLattice (𝓛 : LatticeChain O K V) (β : Module.End K V) (k : ℤ) :
    Submodule O (Module.End K V) :=
  𝓛.endFiltration k ⊓ (adjointMap O β).ker

/-- The integer set whose maximum defines `k₀` (BK93 (1.4.5), p. 36). -/
def criticalIndexSet (𝓛 : LatticeChain O K V) (β : Module.End K V) : Set ℤ :=
  {k | ¬ adjointLattice 𝓛 β k ≤ centralizerLattice 𝓛 β 0 ⊔ 𝓛.endFiltration 1}

open scoped Classical in
/-- The critical exponent `k₀(β,𝔄)` (BK93 (1.4.5)–(1.4.6), p. 36).
It is `−∞` if `K[β] = K`, and otherwise the integer supremum of `criticalIndexSet`.
T2 separately asserts that under the source hypotheses this is its greatest element. -/
def criticalExponent (𝓛 : LatticeChain O K V) (β : Module.End K V) : WithBot ℤ :=
  if Algebra.adjoin K ({β} : Set (Module.End K V)) = ⊥ then ⊥
  else ((sSup (criticalIndexSet 𝓛 β) : ℤ) : WithBot ℤ)

end Langlands.BushnellKutzko
