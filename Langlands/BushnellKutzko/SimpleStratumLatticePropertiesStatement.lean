import Langlands.BushnellKutzko.SimpleStratumGroups

/-! # The lattice properties (BK93 (3.1.9)–(3.1.13), printed pp. 91–94; U1) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uV

/-- The two-sided ideal conditions on a submodule viewed in the ambient algebra. -/
private def IsTwoSidedIn {O A : Type*} [CommRing O] [Ring A] [Algebra O A]
    (I R : Submodule O A) : Prop := I ≤ R ∧ R * I ≤ I ∧ I * R ≤ I

/-- **BK93 (3.1.9)–(3.1.13), U1.** Independence, orders and ideals, high-degree
agreement with a critical approximation, relative fractional ideal products and
normalization, cross-products, and stability under equivalent simple strata. -/
def SimpleStratumLatticePropertiesStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple →
    ∀ q : S.DefiningSequenceChoice,
    let L := S.chain
    let H := simpleHLattice L S.n S.b q.tail
    let J := simpleJLattice L S.n S.b q.tail
    let Hk := simpleHLayer L S.n S.b q.tail
    let Jk := simpleJLayer L S.n S.b q.tail
    let Q := centralizerLattice L S.b
    let d := simpleCriticalDepth L S.b
    let r := finiteCriticalDepth L S.n S.b
    -- (a)
    (∀ q' : S.DefiningSequenceChoice,
      H = simpleHLattice L S.n S.b q'.tail ∧ J = simpleJLattice L S.n S.b q'.tail) ∧
    -- (b)
    (H.IsLattice F ∧ J.IsLattice F ∧
      (∃ R : Subalgebra 𝒪[F] (Module.End F V), R.toSubmodule = H) ∧
      (∃ R : Subalgebra 𝒪[F] (Module.End F V), R.toSubmodule = J) ∧
      Q 0 ≤ H ∧ H ≤ J ∧ J ≤ L.order.toSubmodule ∧
      ∀ k, IsTwoSidedIn (Hk k) H ∧ IsTwoSidedIn (Jk k) J ∧ Hk k ≤ Jk k) ∧
    -- (c)
    (∀ T : Stratum 𝒪[F] F V, S.IsCriticalApproximation T →
      ∀ q' : T.DefiningSequenceChoice,
        (∀ k : ℕ, simpleHCutoff r ≤ (k : ℤ) →
          Hk k = simpleHLayer L S.n T.b q'.tail k) ∧
        (∀ k : ℕ, simpleJCutoff r ≤ (k : ℤ) →
          Jk k = simpleJLayer L S.n T.b q'.tail k)) ∧
    -- (d)
    (∀ k : ℕ,
      (∀ m : ℤ, Q m * Hk k = Hk k * Q m ∧ Q m * Jk k = Jk k * Q m) ∧
      ∀ g ∈ relativeOrderNormalizer L S.b, ∀ x : Module.End F V,
        (↑g * x * ↑g⁻¹ ∈ Hk k ↔ x ∈ Hk k) ∧ (↑g * x * ↑g⁻¹ ∈ Jk k ↔ x ∈ Jk k)) ∧
    -- (e)
    ((∀ k, Q 1 * Jk k ≤ Hk (k + 1)) ∧
      (∀ k l : ℕ, 1 ≤ k → 1 ≤ l → Jk k * Jk l ≤ Hk (k + l)) ∧
      (∀ k : ℕ, 1 ≤ k → IsTwoSidedIn (Hk k) J)) ∧
    -- (f)
    (∀ T : Stratum 𝒪[F] F V, T.chain.order = L.order → T.n = S.n → T.IsSimple →
      (T.r : WithTop ℤ) < d → T.b - S.b ∈ L.endFiltration (-T.r) →
      ∀ q' : T.DefiningSequenceChoice,
        (∀ k : ℕ, (if d = ⊤ then 0 else max 0 (T.r + 1 - simpleJCutoff r)) ≤ (k : ℤ) →
          simpleHLayer L S.n T.b q'.tail k = Hk k) ∧
        (∀ k : ℕ, (if d = ⊤ then 0 else max 0 (T.r - r / 2)) ≤ (k : ℤ) →
          simpleJLayer L S.n T.b q'.tail k = Jk k))

end Langlands.BushnellKutzko
