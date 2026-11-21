import Langlands.BushnellKutzko.SimpleStratumGroups

/-! # The subgroup properties (BK93 (3.1.14)–(3.1.15), printed p. 95; U2) -/

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uF uV

/-- **BK93 (3.1.14)–(3.1.15), U2.** The intersections are subgroups;
relative-unit product, normalizers, inclusions, normality and commutator bounds. -/
def SimpleStratumGroupPropertiesStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V), S.r = 0 → S.IsSimple → ∀ q : S.DefiningSequenceChoice,
    let H := simpleHGroup S.chain S.n S.b q.tail
    let J := simpleJGroup S.chain S.n S.b q.tail
    let U := relativeUnitFiltration S.chain S.b
    let K := relativeOrderNormalizer S.chain S.b
    let r := finiteCriticalDepth S.chain S.n S.b
    let G := (Module.End F V)ˣ
    (∀ m, (H m : Set G) = simpleHCarrier S.chain S.n S.b q.tail m ∧
      (J m : Set G) = simpleJCarrier S.chain S.n S.b q.tail m) ∧
    (elementAlgebra S.b ≠ ⊥ →
      (∀ m : ℕ, (m : ℤ) ≤ simpleHCutoff r →
        (H m : Set G) = (U m : Set G) * (H (simpleHCutoff r).toNat : Set G)) ∧
      (∀ m : ℕ, (m : ℤ) ≤ simpleJCutoff r →
        (J m : Set G) = (U m : Set G) * (J (simpleJCutoff r).toNat : Set G))) ∧
    (∀ m, K ≤ Subgroup.normalizer (H m : Set G) ∧ K ≤ Subgroup.normalizer (J m : Set G)) ∧
    (∀ m : ℕ, H m ≤ J m ∧ H (m + 1) ≤ J 0 ∧ J 0 ≤ Subgroup.normalizer (H (m + 1) : Set G)) ∧
    (∀ k l : ℕ, 1 ≤ k → 1 ≤ l → ⁅J k, J l⁆ ≤ H (k + l))

end Langlands.BushnellKutzko
