import Langlands.BushnellKutzko.BetaExtension
import Langlands.BushnellKutzko.SimpleCharacterRestrictionLow
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Extending relative-unit quotients to products with congruence groups -/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.SplitTypeJacquet

section Product

variable {G D : Type*} [Group G] [Group D] {B U : Subgroup G}
  (hn : B ≤ Subgroup.normalizer (U : Set G))
  (q : B →* D) (hq : U.subgroupOf B ≤ q.ker)

/-- Extend a homomorphism from `B` to `B ⊔ U` by sending `U` to the identity. -/
def extendProductHom : (B ⊔ U : Subgroup G) →* D :=
  letI := Subgroup.normal_subgroupOf_of_le_normalizer hn
  letI := Subgroup.normal_subgroupOf_sup_of_le_normalizer hn
  (QuotientGroup.lift (U.subgroupOf B) q hq).comp <|
    (QuotientGroup.quotientInfEquivProdNormalizerQuotient B U hn).symm.toMonoidHom.comp <|
      QuotientGroup.mk' (U.subgroupOf (B ⊔ U))

theorem extendProductHom_apply_left (b : B) :
    extendProductHom hn q hq (Subgroup.inclusion le_sup_left b) = q b := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hn
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hn
  let e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B U hn
  have he : e (QuotientGroup.mk b) =
      QuotientGroup.mk (Subgroup.inclusion le_sup_left b) := rfl
  change QuotientGroup.lift (U.subgroupOf B) q hq
    (e.symm (QuotientGroup.mk (Subgroup.inclusion le_sup_left b))) = q b
  rw [← he, MulEquiv.symm_apply_apply, QuotientGroup.lift_mk']

theorem extendProductHom_apply_right (u : U) :
    extendProductHom hn q hq (Subgroup.inclusion le_sup_right u) = 1 := by
  let := Subgroup.normal_subgroupOf_of_le_normalizer hn
  let := Subgroup.normal_subgroupOf_sup_of_le_normalizer hn
  have hu : (QuotientGroup.mk (Subgroup.inclusion le_sup_right u) :
      (B ⊔ U : Subgroup G) ⧸ U.subgroupOf (B ⊔ U)) = 1 :=
    (QuotientGroup.eq_one_iff _).2 u.property
  simp [extendProductHom, hu]

theorem extendProductHom_surjective (hs : Function.Surjective q) :
    Function.Surjective (extendProductHom hn q hq) := by
  intro d
  obtain ⟨b, rfl⟩ := hs d
  exact ⟨_, extendProductHom_apply_left hn q hq b⟩

theorem extendProductHom_ker (hk : q.ker ≤ U.subgroupOf B) :
    (extendProductHom hn q hq).ker = U.subgroupOf (B ⊔ U) := by
  ext g
  have hg : (g : G) ∈ ((B ⊔ U : Subgroup G) : Set G) := g.property
  rw [Subgroup.coe_mul_of_left_le_normalizer_right B U hn] at hg
  obtain ⟨b, hb, u, hu, hbu⟩ := hg
  let b' : B := ⟨b, hb⟩
  let u' : U := ⟨u, hu⟩
  have hg' : g = Subgroup.inclusion le_sup_left b' * Subgroup.inclusion le_sup_right u' :=
    Subtype.ext hbu.symm
  rw [hg', MonoidHom.mem_ker, map_mul, extendProductHom_apply_left,
    extendProductHom_apply_right, mul_one, Subgroup.mem_subgroupOf]
  change q b' = 1 ↔ b * u ∈ U
  exact ⟨fun hb₁ => U.mul_mem (hk hb₁) hu, fun hbu₁ =>
    hq (show b ∈ U from (U.mul_mem_cancel_right hu).mp hbu₁)⟩

end Product

section Simple

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (S : Stratum 𝒪[F] F V) (hr : S.r = 0) (hs : S.IsSimple) (q : S.DefiningSequenceChoice)

local notation "B" => relativeUnitFiltration S.chain S.b 0
local notation "J" => simpleJ S.chain S.n S.b q.tail
local notation "J₁" => simpleJGroup S.chain S.n S.b q.tail 1

theorem relativeUnits_le_normalizer_unitFiltration (m : ℕ) :
    B ≤ Subgroup.normalizer (S.chain.unitFiltration m : Set (Module.End F V)ˣ) := by
  rw [(normalizer F V S.chain).2.2.1 m]
  exact fun _ hx => ((normalizer F V S.chain).1 0).1 hx.2

include hr hs in
theorem relativeUnits_le_normalizer_simpleJOne :
    B ≤ Subgroup.normalizer (J₁ : Set (Module.End F V)ˣ) :=
  fun _ hx => ((simpleStratumGroupProperties F V S hr hs q).2.2.1 1).2
    ⟨hx.1, ((normalizer F V S.chain).1 0).1 hx.2⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem relativeUnitFiltration_one_le_simpleJOne : relativeUnitFiltration S.chain S.b 1 ≤ J₁ := by
  intro g hg
  apply Subgroup.subset_closure
  refine ⟨hg.2, ?_⟩
  have hc : (g : Module.End F V) ∈ centralizerLattice S.chain S.b 0 := by
    refine ⟨S.chain.mem_order_iff_mem_endFiltration.1 hg.2.1, ?_⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker]
    have h : S.b * (g : Module.End F V) = (g : Module.End F V) * S.b := hg.1
    simp [adjointMap, h]
  cases q.tail <;> exact Submodule.mem_sup_left hc

include hr hs in
/-- The centralizer units and the first `J` group generate `J`. -/
theorem simpleJ_eq_sup : J = B ⊔ J₁ := by
  have hB : B ≤ B ⊔ J₁ := le_sup_left
  have hJ₁ : J₁ ≤ B ⊔ J₁ := le_sup_right
  apply le_antisymm _ (sup_le (relativeUnitFiltration_le_simpleJ _ _ _ _)
    (simpleJGroup_one_le_simpleJ _ _ _ _))
  intro g hg
  by_cases hβ : elementAlgebra S.b = ⊥
  · have hscalar := Algebra.self_mem_adjoin_singleton F S.b
    change S.b ∈ elementAlgebra S.b at hscalar
    rw [hβ, Algebra.mem_bot] at hscalar
    obtain ⟨c, hc⟩ := hscalar
    have hcomm : S.b * (g : Module.End F V) = (g : Module.End F V) * S.b := by
      rw [← hc, Algebra.commutes]
    exact hB ⟨hcomm, simpleJGroup_le_unitFiltration S.chain S.n S.b q.tail 0 hg⟩
  · let k := simpleJCutoff (finiteCriticalDepth S.chain S.n S.b)
    have hk : 1 ≤ k := by
      have hd := finiteCriticalDepth_pos_of_simple hr hs
      dsimp only [k, simpleJCutoff]
      omega
    have hprod := (simpleStratumGroupProperties F V S hr hs q).2.1 hβ |>.2 0
      (by exact_mod_cast (show 0 ≤ k by omega))
    change g ∈ (simpleJGroup S.chain S.n S.b q.tail 0 : Set (Module.End F V)ˣ) at hg
    rw [hprod] at hg
    obtain ⟨b, hb, u, hu, rfl⟩ := hg
    exact mul_mem (hB hb) (hJ₁
      (simpleJGroup_antitone S.chain S.n S.b q.tail
        (show 1 ≤ k.toNat by omega) hu))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An element of the relative order's unit group is in `J¹` exactly when it lies
in the ambient first congruence subgroup. -/
theorem simpleJOne_subgroupOf_relativeUnits :
    (J₁).subgroupOf B = (S.chain.unitFiltration 1).subgroupOf B := by
  ext g
  constructor
  · intro hg
    exact simpleJGroup_le_unitFiltration _ _ _ _ 1 (show g.val ∈ J₁ from hg)
  · intro hg
    exact relativeUnitFiltration_one_le_simpleJOne S q ⟨g.property.1, hg⟩

end Simple

end Langlands.BushnellKutzko.SplitTypeJacquet
