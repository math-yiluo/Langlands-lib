import Langlands.BushnellKutzko.HeisenbergRepresentationStatement
import Langlands.BushnellKutzko.HeisenbergCharacterLocalData
import Langlands.BushnellKutzko.HeisenbergIntertwiningComparison
import Langlands.BushnellKutzko.HeisenbergIntertwiningFactor
import Langlands.BushnellKutzko.SimpleCharacterPairingStatement

/-! # Heisenberg representations from the commutator pairing and character intertwining -/

noncomputable section

open ValuativeRel
open scoped Pointwise commutatorElement MonoidAlgebra

namespace Langlands.BushnellKutzko

open HeisenbergCharacter

universe uF uV uW uW₁ uW₂

section Pairing

variable {G : Type*} [Group G] {H J : Subgroup G} (hHJ : H ≤ J) (θ : H →* ℂˣ)

local notation "K" => H.subgroupOf J
local notation "χ" =>
  MonoidHom.comp θ (MulEquiv.toMonoidHom (Subgroup.subgroupOfEquivOfLe hHJ))

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

private theorem scalar_of_normalized_contains [(K).Normal]
    (hχ : ∀ (g : J) (a : K), χ ⟨g * a * g⁻¹,
      Subgroup.Normal.conj_mem inferInstance _ a.2 g⟩ = χ a)
    (ρ : Representation ℂ J W) (hirr : ρ.IsIrreducible)
    (hcontains : ∃ f : (characterRepresentation θ).IntertwiningMap
      (ρ.comp (Subgroup.inclusion hHJ)), f ≠ 0) :
    ∀ a : H, ρ (Subgroup.inclusion hHJ a) = (θ a : ℂ) • LinearMap.id := by
  have := hirr
  obtain ⟨f, hf⟩ := hcontains
  let e := Subgroup.subgroupOfEquivOfLe hHJ
  let f' : (characterRepresentation χ).IntertwiningMap (ρ.comp (K).subtype) :=
    ⟨f.toLinearMap, fun a => f.2 (e a)⟩
  have hf' : f' ≠ 0 := by
    intro h
    apply hf
    have heq := congrArg (fun t : (characterRepresentation χ).IntertwiningMap
      (ρ.comp (K).subtype) => t.toLinearMap) h
    exact Representation.IntertwiningMap.ext heq
  intro a
  exact scalar_of_contains hχ ρ ⟨f', hf'⟩ (e.symm a)

private theorem scalar_kernel_contains (ρ : Representation ℂ J W)
    (hρ : ∀ a : H, ρ (Subgroup.inclusion hHJ a) = (θ a : ℂ) • LinearMap.id)
    {N : Subgroup J} (hN : ∀ x ∈ N, ∃ hx : (x : G) ∈ H, θ ⟨(x : G), hx⟩ = 1) :
    N ≤ ρ.ker := by
  intro x hx
  obtain ⟨h, hθ⟩ := hN x hx
  change ρ (Subgroup.inclusion hHJ (⟨(x : G), h⟩ : H)) = 1
  rw [hρ, hθ, Units.val_one, one_smul, Module.End.one_eq_id]

private theorem normalized_of_commutator_pairing [(K).Normal]
    (B : (J ⧸ K) →* ((J ⧸ K) →* ℂˣ))
    (hp : ∀ x y : J, ∃ h : ⁅(x : G), (y : G)⁆ ∈ H,
      B (QuotientGroup.mk' K x) (QuotientGroup.mk' K y) = θ ⟨_, h⟩) :
    ∀ (g : J) (a : K), χ ⟨g * a * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ a.2 g⟩ = χ a := by
  intro g a
  obtain ⟨hc, he⟩ := hp g a
  let c : K := ⟨⁅g, (a : J)⁆, hc⟩
  have ha : QuotientGroup.mk' K (a : J) = 1 := (QuotientGroup.eq_one_iff _).mpr a.2
  rw [ha, map_one] at he
  have hc' : χ c = 1 := he.symm
  have heq : (⟨g * a * g⁻¹, Subgroup.Normal.conj_mem inferInstance _ a.2 g⟩ : K) = c * a := by
    apply Subtype.ext
    exact conj_eq_commutatorElement_mul
  rw [heq, map_mul, hc', one_mul]

private theorem trace_zero_off_scalar_subgroup [(K).Normal]
    (B : (J ⧸ K) →* ((J ⧸ K) →* ℂˣ))
    (hp : ∀ x y : J, ∃ h : ⁅(x : G), (y : G)⁆ ∈ H,
      B (QuotientGroup.mk' K x) (QuotientGroup.mk' K y) = θ ⟨_, h⟩)
    (hrad : ∀ x : J ⧸ K, (∀ y : J ⧸ K, B x y = 1) → x = 1)
    (ρ : Representation ℂ J W)
    (hρ : ∀ a : H, ρ (Subgroup.inclusion hHJ a) = (θ a : ℂ) • LinearMap.id) :
    ∀ x : J, (x : G) ∉ H → ρ.character x = 0 := by
  intro x hx
  obtain ⟨y, hy⟩ : ∃ y : J, B (QuotientGroup.mk' K x) (QuotientGroup.mk' K y) ≠ 1 := by
    by_contra! h
    exact hx ((QuotientGroup.eq_one_iff (N := K) x).mp (hrad _ fun q => by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective K q
      exact h y))
  obtain ⟨hc, he⟩ := hp x y
  let c : H := ⟨⁅(x : G), (y : G)⁆, hc⟩
  have hc' : θ c ≠ 1 := fun h => hy (he.trans h)
  have hi : (θ c⁻¹ : ℂ) ≠ 1 := by
    intro h
    have hu : θ c⁻¹ = 1 := Units.ext h
    rw [map_inv, inv_eq_one] at hu
    exact hc' hu
  apply character_eq_zero_of_commutator ρ x y _ hi
  have hl : Subgroup.inclusion hHJ c⁻¹ = ⁅y, x⁆ := Subtype.ext (commutatorElement_inv _ _)
  rw [← hl]
  exact hρ c⁻¹

end Pairing

private theorem criticalDepth_ge_one {F : Type uF} [Field F] [ValuativeRel F]
    {V : Type uV} [AddCommGroup V] [Module F V]
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hS : S.IsSimple) :
    ((1 : ℤ) : WithTop ℤ) ≤ simpleCriticalDepth S.chain S.b := by
  have h := hS.2
  rw [h0, neg_zero] at h
  cases hr : criticalExponent S.chain S.b with
  | bot => simp [simpleCriticalDepth, hr]
  | coe a =>
    have ha : a < (0 : ℤ) := WithBot.coe_lt_coe.mp (hr ▸ h)
    rw [simpleCriticalDepth, hr]
    change ((1 : ℤ) : WithTop ℤ) ≤ ((-a : ℤ) : WithTop ℤ)
    exact WithTop.coe_le_coe.mpr (by omega)

/-- The commutator pairing, character intertwining formula and subgroup properties
imply the Heisenberg representation proposition. -/
def HeisenbergRepresentationReductionStatement : Prop :=
  SimpleCharacterPairingStatement.{uF, uV} →
    SimpleCharacterIntertwiningStatement.{uF, uV} →
    SimpleStratumGroupPropertiesStatement.{uF, uV} →
    HeisenbergRepresentationStatement.{uF, uV, uW, uW₁, uW₂}

/-- The reduction supplies existence, uniqueness, the scalar and dimension formulas, and
the ambient intertwining set in the published scope. -/
theorem heisenbergRepresentation_of :
    HeisenbergRepresentationReductionStatement.{uF, uV, uW, uW₁, uW₂} := by
  intro hpairing hintertwining hgroups F _ _ _ _ V _ _ ψF hψ S h0 hS q θ hθ
  let H := simpleHGroup S.chain S.n S.b q.tail 1
  let J := simpleJGroup S.chain S.n S.b q.tail 1
  let K := H.subgroupOf J
  let hHJ : H ≤ J := simpleHGroup_le_simpleJGroup S.chain S.n S.b q.tail 1
  let e := Subgroup.subgroupOfEquivOfLe hHJ
  have hn : 0 < S.n := h0 ▸ S.r_lt_n
  have hn₁ : (1 : ℤ) ≤ S.n := by omega
  have hd := criticalDepth_ge_one S h0 hS
  obtain ⟨-, hnormal, B, hp, -, hrad⟩ := hpairing F V ψF hψ S h0 hS q 0 (by simpa using hn₁)
    (by simpa using hd) θ hθ
  let : K.Normal := hnormal
  have hχ := normalized_of_commutator_pairing hHJ θ B hp
  obtain ⟨k, hk, hdeep⟩ := simpleCharacter_trivial_on_deep_units S.chain S.n hψ S.b q.tail 0 hθ
  let U := (S.chain.unitFiltration k).subgroupOf J
  have hJU : J ≤ S.chain.unitFiltration 1 := simpleJGroup_le_unitFiltration _ _ _ _ _
  have hU : U.FiniteIndex := by
    obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    let := S.chain.unitFiltration_finiteIndex_in_one k'
    change ((S.chain.unitFiltration (k' + 1)).subgroupOf J).FiniteIndex
    rw [← Subgroup.comap_inclusion_subgroupOf hJU]
    infer_instance
  let : U.FiniteIndex := hU
  let N := U.normalCore
  let : N.Normal := inferInstanceAs U.normalCore.Normal
  let : N.FiniteIndex := inferInstanceAs U.normalCore.FiniteIndex
  have hNU : N ≤ U := Subgroup.normalCore_le U
  have hNdata (g : J) (hg : g ∈ N) : ∃ h : (g : (Module.End F V)ˣ) ∈ H, θ ⟨_, h⟩ = 1 :=
    hdeep g (hNU hg)
  have hNK : N ≤ K := fun g hg => (hNdata g hg).1
  let : K.FiniteIndex := Subgroup.finiteIndex_of_le hNK
  have hd0 : (0 : WithTop ℤ) < simpleCriticalDepth S.chain S.b :=
    lt_of_lt_of_le (by norm_num : (0 : WithTop ℤ) < ((1 : ℤ) : WithTop ℤ)) hd
  have hint := (hintertwining F V ψF hψ S h0 hS q 0 hn hd0 θ hθ).1
  have hint' := hint.trans (simpleCharacterIntertwiningFactor_mul_centralizer_zero hgroups S h0 hS q)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨d, η, hirr, hη⟩ := exists_irreducible_scalar hχ
    let : η.IsIrreducible := hirr
    have : Nontrivial (Fin d → ℂ) := IsSimpleModule.nontrivial ℂ[J] η.asModule
    have hscalar (a : H) : η (Subgroup.inclusion hHJ a) = (θ a : ℂ) • LinearMap.id := hη (e.symm a)
    refine ⟨d, η, inferInstance, ⟨S.chain, k, fun g hg => ?_⟩, hirr,
      contains_of_scalar hHJ θ η hscalar⟩
    obtain ⟨h, hθ⟩ := hdeep g hg
    change η (Subgroup.inclusion hHJ (⟨(g : (Module.End F V)ˣ), h⟩ : H)) = 1
    rw [hscalar, hθ, Units.val_one, one_smul, Module.End.one_eq_id]
  · intro W₁ _ _ W₂ _ _ η₁ η₂ hη₁ hη₂
    obtain ⟨hfd₁, -, hirr₁, hcontains₁⟩ := hη₁
    obtain ⟨hfd₂, -, hirr₂, hcontains₂⟩ := hη₂
    let : FiniteDimensional ℂ W₁ := hfd₁
    let : FiniteDimensional ℂ W₂ := hfd₂
    let : η₁.IsIrreducible := hirr₁
    let : η₂.IsIrreducible := hirr₂
    have : Nontrivial W₁ := IsSimpleModule.nontrivial ℂ[J] η₁.asModule
    have : Nontrivial W₂ := IsSimpleModule.nontrivial ℂ[J] η₂.asModule
    have hs₁ := scalar_of_normalized_contains hHJ θ hχ η₁ hirr₁ hcontains₁
    have hs₂ := scalar_of_normalized_contains hHJ θ hχ η₂ hirr₂ hcontains₂
    have htr := trace_zero_off_scalar_subgroup hHJ θ B hp hrad η₂ hs₂
    have hfin := finrank_intertwiningMap_mul_relIndex hHJ θ η₁ η₂ N hNK
      (scalar_kernel_contains hHJ θ η₁ hs₁ hNdata)
      (scalar_kernel_contains hHJ θ η₂ hs₂ hNdata) hs₁ hs₂ htr
    have hd₁ : 0 < Module.finrank ℂ W₁ := Module.finrank_pos
    have hd₂ : 0 < Module.finrank ℂ W₂ := Module.finrank_pos
    have hf : 0 < Module.finrank ℂ (η₁.IntertwiningMap η₂) := by
      by_contra! h
      rw [Nat.eq_zero_of_le_zero h, zero_mul] at hfin
      exact (Nat.mul_ne_zero hd₂.ne' hd₁.ne') hfin.symm
    have : Nontrivial (η₁.IntertwiningMap η₂) := Module.nontrivial_of_finrank_pos hf
    obtain ⟨f, hf⟩ := exists_ne (0 : η₁.IntertwiningMap η₂)
    exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩
  · intro W _ _ η hη
    obtain ⟨hfd, -, hirr, hcontains⟩ := hη
    let : FiniteDimensional ℂ W := hfd
    let : η.IsIrreducible := hirr
    have : Nontrivial W := IsSimpleModule.nontrivial ℂ[J] η.asModule
    have hs := scalar_of_normalized_contains hHJ θ hχ η hirr hcontains
    have hker := scalar_kernel_contains hHJ θ η hs hNdata
    have htr := trace_zero_off_scalar_subgroup hHJ θ B hp hrad η hs
    have hfin := finrank_intertwiningMap_mul_relIndex hHJ θ η η N hNK hker hker hs hs htr
    rw [Representation.IsIrreducible.finrank_intertwiningMap_self, one_mul, ← pow_two] at hfin
    refine ⟨hs, hfin.symm, ?_⟩
    exact (selfIntertwining_eq hHJ θ η N hNK hker hs htr).trans hint'

end Langlands.BushnellKutzko
