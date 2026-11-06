/-
Adapted from the published Anthropic FLT monomial proof at upstream commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Copyright 2026 Anthropic, PBC,
Apache License 2.0. See licenses/Anthropic-FLT/LICENSE, NOTICE and ATTRIBUTION.md.
Modified by Worker 1787: retain the initial normal abelian subgroup in every
inducing subgroup, and prove the containment invariant through the induction.
-/
import Langlands.AnthropicFLT.P2M.Sol.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem

noncomputable section
open scoped Classical
open Module
open P2MW.S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem.MonomialProof

namespace Langlands.FiniteRep.DegreeZeroMonomial

set_option maxHeartbeats 4000000

private def val {K : Type} [Group K] [Fintype K] (e : Entry K) : K → ℂ :=
  ClassFunction.induced e.1 (extChar e.1 e.2)

/-- An occurring weight is fixed by every element of the weight subgroup. -/
theorem weight_fixed {K : Type} [Group K] [Fintype K]
    {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (σ : Representation ℂ K W) (B : Subgroup K) [B.Normal]
    (χ : B → ℂ) (hχ : wt σ B χ ≠ ⊥) (b : K) (hb : b ∈ B) : b • χ = χ := by
  funext a
  rw [smul_weight_apply]
  have h : weightHom σ B hχ ((⟨b, hb⟩ : B)⁻¹ * a * ⟨b, hb⟩) =
      weightHom σ B hχ a := by simp [mul_comm]
  exact congrArg (fun z : ℂˣ => (z : ℂ)) h

def Monomial {K : Type} [Group K] [Fintype K] (A : Subgroup K) (W : Type) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ K W) : Prop :=
  ∃ l : List (Entry K), (∀ e ∈ l, A ≤ e.1) ∧
    ∀ g : K, LinearMap.trace ℂ W (σ g) = lsum l g

variable {K : Type} [Group K] [Fintype K]
variable {W : Type} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
variable (σ : Representation ℂ K W)

theorem monomial_of_finrank_zero (A : Subgroup K) (h : Module.finrank ℂ W = 0) : Monomial A W σ := by
  haveI : Subsingleton W := Module.finrank_zero_iff.1 h
  refine ⟨[], by simp, fun g => ?_⟩
  have : σ g = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
  rw [this, map_zero, lsum_nil, Pi.zero_apply]

theorem monomial_of_comm (A : Subgroup K) (hab : ∀ x y : K, σ x * σ y = σ y * σ x) : Monomial A W σ := by
  let T : Subgroup K := ⊤
  have hcommT : ∀ a b : T, σ a * σ b = σ b * σ a := fun a b => hab a b
  have hint := isInternal_wt σ T hcommT
  have hfin := finite_wt σ T hint
  set S := hfin.toFinset with hS
  have hSmem : ∀ χ, χ ∈ S ↔ wt σ T χ ≠ ⊥ := fun χ => by simp [hS]

  let ent : (T → ℂ) → Entry K := fun χ =>
    if hχ : wt σ T χ ≠ ⊥ then ⟨⊤, weightHom σ T hχ⟩ else ⟨⊤, 1⟩
  have hval : ∀ χ, ∀ hχ : wt σ T χ ≠ ⊥, ∀ g : K, val (ent χ) g = χ ⟨g, Subgroup.mem_top g⟩ := by
    intro χ hχ g
    have hent : ent χ = ⟨⊤, weightHom σ T hχ⟩ := by simp only [ent, dite_eq_left hχ]
    rw [hent, val]
    have hcf : ∀ x y : K, extChar ⊤ (weightHom σ T hχ) (x⁻¹ * y * x) =
        extChar ⊤ (weightHom σ T hχ) y := by
      intro x y
      simp only [extChar, dite_eq_left (Subgroup.mem_top _), weightHom_apply]
      have e : (⟨x⁻¹ * y * x, Subgroup.mem_top _⟩ : T) =
          (⟨x, Subgroup.mem_top _⟩ : T)⁻¹ * ⟨y, Subgroup.mem_top _⟩ * ⟨x, Subgroup.mem_top _⟩ := rfl
      rw [e, weight_mul σ T hχ, weight_mul σ T hχ, mul_comm (χ _) (χ ⟨y, _⟩), mul_assoc,
        ← weight_mul σ T hχ, inv_mul_cancel, weight_one σ T hχ, mul_one]
    change ClassFunction.induced ⊤ (extChar ⊤ (weightHom σ T hχ)) g = _
    rw [ClassFunction.induced_top_of_conj_invariant _ hcf]
    simp only [extChar, dite_eq_left (Subgroup.mem_top _), weightHom_apply]

  have htr : ∀ g : K, LinearMap.trace ℂ W (σ g) =
      ∑ χ ∈ S, χ ⟨g, Subgroup.mem_top g⟩ * (Module.finrank ℂ (wt σ T χ) : ℂ) := by
    intro g
    have hf : ∀ χ : T → ℂ, Set.MapsTo (σ g) (wt σ T χ) (wt σ T χ) :=
      fun χ => mapsTo_wt_of_comm σ T χ (σ g) (fun a => hab g a)
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin hf]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hres : (σ g).restrict (hf χ) = χ ⟨g, Subgroup.mem_top g⟩ • LinearMap.id := by
      apply LinearMap.ext; intro v; apply Subtype.ext
      simp only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
        Submodule.coe_smul]
      exact (mem_wt σ T χ v).1 v.2 ⟨g, Subgroup.mem_top g⟩
    rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul]

  refine ⟨(S.toList.map fun χ => List.replicate (Module.finrank ℂ (wt σ T χ)) (ent χ)).flatten,
    ?_, fun g => ?_⟩
  · intro e he
    obtain ⟨l, hl, he⟩ := List.mem_flatten.mp he
    obtain ⟨χ, _, rfl⟩ := List.mem_map.mp hl
    have heq : e = ent χ := (List.eq_of_mem_replicate he)
    rw [heq]
    dsimp only [ent]
    split <;> exact le_top
  rw [htr g, lsum_flatten_replicate, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  change χ ⟨g, _⟩ * _ = _ * val (ent χ) g
  rw [hval χ ((hSmem χ).1 hχ) g, mul_comm]

theorem monomial_of_isCompl (A : Subgroup K) (P₁ P₂ : Submodule ℂ W) (hc : IsCompl P₁ P₂)
    (h₁ : ∀ k : K, P₁ ≤ P₁.comap (σ k)) (h₂ : ∀ k : K, P₂ ≤ P₂.comap (σ k))
    (m₁ : Monomial A P₁ (σ.subrepresentation P₁ h₁))
    (m₂ : Monomial A P₂ (σ.subrepresentation P₂ h₂)) : Monomial A W σ := by
  obtain ⟨l₁, hA₁, hl₁⟩ := m₁
  obtain ⟨l₂, hA₂, hl₂⟩ := m₂
  refine ⟨l₁ ++ l₂, ?_, fun g => ?_⟩
  · intro e he
    exact (List.mem_append.mp he).elim (hA₁ e) (hA₂ e)
  rw [lsum_append, Pi.add_apply, ← hl₁, ← hl₂]
  set e := Submodule.prodEquivOfIsCompl P₁ P₂ hc with he
  have : σ g = e.conj (((σ.subrepresentation P₁ h₁) g).prodMap ((σ.subrepresentation P₂ h₂) g)) := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    rw [LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, he,
      Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
    rfl
  rw [this, LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem monomial_of_transitive (A : Subgroup K) (B : Subgroup K) [B.Normal]
    (hcommB : ∀ a b : B, σ a * σ b = σ b * σ a)
    (S : Finset (B → ℂ)) (hS : ∀ χ, χ ∈ S ↔ wt σ B χ ≠ ⊥) (χ₁ : B → ℂ) (hχ₁ : χ₁ ∈ S)
    (htrans : ∀ χ ∈ S, χ ∈ MulAction.orbit K χ₁)
    (H₁ : Subgroup K) (hH₁ : ∀ h : K, h ∈ H₁ ↔ h • χ₁ = χ₁)
    (hAH : A ≤ H₁)
    (m : Monomial (A.subgroupOf H₁) (wt σ B χ₁) (stabRep σ B χ₁ H₁ (fun h hh => (hH₁ h).1 hh))) :
    Monomial A W σ := by
  obtain ⟨l', hAl', hl'⟩ := m
  refine ⟨l'.map (lift H₁), ?_, fun g => ?_⟩
  · intro e he a ha
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
    exact ⟨⟨a, hAH ha⟩, hAl' d hd ha, rfl⟩
  rw [← induced_lsum_eq]

  suffices key : ∀ Φ : K → ℂ,
      (∀ (y : K) (hy : y ∈ H₁), Φ y =
        LinearMap.trace ℂ _ (stabRep σ B χ₁ H₁ (fun h hh => (hH₁ h).1 hh) ⟨y, hy⟩)) →
      LinearMap.trace ℂ W (σ g) = ClassFunction.induced H₁ Φ g by
    apply key
    intro y hy
    beta_reduce
    rw [dite_eq_left hy]
    exact (hl' ⟨y, hy⟩).symm
  intro Φ hΦ
  rw [ClassFunction.induced_apply]
  have hint := isInternal_wt σ B hcommB
  have horbS : ∀ x : K, x • χ₁ ∈ S := fun x =>
    (hS _).2 ((wt_smul_ne_bot_iff σ B x χ₁).2 ((hS _).1 hχ₁))

  let D : (B → ℂ) → ℂ := fun χ => if hχ : g • χ = χ then
    LinearMap.trace ℂ (wt σ B χ) ((σ g).restrict (mapsTo_of_eq (mapsTo_smul σ B g χ) hχ)) else 0
  have hD : LinearMap.trace ℂ W (σ g) = ∑ χ ∈ S, D χ :=
    trace_eq_sum_fixed hint S (fun χ h => (hS χ).2 h) (fun χ => g • χ) (σ g) (mapsTo_smul σ B g)

  have hstep1 : ∀ x : K, (if x⁻¹ * g * x ∈ H₁ then Φ (x⁻¹ * g * x) else 0) = D (x • χ₁) := by
    intro x
    have hiff : x⁻¹ * g * x ∈ H₁ ↔ g • (x • χ₁) = x • χ₁ := by
      rw [hH₁, mul_smul, mul_smul, inv_smul_eq_iff]
    by_cases hx : x⁻¹ * g * x ∈ H₁
    · rw [ite_eq_left hx, hΦ _ hx]
      simp only [D, dite_eq_left (hiff.1 hx)]
      rw [stabRep_apply]
      exact (trace_restrict_conj σ B x g χ₁ _ _).symm
    · rw [ite_eq_right hx]
      simp only [D, dite_eq_right (mt hiff.2 hx)]

  have hstep2 : ∑ x : K, D (x • χ₁) = (Nat.card H₁ : ℂ) * ∑ χ ∈ S, D χ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := fun x : K => x • χ₁)
      (fun x _ => horbS x) (fun x => D (x • χ₁)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have : ∑ x ∈ Finset.univ.filter (fun x : K => x • χ₁ = χ), D (x • χ₁) =
        ∑ x ∈ Finset.univ.filter (fun x : K => x • χ₁ = χ), D χ := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [this, Finset.sum_const, nsmul_eq_mul]
    congr 1
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 (htrans χ hχ)
    have hcard : Nat.card {x : K // x • χ₁ = k • χ₁} =
        (Finset.univ.filter fun x : K => x • χ₁ = k • χ₁).card := Nat.subtype_card _ (by simp)
    have hcard2 : Nat.card {x : K // x • χ₁ = k • χ₁} = Nat.card H₁ := by
      apply Nat.card_congr
      exact
        { toFun := fun x => ⟨k⁻¹ * x.1, by
            rw [hH₁, mul_smul, x.2, inv_smul_smul]⟩
          invFun := fun h => ⟨k * h.1, by
            rw [mul_smul, (hH₁ _).1 h.2]⟩
          left_inv := fun x => by simp
          right_inv := fun h => by simp }
    rw [← hcard2, hcard]

  rw [Finset.sum_congr rfl (fun x _ => hstep1 x), hstep2, hD, ← mul_assoc]
  have hne : (Nat.card H₁ : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [inv_mul_cancel₀ hne, one_mul]

theorem engine {p : ℕ} (hp : p.Prime) : ∀ (m : ℕ) (K : Type) [Group K] [Fintype K]
    (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ K W),
    Fintype.card K + Module.finrank ℂ W ≤ m →
    ∀ (A : Subgroup K) [A.Normal], (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ k : K, ∃ n : ℕ, k ^ p ^ n ∈ A) → Monomial A W σ := by
  intro m
  induction m with
  | zero =>
    intro K _ _ W _ _ _ σ hm
    exfalso
    have := Fintype.card_pos (α := K)
    omega
  | succ m ih =>
    intro K _ _ W _ _ _ σ hm A hAn hAcomm hpow
    by_cases hW : Module.finrank ℂ W = 0
    · exact monomial_of_finrank_zero σ A hW
    by_cases hab : ∀ x y : K, σ x * σ y = σ y * σ x
    · exact monomial_of_comm σ A hab

    push Not at hab
    obtain ⟨x, y, hxy⟩ := hab
    let f := σ.toHomUnits
    have hf : ∀ k, ((f k : (W →ₗ[ℂ] W)ˣ) : W →ₗ[ℂ] W) = σ k := fun k => rfl
    obtain ⟨B, hBn, hAB, hBcomm, b₀, hb₀, k₀, hbk⟩ := exists_normal_comm_not_central hp A hpow f
      (fun a ha b hb => Units.ext (by
        simp only [Units.val_mul, hf, ← map_mul, hAcomm a ha b hb]))
      ⟨x, y, fun h => hxy (by simpa [hf] using congrArg Units.val h)⟩
    haveI := hBn
    have hcommB : ∀ a b : B, σ a * σ b = σ b * σ a := fun a b => by
      simpa [hf] using congrArg Units.val (hBcomm a a.2 b b.2)
    have hbk' : σ b₀ * σ k₀ ≠ σ k₀ * σ b₀ := fun h => hbk (Units.ext (by simpa [hf] using h))
    have hint := isInternal_wt σ B hcommB
    have hfin := finite_wt σ B hint
    set S := hfin.toFinset with hS
    have hSmem : ∀ χ, χ ∈ S ↔ wt σ B χ ≠ ⊥ := fun χ => by simp [hS]

    haveI hW' : Nontrivial W := Module.finrank_pos_iff.1 (Nat.pos_of_ne_zero hW)
    obtain ⟨χ₁, hχ₁⟩ : ∃ χ₁, χ₁ ∈ S := by
      by_contra hnone
      push Not at hnone
      have htop := hint.submodule_iSup_eq_top
      have : (⨆ χ, wt σ B χ) = ⊥ := by
        apply iSup_eq_bot.2
        intro χ
        by_contra hne
        exact hnone χ ((hSmem χ).2 hne)
      rw [this] at htop
      exact bot_ne_top htop
    obtain ⟨χ₂, hχ₂, hne⟩ : ∃ χ₂ ∈ S, χ₂ ≠ χ₁ := by
      by_contra hall
      push Not at hall
      have htop : wt σ B χ₁ = ⊤ := by
        rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
        apply iSup_le
        intro χ
        by_cases hχ : wt σ B χ = ⊥
        · rw [hχ]; exact bot_le
        · rw [hall χ ((hSmem χ).2 hχ)]
      apply hbk'
      apply LinearMap.ext
      intro v
      have hv : ∀ w : W, σ b₀ w = χ₁ ⟨b₀, hb₀⟩ • w := fun w =>
        (mem_wt σ B χ₁ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩
      simp only [Module.End.mul_apply, hv, map_smul]
    by_cases htr : ∀ χ ∈ S, χ ∈ MulAction.orbit K χ₁
    ·
      obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Subgroup K, ∀ h : K, h ∈ H₁ ↔ h • χ₁ = χ₁ :=
        ⟨MulAction.stabilizer K χ₁, fun h => MulAction.mem_stabilizer_iff⟩
      have hH₁top : H₁ ≠ ⊤ := by
        intro htopH
        obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 (htr χ₂ hχ₂)
        apply hne
        have : k ∈ H₁ := htopH ▸ Subgroup.mem_top k
        exact (hH₁ k).1 this
      have hcard : Fintype.card H₁ < Fintype.card K := by
        have h1 := Subgroup.card_mul_index H₁
        have h2 := Subgroup.one_lt_index_of_ne_top hH₁top
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
        have h3 := Fintype.card_pos (α := H₁)
        nlinarith
      have hdim : Module.finrank ℂ (wt σ B χ₁) ≤ Module.finrank ℂ W := Submodule.finrank_le _
      have hAH : A ≤ H₁ := by
        intro a ha
        rw [hH₁]
        exact weight_fixed σ B χ₁ ((hSmem χ₁).1 hχ₁) a (hAB ha)
      apply monomial_of_transitive σ A B hcommB S hSmem χ₁ hχ₁ htr H₁ hH₁ hAH
      apply ih (↥H₁) (wt σ B χ₁) (stabRep σ B χ₁ H₁ fun h hh => (hH₁ h).1 hh) (by omega)
        (A.subgroupOf H₁)
      · intro a ha b hb
        apply Subtype.ext
        exact hAcomm a ha b hb
      · intro h
        obtain ⟨n, hn⟩ := hpow h
        exact ⟨n, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hn⟩
    ·
      push Not at htr
      obtain ⟨χ₃, hχ₃, hno⟩ := htr
      let O := MulAction.orbit K χ₁
      let P₁ : Submodule ℂ W := ⨆ χ ∈ O, wt σ B χ
      let P₂ : Submodule ℂ W := ⨆ χ ∈ Oᶜ, wt σ B χ
      have hc : IsCompl P₁ P₂ := by
        constructor
        · exact hint.submodule_iSupIndep.disjoint_biSup_biSup disjoint_compl_right
        · rw [codisjoint_iff]
          have : P₁ ⊔ P₂ = ⨆ χ, wt σ B χ := by
            change (⨆ χ ∈ O, wt σ B χ) ⊔ (⨆ χ ∈ Oᶜ, wt σ B χ) = _
            rw [← iSup_union, Set.union_compl_self, iSup_univ]
          rw [this, hint.submodule_iSup_eq_top]
      have hstab : ∀ (T : Set (B → ℂ)), (∀ k : K, ∀ χ ∈ T, k • χ ∈ T) →
          ∀ k : K, (⨆ χ ∈ T, wt σ B χ) ≤ (⨆ χ ∈ T, wt σ B χ).comap (σ k) := by
        intro T hT k
        rw [← Submodule.map_le_iff_le_comap, Submodule.map_iSup]
        apply iSup_le
        intro χ
        rw [Submodule.map_iSup]
        apply iSup_le
        intro hχ
        refine le_trans ?_ (le_biSup (fun χ => wt σ B χ) (hT k χ hχ))
        rintro _ ⟨v, hv, rfl⟩
        exact mapsTo_smul σ B k χ hv
      have hO : ∀ k : K, ∀ χ ∈ O, k • χ ∈ O := by
        intro k χ hχ
        obtain ⟨j, rfl⟩ := MulAction.mem_orbit_iff.1 hχ
        exact MulAction.mem_orbit_iff.2 ⟨k * j, mul_smul k j χ₁⟩
      have hOc : ∀ k : K, ∀ χ ∈ Oᶜ, k • χ ∈ Oᶜ := by
        intro k χ hχ hk
        apply hχ
        have := hO k⁻¹ _ hk
        rwa [inv_smul_smul] at this
      have h₁ := hstab O hO
      have h₂ := hstab Oᶜ hOc
      have hP₁ : P₁ ≠ ⊥ := by
        intro hbot
        apply (hSmem χ₁).1 hχ₁
        rw [eq_bot_iff, ← hbot]
        exact le_biSup (fun χ => wt σ B χ) (MulAction.mem_orbit_self χ₁)
      have hP₂ : P₂ ≠ ⊥ := by
        intro hbot
        apply (hSmem χ₃).1 hχ₃
        rw [eq_bot_iff, ← hbot]
        exact le_biSup (fun χ => wt σ B χ) hno
      have hsum := Submodule.finrank_add_eq_of_isCompl hc
      have hp1 : 0 < Module.finrank ℂ P₁ :=
        Nat.pos_of_ne_zero (fun h => hP₁ (Submodule.finrank_eq_zero.1 h))
      have hp2 : 0 < Module.finrank ℂ P₂ :=
        Nat.pos_of_ne_zero (fun h => hP₂ (Submodule.finrank_eq_zero.1 h))
      apply monomial_of_isCompl σ A P₁ P₂ hc h₁ h₂
      · exact ih K P₁ (σ.subrepresentation P₁ h₁) (by omega) A hAcomm hpow
      · exact ih K P₂ (σ.subrepresentation P₂ h₂) (by omega) A hAcomm hpow


end Langlands.FiniteRep.DegreeZeroMonomial
