import Langlands.BushnellKutzko.SimpleStratumConjugacyRelative
import Langlands.BushnellKutzko.SimpleStratumCorestrictionCongruenceProof
import Langlands.BushnellKutzko.CriticalDerivedStratumProof
import Langlands.BushnellKutzko.PureStratumApproximationConjugation
import Langlands.BushnellKutzko.PureStratumSimpleApproximationStatement

/-! # The induction step in the proof of BK93 (2.6.1)

Let `β₁, β₂` be elements of pure strata on the same chain with the same `n`, congruent
modulo `𝔓^{−t}`, whose cosets modulo `𝔓^{1−t}` are intertwined. Assuming the existence of
simple approximations (BK93 (2.4.1)(i)), a unit of `𝔄` conjugates `β₂` into
`β₁ + 𝔓^{1−t}`. This is the induction step of the proof of BK93 (2.6.1), printed
pp. 84–86.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SimpleConjugacy

open CriticalDerived

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  (𝓛 : LatticeChain 𝒪[F] F V)

local notation "P" => 𝓛.endFiltration
local notation "A" => Module.End F V

/-- `β` is the element of a pure stratum on `𝓛` whose first integer is `n`. Purity does not
depend on the level `r` of the stratum. -/
def IsPureElement (n : ℤ) (β : A) : Prop :=
  ∃ S : Stratum 𝒪[F] F V, S.chain = 𝓛 ∧ S.n = n ∧ S.b = β ∧ S.IsPure

variable {𝓛}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem IsPureElement.valuation_ge {n : ℤ} {β : A} (h : IsPureElement 𝓛 n β) :
    (-n : WithTop ℤ) ≤ 𝓛.valuation β := by
  obtain ⟨S, rfl, rfl, rfl, -⟩ := h
  exact S.valuation_ge

/-- The stratum `[𝓛,n,r,β]` for a pure element `β`. -/
def IsPureElement.stratum {n : ℤ} {β : A} (h : IsPureElement 𝓛 n β) (r : ℤ) (hr : r < n) :
    Stratum 𝒪[F] F V :=
  ⟨𝓛, n, r, β, hr, h.valuation_ge⟩

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem IsPureElement.isPure_stratum {n : ℤ} {β : A} (h : IsPureElement 𝓛 n β) (r : ℤ)
    (hr : r < n) : (h.stratum r hr).IsPure := by
  obtain ⟨S, rfl, rfl, rfl, hS⟩ := h
  exact hS

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem isPureElement_of_isPure {S : Stratum 𝒪[F] F V} (hS : S.IsPure) :
    IsPureElement S.chain S.n S.b :=
  ⟨S, rfl, rfl, rfl, hS⟩

/-- A simple approximation in element form (BK93 (2.4.1)(i)). -/
theorem exists_simple_approx (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    [FiniteDimensional F V] {n r : ℤ} (hr : r < n) {β : A} (hβ : IsPureElement 𝓛 n β) :
    ∃ γ : A, IsPureElement 𝓛 n γ ∧ criticalExponent 𝓛 γ < ((-r : ℤ) : WithBot ℤ) ∧
      β - γ ∈ P (-r) := by
  obtain ⟨T, hTc, hTn, hTr, hTs, hST, -, -⟩ := hApprox F V _ (hβ.isPure_stratum r hr)
  refine ⟨T.b, ⟨T, hTc, hTn, rfl, hTs.1⟩, ?_, Stratum.sub_mem_of_equivalent hST⟩
  have h := hTs.2
  rw [hTc, hTr] at h
  exact h

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in
/-- **The induction step of the proof of BK93 (2.6.1)**, printed pp. 84–86. -/
theorem exists_conj_step (hApprox : PureStratumSimpleApproximationStatement.{uF, uV})
    [FiniteDimensional F V] {n t : ℤ} (ht : t < n) {β₁ β₂ : A}
    (h₁ : IsPureElement 𝓛 n β₁) (h₂ : IsPureElement 𝓛 n β₂) (h12 : β₂ - β₁ ∈ P (-t))
    {g : Aˣ} {y : A} (hy : y - β₂ ∈ P (1 - t))
    (hgy : ((g⁻¹ : Aˣ) : A) * y * g - β₁ ∈ P (1 - t)) :
    ∃ u : Aˣ, Shifts 𝓛 0 u ∧ (u : A) * β₂ * ((u⁻¹ : Aˣ) : A) - β₁ ∈ P (1 - t) := by
  -- the simple approximation `[𝓛,n,t,γ]` of `[𝓛,n,t,β₁]`
  obtain ⟨γ, hγp, hγk, hγ₁⟩ := exists_simple_approx hApprox ht h₁
  let Γ : Stratum 𝒪[F] F V := ⟨𝓛, n, t, γ, ht, hγp.valuation_ge⟩
  have hΓ : Γ.IsSimple := ⟨hγp.isPure_stratum t ht, hγk⟩
  have hγ₂ : β₂ - γ ∈ P (-t) := by
    simpa only [sub_add_sub_cancel] using add_mem h12 hγ₁
  have hle : P (1 - t) ≤ P (-t) := 𝓛.endFiltration_antitone (by omega)
  -- the field `E = F[γ]`, a tame corestriction, and `E` as a local field
  obtain ⟨⟨hEf0, hEn⟩, -⟩ := hΓ.1
  have hEf : IsField (elementAlgebra γ) := hEf0
  let := hEf.toField
  have hEn' : ∀ a : (elementAlgebra γ)ˣ, subfieldUnits F (elementAlgebra γ) V a ∈ 𝓛.stabilizer :=
    hEn
  have : FiniteDimensional F (elementAlgebra γ) := 𝓛.finiteDimensional_subfield _
  obtain ⟨s⟩ := (tameCorestriction F V (elementAlgebra γ)).1
  have himage := (tameCorestriction F V (elementAlgebra γ)).2.2 s 𝓛 hEn'
  let := LocalField.FiniteExtension.normedField F (elementAlgebra γ)
  let := LocalField.FiniteExtension.valuativeRel F (elementAlgebra γ)
  have := LocalField.FiniteExtension.isLocalField F (elementAlgebra γ)
  have : IsScalarTower 𝒪[elementAlgebra γ] (elementAlgebra γ) V :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let C : LatticeChain 𝒪[elementAlgebra γ] (elementAlgebra γ) V :=
    (𝓛.extensionChain hEn').transfer (subfieldIntegerEquiv F (elementAlgebra γ)) (fun _ => rfl)
  have hlat : ∀ i, (C.lattice i : Set V) = 𝓛.lattice i := fun _ => rfl
  have hmemC {x : Module.End (elementAlgebra γ) V} {k : ℤ} :
      x ∈ C.endFiltration k ↔ x.restrictScalars F ∈ P k :=
    mem_endFiltration_restrictScalars hlat
  have hsP {x : A} {k : ℤ} (hx : x ∈ P k) : s x ∈ C.endFiltration k := by
    have hm : s x ∈ s '' (P k : Set A) := ⟨x, hx, rfl⟩
    rw [himage k] at hm
    exact hmemC.mpr hm
  -- the derived cosets are pure or null
  let sL := s.toLinearMap
  have hsL (x : A) : sL x = s x := rfl
  have hclass : ∀ β : A, IsPureElement 𝓛 n β → β - γ ∈ P (-t) →
      PureOrNull C t (s (β - γ)) := by
    intro β hβ hβγ
    obtain ⟨γi, hγip, hγik, hγi⟩ := exists_simple_approx hApprox (r := t - 1) (by omega) hβ
    have hγi' : β - γi ∈ P (1 - t) := by rwa [show -(t - 1) = 1 - t by ring] at hγi
    have hsplit : s (β - γ) - s (γi - γ) ∈ C.endFiltration (1 - t) := by
      have h := hsP hγi'
      rwa [show β - γi = (β - γ) - (γi - γ) by abel, ← hsL, map_sub] at h
    have hγiγ : γ - γi ∈ P (-t) := by
      rw [show γ - γi = (β - γi) - (β - γ) by abel]
      exact sub_mem (hle hγi') hβγ
    let Γi : Stratum 𝒪[F] F V := ⟨𝓛, n, t, γi, ht, hγip.valuation_ge⟩
    have hΓip : Γi.IsPure := hγip.isPure_stratum t ht
    have hequiv : Γ.Equivalent Γi := Stratum.equivalent_of_sub_mem rfl rfl hγiγ
    by_cases hk : criticalExponent 𝓛 γi < ((-t : ℤ) : WithBot ℤ)
    · -- the scalar case, BK93 (2.4.1)(ii)(c)
      obtain ⟨δ', hδ'⟩ := simpleStratumCorestrictionCongruence F V Γ Γi rfl rfl rfl hΓ
        ⟨hΓip, hk⟩ hequiv hEf s
      have h1 : s (γ - γi) - algebraMap (elementAlgebra γ) _ δ' ∈ C.endFiltration (1 - t) :=
        hmemC.mpr hδ'
      have h0 : s (γ - γi) ∈ C.endFiltration (-t) := hsP hγiγ
      apply pureOrNull_of_scalar C (-δ')
      · rw [map_neg]
        have hz : s (γi - γ) + s (γ - γi) = 0 := by
          rw [← hsL, ← hsL, ← map_add, show γi - γ + (γ - γi) = 0 by abel, map_zero]
        have h2 := sub_mem hsplit h1
        have heq : s (β - γ) -
            -algebraMap (elementAlgebra γ) (Module.End (elementAlgebra γ) V) δ' =
            (s (β - γ) - s (γi - γ)) -
              (s (γ - γi) - algebraMap (elementAlgebra γ) (Module.End (elementAlgebra γ) V) δ') +
              (s (γi - γ) + s (γ - γi)) := by abel
        rw [heq, hz, add_zero]
        exact h2
      · rw [map_neg]
        apply neg_mem
        have h2 := sub_mem h0 (C.endFiltration_antitone (by omega) h1)
        rwa [sub_sub_cancel] at h2
    · -- the critical case, BK93 (2.4.1)(iii)
      have hk' : criticalExponent 𝓛 γi = ((-t : ℤ) : WithBot ℤ) := by
        cases hc : criticalExponent 𝓛 γi with
        | bot => exact absurd (hc ▸ WithBot.bot_lt_coe (-t)) hk
        | coe k =>
          rw [hc] at hk hγik
          have h1 := WithBot.coe_lt_coe.mp hγik
          have h2 : ¬ k < -t := fun h => hk (WithBot.coe_lt_coe.mpr h)
          congr 1
          omega
      obtain ⟨D, Cs, hD, hCc, hCn, -, hDC, hCs⟩ :=
        criticalDerivedStratum F V Γi Γ hΓip hk' rfl rfl rfl hΓ
          (Stratum.equivalent_of_sub_mem rfl rfl (by
            simpa only [neg_sub] using neg_mem hγiγ)) hEf s
      obtain ⟨-, -, -, hDlat, hDn, hDr, hDb⟩ := hD
      have hCslat : ∀ i, (Cs.chain.lattice i : Set V) = C.lattice i := fun i => by
        rw [hCc]
        exact hDlat i
      have hDlat' : ∀ i, (D.chain.lattice i : Set V) = C.lattice i := fun i => hDlat i
      let Cs' : Stratum 𝒪[elementAlgebra γ] (elementAlgebra γ) V :=
        ⟨C, Cs.n, Cs.r, Cs.b, Cs.r_lt_n, by
          rw [← LatticeChain.valuation_congr hCslat]
          exact Cs.valuation_ge⟩
      have hCs'p : Cs'.IsPure := by
        obtain ⟨⟨hf, hnorm⟩, hv⟩ := hCs.1
        exact ⟨⟨hf, fun a => (LatticeChain.mem_stabilizer_congr hCslat).mp (hnorm a)⟩,
          (LatticeChain.valuation_congr hCslat Cs.b).symm.trans hv⟩
      have hn' : Cs.n = t := hCn.trans hDn
      have hDCs : D.b - Cs.b ∈ C.endFiltration (1 - t) := by
        have h := Stratum.sub_mem_of_equivalent hDC
        rw [hDr, show -(t - 1) = 1 - t by ring] at h
        exact (LatticeChain.mem_endFiltration_congr hDlat').mp h
      have hmem : s (β - γ) - Cs'.b ∈ C.endFiltration (1 - Cs'.n) := by
        change s (β - γ) - Cs.b ∈ C.endFiltration (1 - Cs.n)
        rw [hn', show s (β - γ) - Cs.b = (s (β - γ) - s (γi - γ)) + (D.b - Cs.b) by
          rw [hDb]; abel]
        exact add_mem hsplit hDCs
      have h := pureOrNull_of_isPure C Cs' rfl hCs'p hmem
      change PureOrNull C Cs.n _ at h
      rwa [hn'] at h
  -- the intertwining descends to the centralizer
  obtain ⟨δ, w, z₁, z₂, hδ, hw, hδw⟩ := exists_centralizer_intertwining Γ hΓ
    (b₁ := β₁ - γ) (b₂ := β₂ - γ) (y := y) (g := g) hγ₁ hγ₂
    (by show y - (γ + (β₂ - γ)) ∈ P (1 - t); rwa [add_sub_cancel])
    (by show ((g⁻¹ : Aˣ) : A) * y * g - (γ + (β₁ - γ)) ∈ P (1 - t); rwa [add_sub_cancel])
  -- the generator of `E` and the `E`-linearity of `δ`
  let βE : elementAlgebra γ := elementGenerator γ
  have hβE : subfieldEmbedding F (elementAlgebra γ) V βE = γ :=
    subfieldEmbedding_elementGenerator γ hEf
  have hβEtop : Algebra.adjoin F ({βE} : Set (elementAlgebra γ)) = ⊤ :=
    adjoin_elementGenerator γ
  have hδc : Commute (δ : A) (subfieldEmbedding F (elementAlgebra γ) V βE) := by
    rw [hβE]
    exact hδ.symm
  have hδic : Commute ((δ⁻¹ : Aˣ) : A) (subfieldEmbedding F (elementAlgebra γ) V βE) :=
    hδc.units_inv_left
  obtain ⟨D₁, hD₁⟩ := exists_restrictScalars_of_commute hβEtop hδc
  obtain ⟨D₂, hD₂⟩ := exists_restrictScalars_of_commute hβEtop hδic
  let δE : (Module.End (elementAlgebra γ) V)ˣ :=
    { val := D₁
      inv := D₂
      val_inv := by
        ext v
        have h1 := LinearMap.congr_fun hD₁ (D₂ v)
        have h2 := LinearMap.congr_fun hD₂ v
        change D₁ (D₂ v) = v
        change D₁ (D₂ v) = (δ : A) (D₂ v) at h1
        change D₂ v = ((δ⁻¹ : Aˣ) : A) v at h2
        rw [h1, h2, ← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
      inv_val := by
        ext v
        have h1 := LinearMap.congr_fun hD₂ (D₁ v)
        have h2 := LinearMap.congr_fun hD₁ v
        change D₂ (D₁ v) = v
        change D₂ (D₁ v) = ((δ⁻¹ : Aˣ) : A) (D₁ v) at h1
        change D₁ v = (δ : A) v at h2
        rw [h1, h2, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] }
  have hδEv : ((δE : Module.End (elementAlgebra γ) V)).restrictScalars F = δ := hD₁
  have hδEi : ((δE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) :
      Module.End (elementAlgebra γ) V).restrictScalars F = ((δ⁻¹ : Aˣ) : A) := hD₂
  -- the derived intertwining in `B`
  have hsadj (z : A) : s (γ * z - z * γ) = 0 := by
    have h := s.adjointMap_eq_zero βE z
    rwa [hβE, StratumEquivalence.adjointMap_apply] at h
  have hyE : s (w - γ) - s (β₂ - γ) ∈ C.endFiltration (1 - t) := by
    have h := hsP hw
    rw [show s (w - γ) - s (β₂ - γ) =
        s (w - (γ + (γ * z₁ - z₁ * γ) + (β₂ - γ))) + s (γ * z₁ - z₁ * γ) by
      rw [← hsL, ← hsL, ← hsL, ← hsL, ← map_sub, ← map_add]
      congr 1
      abel, hsadj, add_zero]
    exact h
  have hgyE : ((δE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) : Module.End (elementAlgebra γ) V) *
      s (w - γ) * δE - s (β₁ - γ) ∈ C.endFiltration (1 - t) := by
    have hconj : ((δE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) :
        Module.End (elementAlgebra γ) V) * s (w - γ) * δE =
        s (((δ⁻¹ : Aˣ) : A) * (w - γ) * δ) := by
      have hr (z : A) : s (z * ((δE : Module.End (elementAlgebra γ) V)).restrictScalars F) =
          s z * (δE : Module.End (elementAlgebra γ) V) := s.map_mul_right z _
      have hl (z : A) : s (((δE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) :
          Module.End (elementAlgebra γ) V).restrictScalars F * z) =
          ((δE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) : Module.End (elementAlgebra γ) V) * s z :=
        s.map_mul_left _ z
      rw [← hδEv, ← hδEi, hr, hl]
    have hγδ : ((δ⁻¹ : Aˣ) : A) * (w - γ) * δ = ((δ⁻¹ : Aˣ) : A) * w * δ - γ := by
      have hδ' : γ * (δ : A) = δ * γ := hδ
      rw [mul_sub, sub_mul, mul_assoc ((δ⁻¹ : Aˣ) : A) γ, hδ', ← mul_assoc, Units.inv_mul,
        one_mul]
    have h := hsP hδw
    rw [hconj, hγδ, show s (((δ⁻¹ : Aˣ) : A) * w * δ - γ) - s (β₁ - γ) =
        s (((δ⁻¹ : Aˣ) : A) * w * δ - (γ - (γ * z₂ - z₂ * γ) + (β₁ - γ))) -
          s (γ * z₂ - z₂ * γ) by
      rw [← hsL, ← hsL, ← hsL, ← hsL, ← map_sub, ← map_sub]
      congr 1
      abel, hsadj, sub_zero]
    exact h
  -- the depth-one result over `E`
  obtain ⟨xE, hxE, hxEc⟩ := exists_conj_of_pureOrNull C (hclass β₁ h₁ hγ₁)
    (hclass β₂ h₂ hγ₂) hyE hgyE
  let x : Aˣ := restrictUnit xE
  have hxv : (x : A) = (xE : Module.End (elementAlgebra γ) V).restrictScalars F := rfl
  have hxi : ((x⁻¹ : Aˣ) : A) =
      ((xE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) : Module.End (elementAlgebra γ) V).restrictScalars
        F := rfl
  have hx : Shifts 𝓛 0 x := ⟨hmemC.mp hxE.1, hmemC.mp hxE.2⟩
  have hxγ : (x : A) * γ * ((x⁻¹ : Aˣ) : A) = γ := by
    have hc := restrictScalars_commute (F := F) (xE : Module.End (elementAlgebra γ) V) βE
    rw [hβE, ← hxv] at hc
    rw [hc.eq, mul_assoc, Units.mul_inv, mul_one]
  -- the perturbation `b` and its corestriction
  set b : A := (x : A) * (β₂ - γ) * ((x⁻¹ : Aˣ) : A) - (β₁ - γ) with hbdef
  have hb : b ∈ P (-t) := sub_mem (conj_mem_of_shifts_zero 𝓛 hx hγ₂) hγ₁
  have hsb : (s b).restrictScalars F ∈ P (-(t - 1)) := by
    rw [show -(t - 1) = 1 - t by ring]
    apply hmemC.mp
    have hsx : s ((x : A) * (β₂ - γ) * ((x⁻¹ : Aˣ) : A)) =
        (xE : Module.End (elementAlgebra γ) V) * s (β₂ - γ) *
          ((xE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) : Module.End (elementAlgebra γ) V) := by
      have hr (z : A) : s (z * ((xE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) :
          Module.End (elementAlgebra γ) V).restrictScalars F) =
          s z * ((xE⁻¹ : (Module.End (elementAlgebra γ) V)ˣ) : Module.End (elementAlgebra γ) V) :=
        s.map_mul_right z _
      have hl (z : A) : s (((xE : Module.End (elementAlgebra γ) V)).restrictScalars F * z) =
          (xE : Module.End (elementAlgebra γ) V) * s z := s.map_mul_left _ z
      rw [hxv, hxi, hr, hl]
    rw [hbdef, ← hsL, map_sub, hsL, hsL, hsx]
    exact hxEc
  -- BK93 (2.2.1): conjugate by an element of `U¹(𝔄)`
  obtain ⟨g', p, hg'1, hg'i1, -, hp', -, hconj⟩ :=
    PureApproximation.exists_conj_sub_mem Γ hΓ hβE hβEtop s 𝓛 hEn' hb hsb
  have hP0 {z : A} (hz : z - 1 ∈ P 1) : z ∈ P 0 := by
    simpa only [sub_add_cancel] using add_mem (𝓛.endFiltration_antitone (by norm_num) hz)
      ((𝓛.mem_order_iff_mem_endFiltration).mp (one_mem 𝓛.order))
  have hg' : Shifts 𝓛 0 g' := ⟨hP0 hg'1, by simpa only [neg_zero] using hP0 hg'i1⟩
  refine ⟨g' * x, by simpa only [add_zero] using hg'.mul hx, ?_⟩
  have hp'' : p ∈ P (1 - t) := by rwa [show -(t - 1) = 1 - t by ring] at hp'
  have hthird : (g' : A) * (β₁ - γ) * ((g'⁻¹ : Aˣ) : A) - (β₁ - γ) ∈ P (1 - t) := by
    have hcomm : (g' : A) * (β₁ - γ) - (β₁ - γ) * g' ∈ P (1 - t) := by
      rw [show (g' : A) * (β₁ - γ) - (β₁ - γ) * g' =
        ((g' : A) - 1) * (β₁ - γ) - (β₁ - γ) * ((g' : A) - 1) by noncomm_ring]
      refine sub_mem ?_ ?_
      · simpa only [show 1 + -t = 1 - t by ring] using 𝓛.mul_mem_endFiltration hg'1 hγ₁
      · simpa only [show -t + 1 = 1 - t by ring] using 𝓛.mul_mem_endFiltration hγ₁ hg'1
    have h := 𝓛.mul_mem_endFiltration hcomm (hP0 hg'i1)
    rwa [add_zero, sub_mul, mul_assoc (β₁ - γ), Units.mul_inv, mul_one] at h
  have hkey : (↑(g' * x) : A) * β₂ * ↑(g' * x)⁻¹ - β₁ =
      ((g' : A) * (Γ.b + b) * ↑g'⁻¹ - (Γ.b + p)) + p +
        ((g' : A) * (β₁ - γ) * ↑g'⁻¹ - (β₁ - γ)) := by
    have h1 : (↑(g' * x) : A) * β₂ * ↑(g' * x)⁻¹ =
        (g' : A) * ((x : A) * β₂ * ↑x⁻¹) * ↑g'⁻¹ := by
      simp only [mul_inv_rev, Units.val_mul, mul_assoc]
    have h2 : (x : A) * β₂ * ↑x⁻¹ = γ + (x : A) * (β₂ - γ) * ↑x⁻¹ := by
      rw [show (x : A) * β₂ * ↑x⁻¹ = (x : A) * γ * ↑x⁻¹ + (x : A) * (β₂ - γ) * ↑x⁻¹ by
        noncomm_ring, hxγ]
    rw [h1, h2, hbdef]
    change _ = ((g' : A) * (γ + _) * ↑g'⁻¹ - (γ + p)) + p + _
    noncomm_ring
  rw [hkey]
  exact add_mem (add_mem hconj hp'') hthird

end Langlands.BushnellKutzko.SimpleConjugacy
