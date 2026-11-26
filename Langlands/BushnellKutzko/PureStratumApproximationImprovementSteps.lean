import Langlands.BushnellKutzko.PureStratumApproximationConjugation
import Langlands.BushnellKutzko.PureStratumApproximationCandidateBound
import Langlands.BushnellKutzko.PureStratumApproximationSeed

/-! # Moving a simple approximation to a second chain normalized by the same field

These are the two constructions in the proof of BK93 (2.4.5), printed pp. 67–69, and in its
final step, printed pp. 70–71. A simple stratum `[𝓛,n,r,γ]` approximating `β` is replaced by a
simple stratum on a second chain `𝓛'` normalized by `E = F[γ]`, whose lattices are each
sandwiched between consecutive lattices of `𝓛`:

* if the corestriction of `β − γ`, with the next step of `𝓛`, lies in a step of `𝓛'` of
  smaller normalized depth, conjugation alone gives the new approximation;
* if it lies in the coset of a simple stratum over `E` on `𝓛'` at the same normalized depth,
  conjugation and the refinement theorem (2.2.8) give approximations at that depth and one step
  below.
-/

noncomputable section

open ValuativeRel
open scoped Pointwise

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A generator of `E` acting on a chain normalized by `E` generates an algebra with
normalizing units. -/
theorem normalizingUnits_of_generated (𝓒 : LatticeChain 𝒪[F] F V)
    (h𝓒 : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓒.stabilizer) {βE : E}
    (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤) :
    NormalizingUnits 𝓒 (elementAlgebra (subfieldEmbedding F E V βE)) := by
  have h : elementAlgebra (subfieldEmbedding F E V βE) = (subfieldEmbedding F E V).range := by
    change Algebra.adjoin F ({subfieldEmbedding F E V βE} : Set (Module.End F V)) = _
    rw [← AlgHom.map_adjoin_singleton (subfieldEmbedding F E V) βE, hβE, Algebra.map_top]
  rw [h]
  intro x hx hx0
  obtain ⟨a, rfl⟩ := hx
  have ha : a ≠ 0 := fun h => hx0 (by simp [h])
  exact ⟨subfieldUnits F E V (Units.mk0 a ha), rfl, h𝓒 _⟩

omit [Module F V] [IsScalarTower F E V] in
/-- A filtration step over `𝔬_E` contains the elements of at least that valuation. -/
theorem mem_endFiltration_of_le_valuation_subfield [FiniteDimensional F E]
    (C : LatticeChain (subfieldIntegers F E) E V) {x : Module.End E V} {k : ℤ}
    (h : (k : WithTop ℤ) ≤ C.valuation x) : x ∈ C.endFiltration k := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  have := LocalField.FiniteExtension.isLocalField F E
  let C' := C.transfer (subfieldIntegerEquiv F E) (fun _ => rfl)
  have hl : ∀ i, (C.lattice i : Set V) = C'.lattice i := fun i => rfl
  rw [LatticeChain.valuation_congr hl] at h
  exact (LatticeChain.mem_endFiltration_congr hl).mpr (mem_endFiltration_of_le_valuation C' h)

omit [Module F V] [IsScalarTower F E V] in
/-- Membership in a filtration step over `𝔬_E` bounds the valuation below. -/
theorem le_valuation_of_mem_subfield [FiniteDimensional F E]
    (C : LatticeChain (subfieldIntegers F E) E V) {x : Module.End E V} {k : ℤ}
    (h : x ∈ C.endFiltration k) : (k : WithTop ℤ) ≤ C.valuation x := by
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  have := LocalField.FiniteExtension.isLocalField F E
  let C' := C.transfer (subfieldIntegerEquiv F E) (fun _ => rfl)
  have hl : ∀ i, (C.lattice i : Set V) = C'.lattice i := fun i => rfl
  rw [LatticeChain.valuation_congr hl]
  exact le_valuation_of_mem C' ((LatticeChain.mem_endFiltration_congr hl).mp h)

section Steps

variable [FiniteDimensional F E]

/-- The simple stratum `[𝓛',n',ρ,γ]` on a second normalized chain, at a normalized depth not
larger than that of a simple stratum `[𝓛,n,r,γ]` (BK93 (1.4.13), printed p. 39). -/
theorem exists_simple_of_normalized (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (𝓛' : LatticeChain 𝒪[F] F V) (hL' : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛'.stabilizer)
    {ρ : ℤ} (hρ : ρ * S.chain.period ≤ S.r * 𝓛'.period) :
    ∃ T : Stratum 𝒪[F] F V, T.chain = 𝓛' ∧ T.r = ρ ∧ T.b = S.b ∧ T.IsSimple ∧
      T.n * S.chain.period = S.n * 𝓛'.period := by
  have hE := normalized_of_generated S hS.1 hβES hβE
  have hβ0 : βE ≠ 0 := by
    intro h0
    have hv := hS.1.2
    rw [← hβES, h0, map_zero, LatticeChain.valuation_zero] at hv
    exact WithTop.top_ne_coe hv
  have hv : S.chain.valuation (subfieldEmbedding F E V βE) = ((-S.n : ℤ) : WithTop ℤ) := by
    rw [hβES, hS.1.2]
    rfl
  obtain ⟨n', hn', hnn'⟩ := exists_valuation_of_normalized S.chain hE 𝓛' hL' hβ0 hv
  have hpos : (0 : ℤ) < S.chain.period := by exact_mod_cast S.chain.period_pos
  have hpos' : (0 : ℤ) < 𝓛'.period := by exact_mod_cast 𝓛'.period_pos
  have hrn : ρ < n' := by
    have h1 : ρ * S.chain.period < n' * S.chain.period := by
      have := S.r_lt_n
      nlinarith
    exact lt_of_mul_lt_mul_right h1 hpos.le
  refine ⟨⟨𝓛', n', ρ, S.b, hrn, by rw [← hβES, hn']; exact le_rfl⟩, rfl, rfl, rfl, ?_, hnn'⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hN := normalizingUnits_of_generated 𝓛' hL' hβE
    rw [hβES] at hN
    exact isField_of_normalizingUnits 𝓛' hN
  · change 𝓛'.valuation S.b = ((-n' : ℤ) : WithTop ℤ)
    rw [← hβES, hn']
  · change criticalExponent 𝓛' S.b < ((-ρ : ℤ) : WithBot ℤ)
    have hk : criticalExponent S.chain (subfieldEmbedding F E V βE) <
        ((-S.r : ℤ) : WithBot ℤ) := by
      rw [hβES]
      exact hS.2
    rw [← hβES]
    exact criticalExponent_lt_of_normalized S.chain 𝓛' hE hL' hβE hk hρ

/-- **The non-fundamental case of BK93 (2.4.5)**, printed pp. 67–68. -/
theorem exists_improvement_of_le (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) {β : Module.End F V}
    (hb : β - S.b ∈ S.chain.endFiltration (-S.r))
    (𝓛' : LatticeChain 𝒪[F] F V) (hL' : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛'.stabilizer)
    (hsw : ∀ i, ∃ q, S.chain.lattice (q + 1) ≤ 𝓛'.lattice i ∧ 𝓛'.lattice i ≤ S.chain.lattice q)
    {ρ : ℤ} (hρ : ρ * S.chain.period < S.r * 𝓛'.period)
    (hsb : (s (β - S.b)).restrictScalars F ∈ 𝓛'.endFiltration (-ρ))
    (hQ : ∀ y : Module.End E V, y.restrictScalars F ∈ S.chain.endFiltration (1 - S.r) →
      y.restrictScalars F ∈ 𝓛'.endFiltration (-ρ)) :
    ∃ T : Stratum 𝒪[F] F V, T.chain = 𝓛' ∧ T.r = ρ ∧ T.IsSimple ∧ β ∈ T.coset ∧
      elementRamificationIndex F T.b = elementRamificationIndex F S.b ∧
      elementResidueDegree F T.b = elementResidueDegree F S.b := by
  have hE := normalized_of_generated S hS.1 hβES hβE
  obtain ⟨g, p, hg1, hginv, -, hp', -, hconj⟩ :=
    exists_conj_sub_mem S hS hβES hβE s 𝓛' hL' hb hsb
  have hP := endFiltration_le_of_restrict_le S.chain 𝓛' hE hL' hQ
  obtain ⟨T₀, hT₀c, hT₀r, hT₀b, hT₀, -⟩ := exists_simple_of_normalized S hS hβES hβE 𝓛' hL' hρ.le
  have hg : (g : Module.End F V) ∈ 𝓛'.endFiltration 0 := by
    have h := one_add_mem_order_of_sandwiched S.chain 𝓛' hsw hg1
    rwa [add_sub_cancel] at h
  have hg' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ 𝓛'.endFiltration 0 := by
    have h := one_add_mem_order_of_sandwiched S.chain 𝓛' hsw hginv
    rwa [add_sub_cancel] at h
  have hsum : S.b + (β - S.b) = β := by abel
  rw [hsum] at hconj
  have hmem : (g : Module.End F V) * β * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) - S.b ∈
      𝓛'.endFiltration (-ρ) := by
    have h := add_mem (hP hconj) hp'
    rwa [sub_add_eq_sub_sub, sub_add_cancel] at h
  subst hT₀c
  refine ⟨conjStratum T₀ g hg hg', rfl, hT₀r, isSimple_conjStratum T₀ g hg hg' hT₀, ?_, ?_⟩
  · change β - conjAlgHom g T₀.b ∈ T₀.chain.endFiltration (-T₀.r)
    have heq : β - conjAlgHom g T₀.b = conjAlgHom g
        ((g : Module.End F V) * β * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) - S.b) := by
      rw [hT₀b, map_sub]
      simp [conjAlgHom_apply, mul_assoc]
    rw [heq, hT₀r]
    exact (mem_endFiltration_conj_iff T₀.chain hg hg').mpr hmem
  · have hN : NormalizingUnits T₀.chain (elementAlgebra T₀.b) := by
      rw [hT₀b, ← hβES]
      exact normalizingUnits_of_generated T₀.chain hL' hβE
    have h := elementInvariants_conj T₀.chain hg hg' T₀.b hN
    change elementRamificationIndex F (conjAlgHom g T₀.b) = _ ∧
      elementResidueDegree F (conjAlgHom g T₀.b) = _
    rw [hT₀b] at h ⊢
    exact h

/-- **The refinement case of BK93 (2.4.5)**, printed p. 69, and the construction of its final
step, printed pp. 70–71: if the corestriction of `β − γ` lies in the coset of a simple stratum
`[𝓛'_E,ρ,ρ−1,c]` over `E` at the same normalized depth, then `β` is approximated on `𝓛'` by
conjugates of `[𝓛',n',ρ,γ]` and of a simple refinement `[𝓛',n',ρ−1,γ']` with
`F[γ']` having the invariants of `F[γ,c]` and `k₀(γ') = max(k₀(γ),k₀(c))`. -/
theorem exists_refinement_of_coset (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) {β : Module.End F V}
    (hb : β - S.b ∈ S.chain.endFiltration (-S.r))
    (𝓛' : LatticeChain 𝒪[F] F V) (hL' : ∀ a : Eˣ, subfieldUnits F E V a ∈ 𝓛'.stabilizer)
    (hsw : ∀ i, ∃ q, S.chain.lattice (q + 1) ≤ 𝓛'.lattice i ∧ 𝓛'.lattice i ≤ S.chain.lattice q)
    {ρ : ℤ} (hρ : ρ * S.chain.period = S.r * 𝓛'.period)
    (C : Stratum (subfieldIntegers F E) E V)
    (hClat : ∀ i, (C.chain.lattice i : Set V) = 𝓛'.lattice i)
    (hCn : C.n = ρ) (hCr : C.r = ρ - 1) (hC : C.IsSimple) (hsC : s (β - S.b) ∈ C.coset)
    (hQ : ∀ y : Module.End E V, y.restrictScalars F ∈ S.chain.endFiltration (1 - S.r) →
      y.restrictScalars F ∈ 𝓛'.endFiltration (1 - ρ)) :
    ∃ T U : Stratum 𝒪[F] F V, T.chain = 𝓛' ∧ U.chain = 𝓛' ∧ U.n = T.n ∧ T.r = ρ ∧
      U.r = ρ - 1 ∧ T.IsSimple ∧ β ∈ T.coset ∧ U.IsSimple ∧ β ∈ U.coset ∧
      elementRamificationIndex F T.b = elementRamificationIndex F S.b ∧
      elementResidueDegree F T.b = elementResidueDegree F S.b ∧
      elementRamificationIndex F U.b = subalgebraRamificationIndex F
        (Algebra.adjoin F ({S.b, C.b.restrictScalars F} : Set (Module.End F V))) ∧
      elementResidueDegree F U.b = subalgebraResidueDegree F
        (Algebra.adjoin F ({S.b, C.b.restrictScalars F} : Set (Module.End F V))) ∧
      criticalExponent U.chain U.b =
        max (criticalExponent 𝓛' S.b) (criticalExponent C.chain C.b) := by
  have := S.chain.finiteDimensional
  have hE := normalized_of_generated S hS.1 hβES hβE
  have hCc : C.b ∈ C.chain.endFiltration (-ρ) := by
    apply mem_endFiltration_of_le_valuation_subfield C.chain
    have h := C.valuation_ge
    rw [hCn] at h
    exact_mod_cast h
  have hsC' : s (β - S.b) - C.b ∈ C.chain.endFiltration (1 - ρ) := by
    have h : s (β - S.b) - C.b ∈ C.chain.endFiltration (-C.r) := hsC
    rwa [hCr, show -(ρ - 1) = 1 - ρ by ring] at h
  have hsbE : s (β - S.b) ∈ C.chain.endFiltration (-ρ) := by
    have h := add_mem (C.chain.endFiltration_antitone (by omega : -ρ ≤ 1 - ρ) hsC') hCc
    rwa [sub_add_cancel] at h
  have hsb : (s (β - S.b)).restrictScalars F ∈ 𝓛'.endFiltration (-ρ) :=
    (mem_endFiltration_restrictScalars hClat).mp hsbE
  obtain ⟨g, p, hg1, hginv, -, hp', hsp, hconj⟩ :=
    exists_conj_sub_mem S hS hβES hβE s 𝓛' hL' hb hsb
  have hP := endFiltration_le_of_restrict_le S.chain 𝓛' hE hL' hQ
  obtain ⟨T₀, hT₀c, hT₀r, hT₀b, hT₀, -⟩ :=
    exists_simple_of_normalized S hS hβES hβE 𝓛' hL' hρ.le
  have hg : (g : Module.End F V) ∈ 𝓛'.endFiltration 0 := by
    have h := one_add_mem_order_of_sandwiched S.chain 𝓛' hsw hg1
    rwa [add_sub_cancel] at h
  have hg' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ 𝓛'.endFiltration 0 := by
    have h := one_add_mem_order_of_sandwiched S.chain 𝓛' hsw hginv
    rwa [add_sub_cancel] at h
  have hsum : S.b + (β - S.b) = β := by abel
  rw [hsum] at hconj
  set β' := (g : Module.End F V) * β * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) with hβ'
  have h1 : β' - (S.b + p) ∈ 𝓛'.endFiltration (1 - ρ) := hP hconj
  have h2 : β' - S.b ∈ 𝓛'.endFiltration (-ρ) := by
    have h := add_mem (𝓛'.endFiltration_antitone (by omega : -ρ ≤ 1 - ρ) h1) hp'
    rwa [sub_add_eq_sub_sub, sub_add_cancel] at h
  -- the derived stratum of `p` on the second chain
  have hspE : s p ∈ C.chain.endFiltration (-ρ) := by rw [hsp]; exact hsbE
  let D : Stratum (subfieldIntegers F E) E V :=
    ⟨C.chain, ρ, ρ - 1, s p, by omega, by
      have h := le_valuation_of_mem_subfield C.chain hspE
      exact_mod_cast h⟩
  have hD : T₀.IsDerivedStratum E p s D := by
    refine ⟨hT₀, ⟨βE, hβES.trans hT₀b.symm, hβE⟩, ?_, ?_, hT₀r.symm, by rw [hT₀r], rfl⟩
    · rw [hT₀c, hT₀r]
      exact hp'
    · intro i
      rw [hT₀c]
      exact hClat i
  have hDC : D.Equivalent C := by
    unfold Stratum.Equivalent Stratum.coset
    ext x
    change x - s p ∈ C.chain.endFiltration (-(ρ - 1)) ↔ x - C.b ∈ C.chain.endFiltration (-C.r)
    rw [hCr, hsp, show -(ρ - 1) = 1 - ρ by ring]
    constructor
    · intro hx
      have h := add_mem hx hsC'
      rwa [sub_add_sub_cancel] at h
    · intro hx
      have h := sub_mem hx hsC'
      rwa [sub_sub_sub_cancel_right] at h
  obtain ⟨U₀, hU₀c, hU₀n, hU₀r, hU₀, hU₀coset, hU₀e, hU₀f, hU₀k⟩ :=
    refinement_aux (C := C) hD rfl (by rw [hCr]) hDC hC _ rfl
  rw [hT₀b] at hU₀coset hU₀e hU₀f hU₀k
  rw [hT₀c] at hU₀c hU₀k
  rw [hT₀c, hT₀r] at hU₀coset
  have hβ'U : β' ∈ U₀.coset := by
    rw [hU₀coset]
    exact h1
  have hgU : (g : Module.End F V) ∈ U₀.chain.endFiltration 0 := by rw [hU₀c]; exact hg
  have hgU' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ U₀.chain.endFiltration 0 := by
    rw [hU₀c]; exact hg'
  have hgT : (g : Module.End F V) ∈ T₀.chain.endFiltration 0 := by rw [hT₀c]; exact hg
  have hgT' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ T₀.chain.endFiltration 0 := by
    rw [hT₀c]; exact hg'
  have hback : ∀ y : Module.End F V, β - conjAlgHom g y = conjAlgHom g (β' - y) := by
    intro y
    rw [map_sub, hβ']
    simp [conjAlgHom_apply, mul_assoc]
  have hNT : NormalizingUnits 𝓛' (elementAlgebra S.b) := by
    rw [← hβES]
    exact normalizingUnits_of_generated 𝓛' hL' hβE
  obtain ⟨⟨hUf, hUn⟩, -⟩ := hU₀.1
  have hNU : NormalizingUnits 𝓛' (elementAlgebra U₀.b) := by
    rw [← hU₀c]
    exact normalizingUnits_of_isField U₀.chain hUf hUn
  refine ⟨conjStratum T₀ g hgT hgT', conjStratum U₀ g hgU hgU', hT₀c, hU₀c, hU₀n, hT₀r,
    by rw [← hT₀r]; exact hU₀r, isSimple_conjStratum T₀ g hgT hgT' hT₀, ?_,
    isSimple_conjStratum U₀ g hgU hgU' hU₀, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change β - conjAlgHom g T₀.b ∈ T₀.chain.endFiltration (-T₀.r)
    rw [hback, hT₀b, hT₀c, hT₀r]
    exact (mem_endFiltration_conj_iff 𝓛' hg hg').mpr h2
  · change β - conjAlgHom g U₀.b ∈ U₀.chain.endFiltration (-U₀.r)
    rw [hback]
    exact (mem_endFiltration_conj_iff U₀.chain hgU hgU').mpr hβ'U
  · change elementRamificationIndex F (conjAlgHom g T₀.b) = _
    rw [hT₀b]
    exact (elementInvariants_conj 𝓛' hg hg' S.b hNT).1
  · change elementResidueDegree F (conjAlgHom g T₀.b) = _
    rw [hT₀b]
    exact (elementInvariants_conj 𝓛' hg hg' S.b hNT).2
  · change elementRamificationIndex F (conjAlgHom g U₀.b) = _
    rw [(elementInvariants_conj 𝓛' hg hg' U₀.b hNU).1]
    exact hU₀e
  · change elementResidueDegree F (conjAlgHom g U₀.b) = _
    rw [(elementInvariants_conj 𝓛' hg hg' U₀.b hNU).2]
    exact hU₀f
  · change criticalExponent U₀.chain (conjAlgHom g U₀.b) = _
    rw [criticalExponent_conj U₀.chain hgU hgU', hU₀k]

end Steps

end Langlands.BushnellKutzko.PureApproximation
