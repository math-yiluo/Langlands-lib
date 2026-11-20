import Langlands.BushnellKutzko.StratumApproximationStatement
import Langlands.BushnellKutzko.MinimalCriticalExponentStatement
import Langlands.BushnellKutzko.StratumEquivalenceStatement
import Langlands.BushnellKutzko.RefinementStatement
import Langlands.BushnellKutzko.TameCorestrictionProof
import Langlands.BushnellKutzko.CorestrictionIntegers
import Langlands.BushnellKutzko.PureStratumSimpleApproximationStatement
import Langlands.BushnellKutzko.SimpleStratumCorestrictionCongruenceStatement
import Langlands.BushnellKutzko.CriticalDerivedStratumStatement

/-! # Reduction of T7 to its source parts (BK93 (2.4.1)–(2.4.2), pp. 65–66)

`StratumApproximationStatement` (T7) follows from the published T3, T5 and T6 and three
separately stated parts of BK93 (2.4.1): existence of a simple approximation with divisible
invariants, the corestriction congruence (ii)(c), and the critical derived stratum (iii).
The divisibility for every approximation, both directions of the minimal-degree
characterization, and the existence of defining sequences are derived here.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uE uV

section Degree

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (E : Type uE) [Field E] [Algebra F E] [FiniteDimensional F E]

/-- The length over `R` of a residue field `S/q` is the inertia degree of `q`. -/
private theorem length_quotient_eq_inertiaDeg {R : Type uF} {S : Type uE} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsMaximal]
    [q.LiesOver p] :
    (Module.length R (S ⧸ q)).toNat = q.inertiaDeg R := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal p q]
  let : Field (R ⧸ p) := Ideal.Quotient.field p
  rw [Module.length_eq_of_surjective (R := R ⧸ p) (S := R) (M := S ⧸ q)
    Ideal.Quotient.mk_surjective]
  simp [Module.length_eq_rank, Module.finrank]

/-- `e(E|F) f(E|F) = [E:F]` for the constructed invariants of a finite extension. -/
theorem subfieldRamificationIndex_mul_residueDegree :
    subfieldRamificationIndex F E * subfieldResidueDegree F E = Module.finrank F E := by
  classical
  let O := subfieldIntegers F E
  let P := IsLocalRing.maximalIdeal O
  have hmax : subfieldMaximalIdeal F E = P := subfieldMaximalIdeal_eq F E
  have : FaithfulSMul 𝒪[F] O := by
    apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
    intro x y hxy
    exact Subtype.ext ((algebraMap F E).injective
      (congrArg (fun z : O => (z : E)) hxy))
  have : Module.IsTorsionFree 𝒪[F] O :=
    Module.IsTorsionFree.trans_faithfulSMul 𝒪[F] O O
  have hp := IsDiscreteValuationRing.not_a_field 𝒪[F]
  have : P.LiesOver (𝓂[F]) :=
    ⟨(IsLocalRing.eq_maximalIdeal (inferInstance : (P.under 𝒪[F]).IsMaximal)).symm⟩
  have : Algebra.IsIntegral 𝒪[F] O := inferInstanceAs
    (Algebra.IsIntegral 𝒪[F] (integralClosure 𝒪[F] E))
  have hprime : (𝓂[F]).primesOver O = {P} := by
    ext Q
    constructor
    · intro hQ
      exact Set.mem_singleton_iff.mpr
        (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_mem_primesOver hQ))
    · intro hQ
      obtain rfl := Set.mem_singleton_iff.mp hQ
      exact ⟨inferInstance, inferInstance⟩
  let : Unique ((𝓂[F]).primesOver O) :=
    { default := ⟨P, hprime ▸ Set.mem_singleton _⟩
      uniq := fun q => Subtype.ext (Set.mem_singleton_iff.mp (hprime ▸ q.property)) }
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (𝓂[F] : Ideal 𝒪[F]) O
  have hq (q : (𝓂[F] : Ideal 𝒪[F]).primesOver O) : (q : Ideal O) = P :=
    Set.mem_singleton_iff.mp (hprime ▸ q.property)
  simp only [Fintype.sum_unique, hq] at hsum
  have hfr : Module.finrank F E = Module.finrank 𝒪[F] O :=
    IsFractionRing.finrank_eq 𝒪[F] F O E
  have : P.IsMaximal := IsLocalRing.maximalIdeal.isMaximal O
  have hres : subfieldResidueDegree F E = P.inertiaDeg 𝒪[F] := by
    unfold subfieldResidueDegree subfieldResidueRing
    rw [hmax]
    exact length_quotient_eq_inertiaDeg (𝓂[F]) P
  rw [hfr, ← hsum, hres]
  unfold subfieldRamificationIndex
  rw [hmax]

end Degree

section Element

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- `e f = [R:F]` for a field subalgebra `R` of `End_F(V)`. -/
theorem subalgebraRamificationIndex_mul_residueDegree (R : Subalgebra F (Module.End F V))
    (h : IsField R) :
    subalgebraRamificationIndex F R * subalgebraResidueDegree F R = Module.finrank F R := by
  unfold subalgebraRamificationIndex subalgebraResidueDegree
  rw [dite_eq_left h, dite_eq_left h]
  let := h.toField
  exact subfieldRamificationIndex_mul_residueDegree F R

/-- `e(F[b]|F) f(F[b]|F) = [F[b]:F]` when `F[b]` is a field. -/
theorem elementRamificationIndex_mul_residueDegree (b : Module.End F V)
    (h : IsField (elementAlgebra b)) :
    elementRamificationIndex F b * elementResidueDegree F b = elementDegree F b := by
  unfold elementRamificationIndex elementResidueDegree elementDegree
  rw [dite_eq_left h, dite_eq_left h]
  let := h.toField
  exact subfieldRamificationIndex_mul_residueDegree F (elementAlgebra b)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- A generated field has positive degree. -/
theorem elementDegree_pos (b : Module.End F V) (h : IsField (elementAlgebra b)) :
    0 < elementDegree F b := by
  have : Nontrivial (elementAlgebra b) := ⟨h.exists_pair_ne⟩
  exact Module.finrank_pos

end Element

section Strata

variable {O : Type*} {K : Type*} {V : Type*} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

/-- Strata with the same chain and depth are equivalent when `S.b − T.b ∈ 𝔓^{−r}`. -/
theorem Stratum.equivalent_of_sub_mem {S T : Stratum O K V} (hc : T.chain = S.chain)
    (hr : T.r = S.r) (h : S.b - T.b ∈ S.chain.endFiltration (-S.r)) : S.Equivalent T := by
  unfold Stratum.Equivalent Stratum.coset
  rw [hc, hr]
  ext x
  constructor
  · intro hx
    have := add_mem hx h
    simpa using this
  · intro hx
    have := sub_mem hx h
    simpa using this

/-- Equivalent strata satisfy `S.b − T.b ∈ 𝔓^{−r}`. -/
theorem Stratum.sub_mem_of_equivalent {S T : Stratum O K V} (h : S.Equivalent T) :
    S.b - T.b ∈ S.chain.endFiltration (-S.r) := by
  have hT : T.b ∈ S.coset := by
    rw [h]
    show T.b - T.b ∈ T.chain.endFiltration (-T.r)
    simp
  have h' : T.b - S.b ∈ S.chain.endFiltration (-S.r) := hT
  have := neg_mem h'
  simpa using this

/-- `v_𝔄(x) = k` when `x ∈ 𝔓^k` and `x ∉ 𝔓^{k+1}`. -/
theorem LatticeChain.valuation_eq_of_mem_of_notMem (𝓛 : LatticeChain O K V)
    {x : Module.End K V} {k : ℤ} (h1 : x ∈ 𝓛.endFiltration k)
    (h2 : x ∉ 𝓛.endFiltration (k + 1)) : 𝓛.valuation x = (k : WithTop ℤ) := by
  have hx : x ≠ 0 := by
    rintro rfl
    exact h2 (zero_mem _)
  unfold LatticeChain.valuation
  rw [ite_eq_right hx]
  have hset : {n : ℤ | x ∈ 𝓛.endFiltration n} = Set.Iic k := by
    ext n
    constructor
    · intro hn
      by_contra hlt
      exact h2 (𝓛.endFiltration_antitone (show k + 1 ≤ n by simp at hlt; omega) hn)
    · intro hn
      exact 𝓛.endFiltration_antitone hn h1
  rw [hset, csSup_Iic]

end Strata

section Reduction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- Divisibility of `e` and `f` for every simple approximation (T7, part (i)). -/
theorem dvd_of_simpleApproximation (hT5 : StratumEquivalenceStatement.{uF, uV})
    (hPi : PureStratumSimpleApproximationStatement.{uF, uV})
    (S : Stratum 𝒪[F] F V) (hS : S.IsPure) (T : Stratum 𝒪[F] F V)
    (hT : T.IsSimple) (hST : S.Equivalent T) :
    elementRamificationIndex F T.b ∣ elementRamificationIndex F S.b ∧
      elementResidueDegree F T.b ∣ elementResidueDegree F S.b := by
  obtain ⟨T₀, -, -, -, hT₀, hST₀, he, hf⟩ := hPi F V S hS
  have h := (hT5 F V T₀ T (hST₀.symm.trans hST)).2.2.2 hT₀ hT
  rw [← h.2.2.1, ← h.2.2.2]
  exact ⟨he, hf⟩

/-- A simple stratum has minimal generated-field degree in its class. -/
theorem degree_le_of_isSimple (hT5 : StratumEquivalenceStatement.{uF, uV})
    (hPi : PureStratumSimpleApproximationStatement.{uF, uV})
    (S T U : Stratum 𝒪[F] F V) (hT : T.IsSimple) (hST : S.Equivalent T)
    (hU : U.IsPure) (hSU : S.Equivalent U) :
    elementDegree F T.b ≤ elementDegree F U.b := by
  obtain ⟨T', -, -, -, hT', hUT', he, hf⟩ := hPi F V U hU
  have h := (hT5 F V T T' (hST.symm.trans (hSU.trans hUT'))).2.2.2 hT hT'
  obtain ⟨hTF, -⟩ := hT.1.1
  obtain ⟨hUF, -⟩ := hU.1
  rw [← elementRamificationIndex_mul_residueDegree T.b hTF,
    ← elementRamificationIndex_mul_residueDegree U.b hUF, h.2.2.1, h.2.2.2]
  apply Nat.le_of_dvd
  · rw [elementRamificationIndex_mul_residueDegree U.b hUF]
    exact elementDegree_pos U.b hUF
  · exact mul_dvd_mul he hf

set_option synthInstance.maxHeartbeats 400000 in
/-- A pure stratum of minimal degree in its class is simple (T7, part (i)). -/
theorem isSimple_of_degree_minimal (hT5 : StratumEquivalenceStatement.{uF, uV})
    (hT6 : RefinementStatement.{uF, uV, uV})
    (hPi : PureStratumSimpleApproximationStatement.{uF, uV})
    (hPiii : CriticalDerivedStratumStatement.{uF, uV})
    (S T : Stratum 𝒪[F] F V) (hc : T.chain = S.chain) (hn : T.n = S.n) (hr : T.r = S.r)
    (hT : T.IsPure) (hST : S.Equivalent T)
    (hmin : ∀ U : Stratum 𝒪[F] F V, U.chain = S.chain → U.n = S.n → U.r = S.r →
      U.IsPure → S.Equivalent U → elementDegree F T.b ≤ elementDegree F U.b) :
    T.IsSimple := by
  refine ⟨hT, ?_⟩
  by_contra hns
  rw [not_lt] at hns
  obtain ⟨k, hk⟩ : ∃ k : ℤ, criticalExponent T.chain T.b = (k : WithBot ℤ) := by
    cases h : criticalExponent T.chain T.b with
    | bot => rw [h] at hns; exact absurd hns (by simp)
    | coe k => exact ⟨k, rfl⟩
  rw [hk] at hns
  have hkr : -T.r ≤ k := WithBot.coe_le_coe.mp hns
  have hrn := T.r_lt_n
  -- The stratum `[𝔄,n,−k₀,β]` at the critical level.
  let T' : Stratum 𝒪[F] F V := ⟨T.chain, T.n, -k, T.b, by omega, T.valuation_ge⟩
  have hT'k : criticalExponent T'.chain T'.b = ((-T'.r : ℤ) : WithBot ℤ) := by
    simp [T', hk]
  obtain ⟨G, hGc, hGn, hGr, hG, hT'G, -, -⟩ := hPi F V T' hT
  have hder := hPiii F V T' G hT hT'k hGc hGn hGr hG hT'G
  have hGc' : G.chain = T.chain := hGc
  have hGn' : G.n = T.n := hGn
  have hGr' : G.r = -k := hGr
  have hb : T.b - G.b ∈ T.chain.endFiltration k := by
    have := Stratum.sub_mem_of_equivalent hT'G
    simpa [T'] using this
  have hGk : criticalExponent G.chain G.b < (k : WithBot ℤ) := by
    have := hG.2
    rwa [hGr', neg_neg] at this
  -- `v_𝔄(β − γ) = −r'`, since otherwise `β` and `γ` would be equivalent simple strata at
  -- level `r' − 1` with different critical exponents.
  have hbv : T.chain.valuation (T.b - G.b) = (k : WithTop ℤ) := by
    apply LatticeChain.valuation_eq_of_mem_of_notMem _ hb
    intro hb1
    have h1 : -k - 1 < T.n := by omega
    have h2 : -k - 1 < G.n := by rw [hGn']; exact h1
    let T₁ : Stratum 𝒪[F] F V := ⟨T.chain, T.n, -k - 1, T.b, h1, T.valuation_ge⟩
    let G₁ : Stratum 𝒪[F] F V := ⟨G.chain, G.n, -k - 1, G.b, h2, G.valuation_ge⟩
    have hT₁ : T₁.IsSimple := ⟨hT, by
      show criticalExponent T.chain T.b < _
      rw [hk]
      exact WithBot.coe_lt_coe.mpr (show k < -(-k - 1) by omega)⟩
    have hG₁ : G₁.IsSimple :=
      ⟨hG.1, lt_trans hGk (WithBot.coe_lt_coe.mpr (show k < -(-k - 1) by omega))⟩
    have hTG₁ : T₁.Equivalent G₁ := by
      apply Stratum.equivalent_of_sub_mem (S := T₁) (T := G₁) hGc' rfl
      show T.b - G.b ∈ T.chain.endFiltration (-(-k - 1))
      simpa [add_comm] using hb1
    have h5 := ((hT5 F V T₁ G₁ hTG₁).2.2.2 hT₁ hG₁).2.1
    change criticalExponent T.chain T.b = criticalExponent G.chain G.b at h5
    rw [hk] at h5
    rw [← h5] at hGk
    exact lt_irrefl _ hGk
  -- Apply the refinement theorem to `γ` and the perturbation `β − γ`.
  obtain ⟨hGF, -⟩ := hG.1.1
  let := hGF.toField
  obtain ⟨s⟩ := (tameCorestriction F V (elementAlgebra G.b)).1
  obtain ⟨D, C, hD, hCc, hCn, hCr, hDC, hC⟩ := hder hGF s
  have hbG : G.chain.valuation (T.b - G.b) = (-G.r : WithTop ℤ) := by
    rw [hGc', hGr', hbv]
    simp
  obtain ⟨T'', hT''c, hT''n, hT''r, hT'', hT''coset, hT''e, hT''f, hT''k⟩ :=
    hT6 F V (elementAlgebra G.b) G (T.b - G.b) s D C hD hbG hCc hCn hCr hDC hC
  -- The refined stratum is equivalent to `[𝔄,n,r'−1,β]`.
  have hrn1 : -k - 1 < T.n := by omega
  let T₁ : Stratum 𝒪[F] F V := ⟨T.chain, T.n, -k - 1, T.b, hrn1, T.valuation_ge⟩
  have hT₁ : T₁.IsSimple := ⟨hT, by
    show criticalExponent T.chain T.b < _
    rw [hk]
    exact WithBot.coe_lt_coe.mpr (show k < -(-k - 1) by omega)⟩
  have hT''T₁ : T''.Equivalent T₁ := by
    unfold Stratum.Equivalent
    rw [hT''coset]
    have e1 : G.b + (T.b - G.b) = T.b := by abel
    have e2 : (1 - G.r) = -(-k - 1) := by rw [hGr']; ring
    rw [e1, e2, hGc']
    rfl
  have h5 := (hT5 F V T'' T₁ hT''T₁).2.2.2 hT'' hT₁
  -- Hence `k₀(c,𝔅) = k₀(β,𝔄)`, so `c` is not a scalar of `E = F[γ]`.
  have hmax : ∀ a c : WithBot ℤ, a < (k : WithBot ℤ) → max a c = (k : WithBot ℤ) →
      c = (k : WithBot ℤ) := by
    intro a c ha h
    rcases max_choice a c with hm | hm
    · rw [hm] at h
      exact absurd h (ne_of_lt ha)
    · rwa [hm] at h
  have h55 := hT''k.symm.trans h5.2.1
  change max _ _ = criticalExponent T.chain T.b at h55
  rw [hk] at h55
  have hkC := hmax _ _ hGk h55
  have hnot : C.b.restrictScalars F ∉ elementAlgebra G.b := by
    intro hmem
    unfold criticalExponent at hkC
    split_ifs at hkC with hbot
    · exact WithBot.bot_ne_coe hkC
    · apply hbot
      apply le_bot_iff.mp
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff, SetLike.mem_coe, Algebra.mem_bot]
      refine ⟨⟨_, hmem⟩, ?_⟩
      ext v
      rfl
  -- The degree of `F[β]` is that of `F[γ,c]`, which strictly contains `F[γ]`.
  set E₁ := Algebra.adjoin F ({G.b, C.b.restrictScalars F} : Set (Module.End F V)) with hE₁
  obtain ⟨hTF, -⟩ := hT.1
  have heT := elementRamificationIndex_mul_residueDegree T.b hTF
  have hdpos := elementDegree_pos T.b hTF
  have he'' : elementRamificationIndex F T''.b = elementRamificationIndex F T.b := h5.2.2.1
  have hf'' : elementResidueDegree F T''.b = elementResidueDegree F T.b := h5.2.2.2
  have hE₁F : IsField E₁ := by
    by_contra hnf
    have h0 : subalgebraRamificationIndex F E₁ = 0 := by
      unfold subalgebraRamificationIndex
      rw [dite_eq_right hnf]
    rw [← he'', hT''e, h0, zero_mul] at heT
    omega
  have hdegT : elementDegree F T.b = Module.finrank F E₁ := by
    rw [← heT, ← he'', ← hf'', hT''e, hT''f]
    exact subalgebraRamificationIndex_mul_residueDegree E₁ hE₁F
  have hlt : elementDegree F G.b < Module.finrank F E₁ := by
    have hle : elementAlgebra G.b ≤ E₁ := Algebra.adjoin_mono (by simp)
    have hne : elementAlgebra G.b ≠ E₁ := by
      intro heq
      exact hnot ((SetLike.ext_iff.mp heq _).mpr (Algebra.subset_adjoin (by simp)))
    have hlt' : Subalgebra.toSubmodule (elementAlgebra G.b) < Subalgebra.toSubmodule E₁ :=
      lt_of_le_of_ne hle (fun h => hne (Subalgebra.toSubmodule_injective h))
    exact Submodule.finrank_lt_finrank_of_lt hlt'
  -- `[𝔄,n,r,γ]` is pure and equivalent to `S`, contradicting minimality.
  have hUr : T.r < G.n := by rw [hGn']; exact hrn
  let U : Stratum 𝒪[F] F V := ⟨G.chain, G.n, T.r, G.b, hUr, G.valuation_ge⟩
  have hTU : T.Equivalent U := by
    apply Stratum.equivalent_of_sub_mem (S := T) (T := U) hGc' rfl
    exact T.chain.endFiltration_antitone (show -T.r ≤ k by omega) hb
  have hle := hmin U (hGc'.trans hc) (hGn'.trans hn) hr hG.1 (hST.trans hTU)
  change elementDegree F T.b ≤ elementDegree F G.b at hle
  omega

/-- For a pure stratum with nonscalar `γ`, `−n ≤ k₀(γ,𝔄)` (from T3, BK93 (1.4.15)). -/
theorem neg_n_le_criticalExponent (hT3 : MinimalCriticalExponentStatement.{uF, uV, uV})
    (G : Stratum 𝒪[F] F V) (hG : G.IsPure) {k : ℤ}
    (hk : criticalExponent G.chain G.b = (k : WithBot ℤ)) : -G.n ≤ k := by
  obtain ⟨⟨hGF, hunits⟩, hv⟩ := hG
  let := hGF.toField
  let β : elementAlgebra G.b := ⟨G.b, Algebra.self_mem_adjoin_singleton F G.b⟩
  have hβ : subfieldEmbedding F (elementAlgebra G.b) V β = G.b := by
    ext v
    rfl
  have htop : Algebra.adjoin F ({β} : Set (elementAlgebra G.b)) = ⊤ := by
    have h := Algebra.adjoin_adjoin_coe_preimage (R := F) (s := ({G.b} : Set (Module.End F V)))
    convert h using 2
    ext x
    simp [β, Subtype.ext_iff]
  have hns : ¬ ∃ a : F, algebraMap F (elementAlgebra G.b) a = β := by
    rintro ⟨a, ha⟩
    have hbot : elementAlgebra G.b = ⊥ := by
      apply le_bot_iff.mp
      apply Algebra.adjoin_le
      rw [Set.singleton_subset_iff, SetLike.mem_coe, Algebra.mem_bot]
      exact ⟨a, congrArg Subtype.val ha⟩
    simp [criticalExponent, hbot] at hk
  obtain ⟨k', hk', hvle, -⟩ := hT3 F V (elementAlgebra G.b) G.chain β htop hns hunits
  rw [hβ] at hk' hvle
  rw [hk] at hk'
  have hkk : k = k' := WithBot.coe_injective hk'
  rw [hv, ← hkk] at hvle
  have h' : ((-G.n : ℤ) : WithTop ℤ) ≤ (k : WithTop ℤ) := by simpa using hvle
  exact WithTop.coe_le_coe.mp h'

/-- Every pure stratum has a defining sequence on its own lattice chain (BK93 (2.4.2)). -/
theorem exists_definingSequence (hT3 : MinimalCriticalExponentStatement.{uF, uV, uV})
    (hPi : PureStratumSimpleApproximationStatement.{uF, uV})
    (hPiii : CriticalDerivedStratumStatement.{uF, uV}) :
    ∀ (m : ℕ) (S : Stratum 𝒪[F] F V), (S.n - S.r).toNat = m → S.IsPure →
      ∃ (s : ℕ) (q : Fin (s + 1) → Stratum 𝒪[F] F V),
        S.IsDefiningSequence q ∧ ∀ i, (q i).chain = S.chain := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro S hm hS
  obtain ⟨G, hGc, hGn, hGr, hG, hSG, -, -⟩ := hPi F V S hS
  by_cases hstop : criticalExponent S.chain G.b = ((-S.n : ℤ) : WithBot ℤ) ∨
      criticalExponent S.chain G.b = ⊥
  · refine ⟨0, fun _ => G, ⟨hS, fun _ => ⟨by rw [hGc], hGn, hG⟩, hSG.symm, hGr,
      fun i j hij => absurd hij (by
        have := i.isLt
        have := j.isLt
        rw [Fin.lt_def]
        omega), fun i => i.elim0, hstop, fun i => i.elim0⟩, fun _ => hGc⟩
  · simp only [not_or] at hstop
    obtain ⟨hne, hnbot⟩ := hstop
    obtain ⟨k, hk⟩ : ∃ k : ℤ, criticalExponent S.chain G.b = (k : WithBot ℤ) := by
      cases h : criticalExponent S.chain G.b with
      | bot => exact absurd h hnbot
      | coe k => exact ⟨k, rfl⟩
    have hkG : criticalExponent G.chain G.b = (k : WithBot ℤ) := by rw [hGc]; exact hk
    have hlow := neg_n_le_criticalExponent hT3 G hG.1 hkG
    have hne' : k ≠ -S.n := fun h => hne (by rw [hk, h])
    have hup : k < -S.r := by
      have := hG.2
      rw [hkG, hGr] at this
      exact WithBot.coe_lt_coe.mp this
    rw [hGn] at hlow
    have hr1 : -k < G.n := by rw [hGn]; omega
    let S₁ : Stratum 𝒪[F] F V := ⟨G.chain, G.n, -k, G.b, hr1, G.valuation_ge⟩
    have hS₁ : S₁.IsPure := hG.1
    have hS₁c : S₁.chain = S.chain := hGc
    have hS₁n : S₁.n = S.n := hGn
    have hm₁ : (S₁.n - S₁.r).toNat < m := by
      rw [← hm, hS₁n]
      show (S.n - -k).toNat < (S.n - S.r).toNat
      omega
    have hcrit₁ : criticalExponent S₁.chain S₁.b = ((-S₁.r : ℤ) : WithBot ℤ) := by
      show criticalExponent G.chain G.b = ((-(-k) : ℤ) : WithBot ℤ)
      rw [neg_neg]
      exact hkG
    obtain ⟨s', q', hq', hq'c⟩ := ih _ hm₁ S₁ rfl hS₁
    obtain ⟨-, hq'1, hq'0e, hq'0r, hq'mono, hq'step, hq'last, hq'der⟩ := hq'
    refine ⟨s' + 1, Fin.cons G q', ⟨hS, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · refine Fin.cases ?_ (fun j => ?_)
      · rw [Fin.cons_zero]
        exact ⟨by rw [hGc], hGn, hG⟩
      · rw [Fin.cons_succ]
        obtain ⟨h1, h2, h3⟩ := hq'1 j
        exact ⟨h1.trans (by rw [hS₁c]), h2.trans hS₁n, h3⟩
    · rw [Fin.cons_zero]
      exact hSG.symm
    · rw [Fin.cons_zero]
      exact hGr
    · rw [Fin.strictMono_iff_lt_succ]
      refine Fin.cases ?_ (fun j => ?_)
      · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hq'0r]
        show G.r < -k
        omega
      · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hq'mono Fin.castSucc_lt_succ
    · refine Fin.cases ?_ (fun j => ?_)
      · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
        refine ⟨?_, ?_⟩
        · rw [hk, hq'0r]
          show (k : WithBot ℤ) = ((-(-k) : ℤ) : WithBot ℤ)
          rw [neg_neg]
        · have h := Stratum.sub_mem_of_equivalent hq'0e
          rw [hq'c 0, hS₁c] at h
          exact h
      · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        obtain ⟨h1, h2⟩ := hq'step j
        rw [hS₁c] at h1 h2
        exact ⟨h1, h2⟩
    · rw [← Fin.succ_last, Fin.cons_succ]
      rw [hS₁c, hS₁n] at hq'last
      exact hq'last
    · refine Fin.cases ?_ (fun j => ?_)
      · rw [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ]
        exact hPiii F V S₁ (q' 0) hS₁ hcrit₁ (hq'c 0) (hq'1 0).2.1 hq'0r (hq'1 0).2.2
          hq'0e.symm
      · rw [← Fin.succ_castSucc, Fin.cons_succ, Fin.cons_succ]
        exact hq'der j
    · refine Fin.cases ?_ (fun j => ?_)
      · rw [Fin.cons_zero]
        exact hGc
      · rw [Fin.cons_succ]
        exact (hq'c j).trans hS₁c

end Reduction

/-- **Reduction of T7.** The published T3, T5 and T6, together with the three source parts
`PureStratumSimpleApproximationStatement` ((2.4.1)(i), existence with divisibility for the
witness), `SimpleStratumCorestrictionCongruenceStatement` ((2.4.1)(ii)(c)) and
`CriticalDerivedStratumStatement` ((2.4.1)(iii)), imply `StratumApproximationStatement`. -/
def StratumApproximationReductionStatement : Prop :=
  MinimalCriticalExponentStatement.{uF, uV, uV} →
  StratumEquivalenceStatement.{uF, uV} →
  RefinementStatement.{uF, uV, uV} →
  PureStratumSimpleApproximationStatement.{uF, uV} →
  SimpleStratumCorestrictionCongruenceStatement.{uF, uV} →
  CriticalDerivedStratumStatement.{uF, uV} →
  StratumApproximationStatement.{uF, uV}

/-- The reduction of T7 to T3, T5, T6 and the three source parts holds. -/
theorem stratumApproximationReduction : StratumApproximationReductionStatement.{uF, uV} := by
  intro hT3 hT5 hT6 hPi hPii hPiii F _ _ _ _ V _ _ _
  refine ⟨fun S hS => ⟨?_, ?_, ?_⟩, hPii F V, hPiii F V, ?_⟩
  · obtain ⟨T, hc, hn, hr, hT, hST, -, -⟩ := hPi F V S hS
    exact ⟨T, hc, hn, hr, hT, hST⟩
  · intro T _ _ _ hT hST
    exact dvd_of_simpleApproximation hT5 hPi S hS T hT hST
  · intro T hc hn hr hT hST
    constructor
    · intro hTs U _ _ _ hU hSU
      exact degree_le_of_isSimple hT5 hPi S T U hTs hST hU hSU
    · intro hmin
      exact isSimple_of_degree_minimal hT5 hT6 hPi hPiii S T hc hn hr hT hST hmin
  · intro S hS
    obtain ⟨s, q, hq, -⟩ := exists_definingSequence hT3 hPi hPiii _ S rfl hS
    exact ⟨s, q, hq⟩


end Langlands.BushnellKutzko
