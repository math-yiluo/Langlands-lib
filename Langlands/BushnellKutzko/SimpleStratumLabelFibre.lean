import Langlands.BushnellKutzko.SimpleStratumLabelConjugation
import Langlands.BushnellKutzko.SimpleStratumLabelAdjoin
import Langlands.BushnellKutzko.SimpleCharacterTransferRelative
import Langlands.BushnellKutzko.StratumApproximationReduction
import Langlands.BushnellKutzko.StratumEquivalenceProof
import Langlands.BushnellKutzko.RefinementProof
import Langlands.BushnellKutzko.CriticalDerivedStratumProof
import Langlands.BushnellKutzko.SimpleStratumCorestrictionCongruenceProof

/-! # Strata in the fibre of a simple stratum one level up

For a simple stratum `[𝔄,n,r,γ]` with `E = F[γ]` and a tame corestriction `s`, this module
compares perturbations `γ + c`, `c ∈ 𝔓^{−r}`, through the derived elements `s(c)` modulo
`𝔔^{1−r}`. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SimpleStratumLabel

universe uF uE uV uO

section Generic

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem restrictScalars_mul (x y : Module.End E V) :
    (x * y).restrictScalars F = x.restrictScalars F * y.restrictScalars F := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem restrictScalars_sub (x y : Module.End E V) :
    (x - y).restrictScalars F = x.restrictScalars F - y.restrictScalars F := rfl

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `E`-linear endomorphisms commute with the scalars of `E`. -/
theorem restrictScalars_commute_subfieldEmbedding (x : Module.End E V) (e : E) :
    x.restrictScalars F * subfieldEmbedding F E V e =
      subfieldEmbedding F E V e * x.restrictScalars F := by
  ext v
  change x (e • v) = e • x v
  exact x.map_smul e v

/-- Let `[𝔄,n,r,γ]` be simple with `E = F[γ]`, and let `c₁, c₂ ∈ 𝔓^{−r}`. Suppose that
`s(c_i) ≡ α_i (mod 𝔔^{1−r})` and that a unit `w` of `𝔅` satisfies
`w⁻¹α₁w ≡ α₂ (mod 𝔔^{1−r})`. Then `γ + c₁` and `γ + c₂` are conjugate modulo `𝔓^{1−r}`
by a unit of `𝔄`. -/
theorem exists_unit_conj_of_derived (T : Stratum 𝒪[F] F V) (hT : T.IsSimple) {γE : E}
    (hγE : subfieldEmbedding F E V γE = T.b) (hgen : Algebra.adjoin F ({γE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) {O : Type uO} [CommRing O] [Algebra O E]
    [Module O V] [IsScalarTower O E V] (C : LatticeChain O E V)
    (hC : ∀ i, (C.lattice i : Set V) = T.chain.lattice i)
    {c₁ c₂ : Module.End F V} (hc₁ : c₁ ∈ T.chain.endFiltration (-T.r))
    (hc₂ : c₂ ∈ T.chain.endFiltration (-T.r)) {α₁ α₂ : Module.End E V}
    (h₁ : (s c₁ - α₁).restrictScalars F ∈ T.chain.endFiltration (1 - T.r))
    (h₂ : (s c₂ - α₂).restrictScalars F ∈ T.chain.endFiltration (1 - T.r))
    {w : (Module.End E V)ˣ} (hw : w ∈ C.unitFiltration 0)
    (hα : ((w⁻¹ : (Module.End E V)ˣ) : Module.End E V) * α₁ * w - α₂ ∈
      C.endFiltration (1 - T.r)) :
    ∃ g ∈ T.chain.unitFiltration 0,
      ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * (T.b + c₁) * g - (T.b + c₂) ∈
        T.chain.endFiltration (1 - T.r) := by
  set L := T.chain
  set W := relativeEndUnits (F := F) (V := V) E w with hW
  have hWL : W ∈ L.unitFiltration 0 :=
    (L.mem_unitFiltration_restrictScalars_iff C (fun i v => by
      rw [← SetLike.mem_coe, hC, SetLike.mem_coe]) 0 w).mpr hw
  have hWv : (W : Module.End F V) = (w : Module.End E V).restrictScalars F := rfl
  have hWiv : ((W⁻¹ : (Module.End F V)ˣ) : Module.End F V) =
      ((w⁻¹ : (Module.End E V)ˣ) : Module.End E V).restrictScalars F := by
    rw [hW, ← map_inv]
    rfl
  -- The conjugated perturbation `c₁' = W⁻¹ c₁ W`.
  set c₁' := ((W⁻¹ : (Module.End F V)ˣ) : Module.End F V) * c₁ * W with hc₁'
  have hc₁'mem : c₁' ∈ L.endFiltration (-T.r) := by
    have h1 := L.mul_mem_endFiltration (L.mul_mem_endFiltration hWL.2.1 hc₁) hWL.1
    simpa using h1
  have hsc₁' : s c₁' = ((w⁻¹ : (Module.End E V)ˣ) : Module.End E V) * s c₁ * w := by
    rw [hc₁', hWiv, hWv]
    have h1 := s.map_mul_right
      (((w⁻¹ : (Module.End E V)ˣ) : Module.End E V).restrictScalars F * c₁) (w : Module.End E V)
    have h2 := s.map_mul_left ((w⁻¹ : (Module.End E V)ˣ) : Module.End E V) c₁
    exact h1.trans (congrArg (· * (w : Module.End E V)) h2)
  -- `s(c₁' − c₂) ∈ 𝔔^{1−r}`.
  have hw0 : (w : Module.End E V) ∈ C.endFiltration 0 := hw.1
  have hwi0 : ((w⁻¹ : (Module.End E V)ˣ) : Module.End E V) ∈ C.endFiltration 0 := hw.2.1
  have h₁C : s c₁ - α₁ ∈ C.endFiltration (1 - T.r) :=
    (mem_endFiltration_restrictScalars hC).mpr h₁
  have h₂C : s c₂ - α₂ ∈ C.endFiltration (1 - T.r) :=
    (mem_endFiltration_restrictScalars hC).mpr h₂
  have hconj : ((w⁻¹ : (Module.End E V)ˣ) : Module.End E V) * (s c₁ - α₁) * w ∈
      C.endFiltration (1 - T.r) := by
    have h1 := C.mul_mem_endFiltration (C.mul_mem_endFiltration hwi0 h₁C) hw0
    simpa using h1
  have hdiff : s (c₁' - c₂) ∈ C.endFiltration (1 - T.r) := by
    have hkey : s (c₁' - c₂) =
        ((w⁻¹ : (Module.End E V)ˣ) : Module.End E V) * (s c₁ - α₁) * w +
          (((w⁻¹ : (Module.End E V)ˣ) : Module.End E V) * α₁ * w - α₂) - (s c₂ - α₂) := by
      rw [map_sub]
      change s c₁' - s c₂ = _
      rw [hsc₁']
      noncomm_ring
    rw [hkey]
    exact sub_mem (add_mem hconj hα) h₂C
  have hdiffL : (s (c₁' - c₂)).restrictScalars F ∈ L.endFiltration (1 - T.r) :=
    (mem_endFiltration_restrictScalars hC).mp hdiff
  obtain ⟨g, hg, hconjg⟩ := exists_unit_conj_add_sub_mem T hT hγE hgen s hc₂
    (sub_mem hc₁'mem hc₂) hdiffL
  -- `W` commutes with `γ`.
  have hcomm : (T.b : Module.End F V) * W = W * T.b := by
    rw [← hγE, hWv]
    exact (restrictScalars_commute_subfieldEmbedding (w : Module.End E V) γE).symm
  have hb : T.b + c₂ + (c₁' - c₂) =
      ((W⁻¹ : (Module.End F V)ˣ) : Module.End F V) * (T.b + c₁) * W := by
    have h1 : ((W⁻¹ : (Module.End F V)ˣ) : Module.End F V) * T.b * W = T.b := by
      rw [mul_assoc, hcomm, ← mul_assoc, Units.inv_mul, one_mul]
    rw [hc₁', mul_add, add_mul, h1]
    abel
  refine ⟨W * g⁻¹, mul_mem hWL (inv_mem ((L.unitFiltration_antitone (Nat.zero_le 1)) hg)), ?_⟩
  rw [hb] at hconjg
  have : (((W * g⁻¹)⁻¹ : (Module.End F V)ˣ) : Module.End F V) * (T.b + c₁) * (W * g⁻¹ : (Module.End F V)ˣ) =
      (g : Module.End F V) * (((W⁻¹ : (Module.End F V)ˣ) : Module.End F V) * (T.b + c₁) * W) *
        ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) := by
    simp only [mul_inv_rev, inv_inv, Units.val_mul]
    noncomm_ring
  rw [this]
  exact hconjg

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The stratum `[𝔄,n,r−1,γ]` attached to a simple stratum `[𝔄,n,r,γ]` is simple. -/
theorem isSimple_lower (T : Stratum 𝒪[F] F V) (hT : T.IsSimple) :
    (⟨T.chain, T.n, T.r - 1, T.b, by have := T.r_lt_n; omega, T.valuation_ge⟩ :
      Stratum 𝒪[F] F V).IsSimple := by
  refine ⟨hT.1, ?_⟩
  change criticalExponent T.chain T.b < ((-(T.r - 1) : ℤ) : WithBot ℤ)
  exact lt_trans hT.2 (WithBot.coe_lt_coe.mpr (by omega))

/-- If the derived element `s(β − γ)` of a simple stratum `[𝔄,n,r−1,β]` in the fibre of
`[𝔄,n,r,γ]` lies in `𝔔^{1−r}`, then `F[β]` and `F[γ]` have the same ramification index and
residue degree. -/
theorem elementInvariants_of_derived_null (T : Stratum 𝒪[F] F V) (hT : T.IsSimple) {γE : E}
    (hγE : subfieldEmbedding F E V γE = T.b) (hgen : Algebra.adjoin F ({γE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) (S : Stratum 𝒪[F] F V) (hSc : S.chain = T.chain)
    (_hSn : S.n = T.n) (hSr : S.r = T.r - 1) (hS : S.IsSimple)
    (hc : S.b - T.b ∈ T.chain.endFiltration (-T.r))
    (hnull : (s (S.b - T.b)).restrictScalars F ∈ T.chain.endFiltration (1 - T.r)) :
    elementRamificationIndex F S.b = elementRamificationIndex F T.b ∧
      elementResidueDegree F S.b = elementResidueDegree F T.b := by
  have := T.chain.finiteDimensional
  obtain ⟨g, hg, hgc⟩ := exists_unit_conj_add_sub_mem T hT hγE hgen s (c := 0)
    (zero_mem _) hc hnull
  have hgS : T.b + 0 + (S.b - T.b) = S.b := by abel
  rw [hgS, add_zero] at hgc
  have hgi : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ S.chain.endFiltration 0 := by
    rw [hSc]; exact hg.2.1
  have hgii : (((g⁻¹)⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ S.chain.endFiltration 0 := by
    rw [hSc, inv_inv]; exact hg.1
  let S' := PureApproximation.conjStratum S g⁻¹ hgi hgii
  have hS' : S'.IsSimple := PureApproximation.isSimple_conjStratum S g⁻¹ hgi hgii hS
  let T₀ : Stratum 𝒪[F] F V := ⟨T.chain, T.n, T.r - 1, T.b, by have := T.r_lt_n; omega,
    T.valuation_ge⟩
  have hT₀ : T₀.IsSimple := isSimple_lower T hT
  have hS'b : S'.b = (g : Module.End F V) * S.b * ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) := by
    change PureApproximation.conjAlgHom g⁻¹ S.b = _
    rw [PureApproximation.conjAlgHom_apply, inv_inv]
  have hequiv : S'.Equivalent T₀ := by
    apply Stratum.equivalent_of_sub_mem (S := S') (T := T₀)
    · exact hSc.symm
    · exact hSr.symm
    · change S'.b - T.b ∈ S.chain.endFiltration (-S.r)
      rw [hS'b, hSc, hSr, show -(T.r - 1) = 1 - T.r by ring]
      exact hgc
  have h5 := (stratumEquivalence F V S' T₀ hequiv).2.2.2 hS' hT₀
  obtain ⟨⟨hf, hn⟩, -⟩ := hS.1
  have hN := normalizingUnits_of_isField S.chain hf hn
  have hconj := PureApproximation.elementInvariants_conj S.chain hgi hgii S.b hN
  exact ⟨hconj.1.symm.trans h5.2.2.1, hconj.2.symm.trans h5.2.2.2⟩

/-- If the derived element `s(β − γ)` of a simple stratum `[𝔄,n,r−1,β]` in the fibre of
`[𝔄,n,r,γ]` is congruent modulo `𝔔^{1−r}` to the element of a simple stratum
`[𝔅,r,r−1,α]` over `E = F[γ]`, then `e(F[β]|F) = e(E|F) e(E[α]|E)` and
`f(F[β]|F) = f(E|F) f(E[α]|E)` (BK94 (1.12), by BK93 (2.2.8)). -/
theorem elementInvariants_of_derived_simple [FiniteDimensional F E] (T : Stratum 𝒪[F] F V)
    (hT : T.IsSimple) {γE : E} (hγE : subfieldEmbedding F E V γE = T.b)
    (hgen : Algebra.adjoin F ({γE} : Set E) = ⊤) (s : TameCorestriction 𝒪[F] F E V)
    (S : Stratum 𝒪[F] F V) (hSc : S.chain = T.chain) (_hSn : S.n = T.n)
    (hSr : S.r = T.r - 1) (hS : S.IsSimple) (hc : S.b - T.b ∈ T.chain.endFiltration (-T.r))
    (C : Stratum (subfieldIntegers F E) E V)
    (hClat : ∀ i, (C.chain.lattice i : Set V) = T.chain.lattice i) (hCn : C.n = T.r)
    (hCr : C.r = T.r - 1) (hC : C.IsSimple)
    (hsC : (s (S.b - T.b) - C.b).restrictScalars F ∈ T.chain.endFiltration (1 - T.r)) :
    letI := LocalField.FiniteExtension.valuativeRel F E
    elementRamificationIndex F S.b = subfieldRamificationIndex F E * elementRamificationIndex E C.b ∧
      elementResidueDegree F S.b = subfieldResidueDegree F E * elementResidueDegree E C.b := by
  have := T.chain.finiteDimensional
  set L := T.chain
  set c := S.b - T.b with hcdef
  have hE := PureApproximation.normalized_of_generated T hT.1 hγE hgen
  -- `s(c) − C.b ∈ 𝔔^{1−r}` on the chain of `C`.
  have hsC' : s c - C.b ∈ C.chain.endFiltration (-C.r) := by
    rw [hCr, show -(T.r - 1) = 1 - T.r by ring]
    exact (mem_endFiltration_restrictScalars hClat).mpr hsC
  -- `s(c) ∈ 𝔔^{−r}`.
  have hscmem : s c ∈ C.chain.endFiltration (-T.r) := by
    have h := (tameCorestriction F V E).2.2 s L hE (-T.r)
    have hmem : s c ∈ s '' (L.endFiltration (-T.r) : Set (Module.End F V)) := ⟨c, hc, rfl⟩
    rw [h] at hmem
    exact (mem_endFiltration_restrictScalars hClat).mpr hmem
  -- The valuation of `c` is exactly `−r`.
  have hval : L.valuation c = (-T.r : WithTop ℤ) := by
    apply LatticeChain.valuation_eq_of_mem_of_notMem _ hc
    intro hc1
    have h := (tameCorestriction F V E).2.2 s L hE (-T.r + 1)
    have hmem : s c ∈ s '' (L.endFiltration (-T.r + 1) : Set (Module.End F V)) := ⟨c, hc1, rfl⟩
    rw [h] at hmem
    have hsc1 : s c ∈ C.chain.endFiltration (-C.r) := by
      rw [hCr, show -(T.r - 1) = -T.r + 1 by ring]
      exact (mem_endFiltration_restrictScalars hClat).mpr hmem
    have hCb : C.b ∈ C.chain.endFiltration (-C.r) := by
      have := sub_mem hsc1 hsC'
      simpa using this
    have hle := PureApproximation.le_valuation_of_mem_subfield C.chain hCb
    rw [hC.1.2, hCn, hCr] at hle
    have := WithTop.coe_le_coe.mp (show ((-(T.r - 1) : ℤ) : WithTop ℤ) ≤ ((-T.r : ℤ) : WithTop ℤ)
      by exact_mod_cast hle)
    omega
  -- The derived stratum on the chain of `C`.
  let D : Stratum (subfieldIntegers F E) E V := ⟨C.chain, T.r, T.r - 1, s c, by omega, by
    have := PureApproximation.le_valuation_of_mem_subfield C.chain hscmem
    exact_mod_cast this⟩
  have hD : T.IsDerivedStratum E c s D :=
    ⟨hT, ⟨γE, hγE, hgen⟩, hc, hClat, rfl, rfl, rfl⟩
  have hDC : D.Equivalent C := by
    apply Stratum.equivalent_of_sub_mem (S := D) (T := C) rfl hCr
    change s c - C.b ∈ C.chain.endFiltration (-(T.r - 1))
    rw [← hCr]
    exact hsC'
  obtain ⟨T', hT'c, hT'n, hT'r, hT', hT'coset, he, hf, -⟩ :=
    refinement F V E T c s D C hD hval rfl (by rw [hCn]) hCr hDC hC
  have hST' : S.Equivalent T' := by
    unfold Stratum.Equivalent
    rw [hT'coset]
    unfold Stratum.coset
    rw [hSc, hSr]
    ext x
    simp only [Set.mem_ofPred_eq, hcdef, add_sub_cancel, show -(T.r - 1) = 1 - T.r by ring]
    exact Iff.rfl
  have h5 := (stratumEquivalence F V S T' hST').2.2.2 hS hT'
  have hCf : IsField (elementAlgebra C.b) := hC.1.1.1
  have hadj := subalgebraInvariants_adjoin_pair (F := F) hgen C.b hCf
  rw [hγE] at hadj
  exact ⟨h5.2.2.1.trans (he.trans hadj.1), h5.2.2.2.trans (hf.trans hadj.2)⟩

end Generic

section Element

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

set_option maxHeartbeats 1000000 in
/-- BK94 proof of (1.8), by BK93 (2.4.1): for a simple stratum `[𝔄,n,r−1,β]` in the fibre of
the simple stratum `[𝔄,n,r,γ]`, the derived element `s(β − γ)` is either in `𝔔^{1−r}` or
congruent modulo `𝔔^{1−r}` to the element of a simple stratum `[𝔅,r,r−1,α]` over `F[γ]`. -/
theorem exists_simple_of_derived_notMem (T : Stratum 𝒪[F] F V) (hT : T.IsSimple)
    (hf : IsField (elementAlgebra T.b)) :
    letI := hf.toField
    ∀ (s : TameCorestriction 𝒪[F] F (elementAlgebra T.b) V) (S : Stratum 𝒪[F] F V),
      S.chain = T.chain → S.n = T.n → S.r = T.r - 1 → S.IsSimple →
      S.b - T.b ∈ T.chain.endFiltration (-T.r) →
      (s (S.b - T.b)).restrictScalars F ∉ T.chain.endFiltration (1 - T.r) →
      ∃ C : Stratum (subfieldIntegers F (elementAlgebra T.b)) (elementAlgebra T.b) V,
        (∀ i, (C.chain.lattice i : Set V) = T.chain.lattice i) ∧ C.n = T.r ∧
          C.r = T.r - 1 ∧ C.IsSimple ∧
          (s (S.b - T.b) - C.b).restrictScalars F ∈ T.chain.endFiltration (1 - T.r) := by
  let E := elementAlgebra T.b
  let : Field E := hf.toField
  intro s S hSc hSn hSr hS hc hnot
  have := T.chain.finiteDimensional
  have : FiniteDimensional F E := inferInstanceAs (FiniteDimensional F (elementAlgebra T.b))
  set L := T.chain
  obtain ⟨Sc, Sn, Sr, Sb, hSlt, hSv⟩ := S
  change Sc = L at hSc
  change Sn = T.n at hSn
  change Sr = T.r - 1 at hSr
  subst hSc hSn hSr
  change Sb - T.b ∈ L.endFiltration (-T.r) at hc
  change (s (Sb - T.b)).restrictScalars F ∉ L.endFiltration (1 - T.r) at hnot
  change ∃ C : Stratum (subfieldIntegers F E) E V, _ ∧ _ ∧ _ ∧ _ ∧
    (s (Sb - T.b) - C.b).restrictScalars F ∈ L.endFiltration (1 - T.r)
  have hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ L.stabilizer := hT.1.1.2
  let S' : Stratum 𝒪[F] F V := ⟨L, T.n, T.r, Sb, T.r_lt_n, hSv⟩
  have hS'pure : S'.IsPure := hS.1
  have hS'T : S'.Equivalent T :=
    Stratum.equivalent_of_sub_mem (S := S') (T := T) rfl rfl hc
  have hk : criticalExponent L Sb ≤ ((-T.r : ℤ) : WithBot ℤ) := by
    have h := withBot_le_sub_one_of_lt hS.2
    change criticalExponent L Sb ≤ ((-(T.r - 1) - 1 : ℤ) : WithBot ℤ) at h
    rwa [show -(T.r - 1) - 1 = -T.r by ring] at h
  rcases eq_or_lt_of_le hk with hcrit | hlt
  · -- The critical case: BK93 (2.4.1)(iii).
    have hder := criticalDerivedStratum F V S' T hS'pure hcrit rfl rfl rfl hT hS'T
    have key : ∃ D C : Stratum (subfieldIntegers F E) E V,
        T.IsDerivedStratum E (Sb - T.b) s D ∧ C.chain = D.chain ∧ C.n = D.n ∧ C.r = D.r ∧
          D.Equivalent C ∧ C.IsSimple := hder hf s
    obtain ⟨D, C, hD, hCc, hCn, hCr, hDC, hC⟩ := key
    have hlat : ∀ i, (D.chain.lattice i : Set V) = L.lattice i := hD.2.2.2.1
    have hDn : D.n = T.r := hD.2.2.2.2.1
    have hDr : D.r = T.r - 1 := hD.2.2.2.2.2.1
    have hDb : D.b = s (Sb - T.b) := hD.2.2.2.2.2.2
    refine ⟨C, fun i => by rw [hCc]; exact hlat i, by rw [hCn, hDn], by rw [hCr, hDr], hC, ?_⟩
    have h1 := Stratum.sub_mem_of_equivalent hDC
    have h2 := (mem_endFiltration_restrictScalars hlat).mp h1
    have hDb' : D.b = s (Sb - T.b) := hDb
    have hDr' : -D.r = 1 - T.r := by omega
    rw [hDr', hDb'] at h2
    exact h2
  · -- The noncritical case: BK93 (2.4.1)(ii)(c), and a scalar simple stratum.
    have hS'' : S'.IsSimple := ⟨hS'pure, hlt⟩
    obtain ⟨δ, hδ⟩ := simpleStratumCorestrictionCongruence F V T S' rfl rfl rfl hT hS''
      hS'T.symm hf s
    change (s (T.b - Sb)).restrictScalars F - subfieldEmbedding F E V δ ∈
      L.endFiltration (1 - T.r) at hδ
    have hneg : (s (T.b - Sb)).restrictScalars F = -(s (Sb - T.b)).restrictScalars F := by
      rw [show T.b - Sb = -(Sb - T.b) by abel, map_neg]
      rfl
    rw [hneg] at hδ
    have hδ' : (s (Sb - T.b)).restrictScalars F - subfieldEmbedding F E V (-δ) ∈
        L.endFiltration (1 - T.r) := by
      have := neg_mem hδ
      rw [map_neg]
      convert this using 1
      abel
    have hsc : (s (Sb - T.b)).restrictScalars F ∈ L.endFiltration (-T.r) := by
      have h := (tameCorestriction F V E).2.2 s L hE (-T.r)
      have hmem : s (Sb - T.b) ∈ s '' (L.endFiltration (-T.r) : Set (Module.End F V)) :=
        ⟨_, hc, rfl⟩
      rw [h] at hmem
      exact hmem
    have hx1 : subfieldEmbedding F E V (-δ) ∈ L.endFiltration (-T.r) := by
      have := sub_mem hsc (L.endFiltration_antitone (by omega) hδ')
      simpa using this
    have hx2 : subfieldEmbedding F E V (-δ) ∉ L.endFiltration (-T.r + 1) := by
      intro hx
      apply hnot
      have := add_mem hδ' (show subfieldEmbedding F E V (-δ) ∈ L.endFiltration (1 - T.r) by
        rwa [show 1 - T.r = -T.r + 1 by ring])
      simpa using this
    have hv := LatticeChain.valuation_eq_of_mem_of_notMem L hx1 hx2
    obtain ⟨C, hlat, hCn, hCr, hCb, hC⟩ :=
      PureApproximation.exists_scalar_simple L hE (ρ := T.r) (by rw [hv])
    refine ⟨C, hlat, hCn, hCr, hC, ?_⟩
    rw [hCb, restrictScalars_sub, PureApproximation.restrictScalars_algebraMap]
    exact hδ'

end Element

end Langlands.BushnellKutzko.SimpleStratumLabel
