import Langlands.BushnellKutzko.PureStratumApproximationAssembly
import Langlands.BushnellKutzko.SplitObstructionIdempotents
import Langlands.BushnellKutzko.AdjointExactnessProof
import Langlands.BushnellKutzko.TameCorestrictionProof
import Langlands.BushnellKutzko.RefinementProof

/-! # Proof of BK93 (2.3.12): a split derived stratum obstructs field generation

`Langlands.BushnellKutzko.PureApproximation.splitObstructionPremise` proves
`SplitObstructionPremise`: for a simple stratum `[𝔄, n, r, β]`, `b ∈ 𝔓^{−r}` and a tame
corestriction `s`, if the derived stratum `[𝔅, r, r−1, s(b)]` is split fundamental, then
`F[β + b]` is not a field (Bushnell–Kutzko (1993), (2.3.12), printed pp. 61–64).
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

open SplitObstruction

universe uF uV uE

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **BK93 (2.3.12).** A split derived stratum prevents `F[β + b]` from being a field. -/
theorem splitObstructionPremise : SplitObstructionPremise.{uF, uV, uE} := by
  intro F _ _ _ _ V _ _ _ E _ _ _ _ S b s D hD hsplit
  classical
  obtain ⟨hS, ⟨β₀, hβ₀S, hβ₀gen⟩, hb, hDlat, hDn, hDr, hDb⟩ := hD
  obtain ⟨⟨hSfield, hSnorm⟩, hSval⟩ := hS.1
  have hSk := hS.2
  have hVnt := S.chain.nontrivial_space
  -- the field `E` normalizes the chain
  have hSN : NormalizingUnits S.chain (elementAlgebra S.b) :=
    normalizingUnits_of_isField S.chain hSfield hSnorm
  have hℓinj : Function.Injective (subfieldEmbedding F E V) :=
    (subfieldEmbedding F E V).toRingHom.injective
  have hEmem : ∀ e : E, subfieldEmbedding F E V e ∈ elementAlgebra S.b := by
    intro e
    have h1 : subfieldEmbedding F E V e ∈
        (Algebra.adjoin F ({β₀} : Set E)).map (subfieldEmbedding F E V) :=
      Subalgebra.mem_map.mpr ⟨e, by rw [hβ₀gen]; exact Algebra.mem_top, rfl⟩
    rw [AlgHom.map_adjoin_singleton, hβ₀S] at h1
    exact h1
  have hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer := by
    intro a
    obtain ⟨g, hg, hgs⟩ := hSN _ (hEmem a)
      (fun h0 => a.ne_zero (hℓinj (h0.trans (map_zero _).symm)))
    have heq : subfieldUnits F E V a = g :=
      Units.ext ((coe_subfieldUnits F E V a).trans hg.symm)
    rw [heq]
    exact hgs
  have hFE : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  -- notation
  set 𝓛 := S.chain with h𝓛
  set r := S.r with hr
  set β := S.b with hβdef
  -- the two filtrations agree
  have hlat : ∀ i v, v ∈ D.chain.lattice i ↔ v ∈ 𝓛.lattice i := fun i v =>
    Set.ext_iff.mp (hDlat i) v
  have hQ : ∀ (n : ℤ) (x : Module.End E V),
      x ∈ D.chain.endFiltration n ↔ x.restrictScalars F ∈ 𝓛.endFiltration n := by
    intro n x
    simp only [LatticeChain.mem_endFiltration, hlat]
    rfl
  have hres_inj : Function.Injective (fun x : Module.End E V => x.restrictScalars F) :=
    LinearMap.restrictScalars_injective F
  have hres_mul : ∀ x y : Module.End E V,
      (x * y).restrictScalars F = x.restrictScalars F * y.restrictScalars F := fun _ _ => rfl
  -- the corestriction preserves the filtration and is surjective
  have hTC := (tameCorestriction F V E).2.2 s 𝓛 hE
  have hsP : ∀ (j : ℤ) (y : Module.End F V), y ∈ 𝓛.endFiltration j →
      (s y).restrictScalars F ∈ 𝓛.endFiltration j := by
    intro j y hy
    have hmem : s y ∈ s '' (𝓛.endFiltration j : Set (Module.End F V)) := ⟨y, hy, rfl⟩
    rw [hTC j] at hmem
    exact hmem
  have hssurj : Function.Surjective s := by
    intro w
    obtain ⟨k, hk⟩ := SplitObstruction.exists_mem_endFiltration 𝓛 (w.restrictScalars F)
    have hw : w ∈ {c : Module.End E V | c.restrictScalars F ∈ 𝓛.endFiltration k} := hk
    rw [← hTC k] at hw
    obtain ⟨y, -, hy⟩ := hw
    exact ⟨y, hy⟩
  -- the derived element
  set a := s b with ha
  have haQ : a ∈ D.chain.endFiltration (-D.n) := by
    rw [hDn, hQ]
    exact hsP _ _ hb
  have hDb' : D.b = a := hDb
  -- the splitting idempotents over `E`
  obtain ⟨e₁, e₂, hsum, h12, hne₁, hne₂, he₁O, he₂O, hc₁, hc₂, hgr⟩ :=
    SplitObstruction.exists_split_idempotents D hsplit (by rw [hDb']; exact haQ)
  rw [hDb', hDn] at hgr
  rw [hDb'] at hc₁ hc₂
  -- block surjectivity of the commutator with `a` over `E`
  have hB : ∀ (j : ℤ) (w : Module.End E V), w ∈ D.chain.endFiltration (j - r) →
      e₁ * w * e₂ = w → ∃ z : Module.End E V, z ∈ D.chain.endFiltration j ∧
        e₁ * z * e₂ = z ∧ a * z - z * a = w := by
    have hfdE : FiniteDimensional E V := D.chain.finiteDimensional
    have h21 : e₂ * e₁ = 0 := SplitObstruction.mul_eq_zero_of_complement hsum h12
    have h11 : e₁ * e₁ = e₁ := SplitObstruction.idempotent_left_of_complement hsum h12
    have h22 : e₂ * e₂ = e₂ := SplitObstruction.idempotent_right_of_complement hsum h12
    let WE : Submodule E (Module.End E V) :=
      { carrier := {x | e₁ * x * e₂ = x}
        add_mem' := by
          intro x y hx hy
          change e₁ * (x + y) * e₂ = x + y
          change e₁ * x * e₂ = x at hx
          change e₁ * y * e₂ = y at hy
          rw [mul_add, add_mul, hx, hy]
        zero_mem' := by
          change e₁ * 0 * e₂ = 0
          simp
        smul_mem' := by
          intro t x hx
          change e₁ * (t • x) * e₂ = t • x
          change e₁ * x * e₂ = x at hx
          rw [mul_smul_comm, smul_mul_assoc, hx] }
    have hWE : ∀ x ∈ WE, a * x - x * a ∈ WE := by
      intro x hx
      change e₁ * (a * x - x * a) * e₂ = a * x - x * a
      change e₁ * x * e₂ = x at hx
      have h1 : e₁ * a * x * e₂ = a * (e₁ * x * e₂) := by
        rw [hc₁.eq]
        simp only [mul_assoc]
      have h2 : e₁ * x * a * e₂ = (e₁ * x * e₂) * a := by
        rw [mul_assoc (e₁ * x) a e₂, ← hc₂.eq]
        simp only [mul_assoc]
      calc e₁ * (a * x - x * a) * e₂ = e₁ * a * x * e₂ - e₁ * x * a * e₂ := by noncomm_ring
        _ = a * x - x * a := by rw [h1, h2, hx]
    let dA : WE →ₗ[E] WE :=
      (LinearMap.mulLeft E a - LinearMap.mulRight E a).restrict hWE
    have hdA : ∀ x : WE, ((dA x : WE) : Module.End E V) = a * x - x * a := fun _ => rfl
    -- graded injectivity gives injectivity
    have hstep : ∀ (k : ℤ) (z : Module.End E V), z ∈ D.chain.endFiltration k →
        e₁ * z * e₂ = z → ∀ j : ℤ, a * z - z * a ∈ D.chain.endFiltration (j - r) →
        ∀ m : ℕ, k + m ≤ j → z ∈ D.chain.endFiltration (k + m) := by
      intro k z hz hz12 j hj m
      induction m with
      | zero => intro _; simpa using hz
      | succ m ih =>
        intro hm
        have hzm := ih (by omega)
        have hc : a * z - z * a ∈ D.chain.endFiltration (k + m - r + 1) :=
          D.chain.endFiltration_antitone (by omega) hj
        have h := hgr (k + m) z hzm hz12 hc
        push_cast
        simpa [add_assoc] using h
    have hinj : Function.Injective dA := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      rw [LinearMap.mem_ker] at hx
      have hx0 : a * (x : Module.End E V) - x * a = 0 := by
        rw [← hdA, hx]
        rfl
      obtain ⟨k, hk⟩ := SplitObstruction.exists_mem_endFiltration 𝓛 ((x : Module.End E V).restrictScalars F)
      have hres : (x : Module.End E V).restrictScalars F = 0 := by
        apply SplitObstruction.eq_zero_of_forall_ge_mem 𝓛 (k₀ := k)
        intro m
        rw [← hQ]
        exact hstep k x ((hQ k _).mpr hk) x.2 (k + m) (by rw [hx0]; exact zero_mem _) m
          le_rfl
      apply Subtype.ext
      apply LinearMap.restrictScalars_injective F
      rw [hres]
      rfl
    have hsurj : Function.Surjective dA := LinearMap.injective_iff_surjective.mp hinj
    intro j w hw hw12
    obtain ⟨z, hz⟩ := hsurj ⟨w, hw12⟩
    have hzw : a * (z : Module.End E V) - z * a = w := by
      rw [← hdA, hz]
    obtain ⟨k, hk⟩ := SplitObstruction.exists_mem_endFiltration 𝓛 ((z : Module.End E V).restrictScalars F)
    have hzk : (z : Module.End E V) ∈ D.chain.endFiltration k := (hQ k _).mpr hk
    refine ⟨z, ?_, z.2, hzw⟩
    by_cases hjk : j ≤ k
    · exact D.chain.endFiltration_antitone hjk hzk
    · have h := hstep k z hzk z.2 j (by rw [hzw]; exact hw) (j - k).toNat
        (by rw [Int.toNat_of_nonneg (by omega)]; omega)
      rwa [Int.toNat_of_nonneg (by omega), add_sub_cancel] at h
  -- the idempotents over `F`
  set ε₁ := e₁.restrictScalars F with hε₁def
  set ε₂ := e₂.restrictScalars F with hε₂def
  have hεsum : ε₁ + ε₂ = 1 := by
    rw [hε₁def, hε₂def, ← LinearMap.restrictScalars_add, hsum]
    rfl
  have hε12 : ε₁ * ε₂ = 0 := by
    rw [hε₁def, hε₂def, ← hres_mul, h12]
    rfl
  have hε21 : ε₂ * ε₁ = 0 := SplitObstruction.mul_eq_zero_of_complement hεsum hε12
  have hε11 : ε₁ * ε₁ = ε₁ := SplitObstruction.idempotent_left_of_complement hεsum hε12
  have hε22 : ε₂ * ε₂ = ε₂ := SplitObstruction.idempotent_right_of_complement hεsum hε12
  have hε₁P : ε₁ ∈ 𝓛.endFiltration 0 := (hQ 0 e₁).mp he₁O
  have hε₂P : ε₂ ∈ 𝓛.endFiltration 0 := (hQ 0 e₂).mp he₂O
  have hε₁ne : ε₁ ≠ 0 := fun h => hne₁ (LinearMap.restrictScalars_injective F
    (by rw [← hε₁def, h]; rfl))
  have hε₂ne : ε₂ ≠ 0 := fun h => hne₂ (LinearMap.restrictScalars_injective F
    (by rw [← hε₂def, h]; rfl))
  -- `β` is a scalar of `E`
  have hβ : β = (algebraMap E (Module.End E V) β₀).restrictScalars F := by
    rw [← hβ₀S]
    rfl
  have hβcomm : ∀ x : Module.End E V, β * x.restrictScalars F = x.restrictScalars F * β := by
    intro x
    rw [hβ, ← hres_mul, ← hres_mul, Algebra.commutes]
  have hβε₁ : β * ε₁ = ε₁ * β := hβcomm e₁
  have hβε₂ : β * ε₂ = ε₂ * β := hβcomm e₂
  -- the corestriction on blocks
  have hs_left : ∀ (x : Module.End E V) (y : Module.End F V),
      s (x.restrictScalars F * y) = x * s y := fun x y => s.map_mul_left x y
  have hs_right : ∀ (y : Module.End F V) (x : Module.End E V),
      s (y * x.restrictScalars F) = s y * x := fun y x => s.map_mul_right y x
  have hs_add : ∀ y y' : Module.End F V, s (y + y') = s y + s y' := fun y y' =>
    map_add s.toAddMonoidHom y y'
  have hs_sub : ∀ y y' : Module.End F V, s (y - y') = s y - s y' := fun y y' =>
    map_sub s.toAddMonoidHom y y'
  -- `s(β)` is central in `B`
  have hsβ : ∀ x : Module.End E V, s β * x = x * s β := by
    intro x
    have h1 : s β = algebraMap E (Module.End E V) β₀ * s 1 := by
      rw [hβ, ← hs_left, mul_one]
    have hcen : ∀ y : Module.End E V, y * s 1 = s 1 * y := by
      intro y
      rw [← hs_left, mul_one, ← hs_right, one_mul]
    rw [h1, mul_assoc, ← hcen x, ← mul_assoc, Algebra.commutes, mul_assoc]
  -- the block filtration and the block commutator
  set M := SplitObstruction.blockFiltration 𝓛 ε₁ ε₂ with hMdef
  set γ := S.b + b with hγdef
  set Dc := SplitObstruction.blockCommutator ε₁ ε₂ γ with hDcdef
  have hDform : ∀ x : Module.End F V, ε₁ * x = x → x * ε₂ = x →
      Dc x = (β * x - x * β) + (ε₁ * b * ε₁ * x - x * (ε₂ * b * ε₂)) := by
    intro x hx1 hx2
    rw [hDcdef, SplitObstruction.blockCommutator_apply, hγdef, ← hβdef]
    have h1 : ε₁ * (β + b) * ε₁ * x = β * x + ε₁ * b * ε₁ * x := by
      rw [mul_add, add_mul, add_mul, ← hβε₁, mul_assoc β ε₁ ε₁, hε11, mul_assoc β ε₁ x, hx1]
    have h2 : x * (ε₂ * (β + b) * ε₂) = x * β + x * (ε₂ * b * ε₂) := by
      rw [mul_add, add_mul, mul_add, ← hβε₂, mul_assoc β ε₂ ε₂, hε22, hβε₂, ← mul_assoc,
        hx2]
    rw [h1, h2]
    abel
  have hblock : ∀ u : Module.End F V,
      ε₁ * (β * u - u * β) * ε₂ = β * (ε₁ * u * ε₂) - ε₁ * u * ε₂ * β := by
    intro u
    have h1 : ε₁ * (β * u) * ε₂ = β * (ε₁ * u * ε₂) := by
      calc ε₁ * (β * u) * ε₂ = (ε₁ * β) * u * ε₂ := by simp only [mul_assoc]
        _ = (β * ε₁) * u * ε₂ := by rw [hβε₁]
        _ = β * (ε₁ * u * ε₂) := by simp only [mul_assoc]
    have h2 : ε₁ * (u * β) * ε₂ = ε₁ * u * ε₂ * β := by
      calc ε₁ * (u * β) * ε₂ = ε₁ * u * (β * ε₂) := by simp only [mul_assoc]
        _ = ε₁ * u * (ε₂ * β) := by rw [hβε₂]
        _ = ε₁ * u * ε₂ * β := by simp only [mul_assoc]
    rw [mul_sub, sub_mul, h1, h2]
  have hpert : ∀ (k : ℤ) (x : Module.End F V), x ∈ 𝓛.endFiltration k →
      ε₁ * b * ε₁ * x - x * (ε₂ * b * ε₂) ∈ 𝓛.endFiltration (k - r) := by
    intro k x hx
    apply sub_mem
    · have h := 𝓛.mul_mem_endFiltration
        (𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hε₁P hb) hε₁P) hx
      exact 𝓛.endFiltration_antitone (by omega) h
    · have h := 𝓛.mul_mem_endFiltration hx
        (𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hε₂P hb) hε₂P)
      exact 𝓛.endFiltration_antitone (by omega) h
  have hpertW : ∀ x : Module.End F V, ε₁ * x * ε₂ = x →
      ε₁ * (ε₁ * b * ε₁ * x - x * (ε₂ * b * ε₂)) * ε₂ = ε₁ * b * ε₁ * x - x * (ε₂ * b * ε₂) := by
    intro x hx
    have hx2 : x * ε₂ = x := by rw [← hx, mul_assoc, hε22]
    have hx1 : ε₁ * x = x := by rw [← hx, ← mul_assoc, ← mul_assoc, hε11]
    rw [mul_sub, sub_mul]
    congr 1
    · rw [show ε₁ * (ε₁ * b * ε₁ * x) * ε₂ = (ε₁ * ε₁) * b * ε₁ * (x * ε₂) by
        simp only [mul_assoc], hε11, hx2]
    · rw [show ε₁ * (x * (ε₂ * b * ε₂)) * ε₂ = (ε₁ * x) * (ε₂ * b * (ε₂ * ε₂)) by
        simp only [mul_assoc], hε22, hx1]
  -- exactness of the adjoint sequence
  have hexact : ∀ (j : ℤ) (y : Module.End F V), y ∈ 𝓛.endFiltration j → s y = 0 →
      ∃ w ∈ 𝓛.endFiltration (j + r + 1), β * w - w * β = y := by
    intro j y hy hsy
    by_cases hscal : ∃ c : F, algebraMap F E c = β₀
    · obtain ⟨c, hc⟩ := hscal
      have hker : y ∈ s.toLinearMap.ker := hsy
      rw [← TameCorestriction.range_adjointMap_eq_ker s β₀ hβ₀gen hssurj] at hker
      obtain ⟨x, hx⟩ := hker
      have hβc : subfieldEmbedding F E V β₀ = algebraMap F (Module.End F V) c := by
        rw [← hc, AlgHom.commutes]
      have hzero : y = 0 := by
        rw [← hx]
        change subfieldEmbedding F E V β₀ * x - x * subfieldEmbedding F E V β₀ = 0
        rw [hβc, Algebra.commutes, sub_self]
      exact ⟨0, zero_mem _, by rw [hzero]; simp⟩
    · have hex := adjointExactness F V E 𝓛 β₀ hβ₀gen hscal hE
      dsimp only at hex
      have hcrit : criticalExponent 𝓛 (subfieldEmbedding F E V β₀) ≤ ((-r - 1 : ℤ) : WithBot ℤ) := by
        rw [hβ₀S]
        have hlt := hSk
        revert hlt
        generalize criticalExponent 𝓛 β = c
        intro hlt
        induction c using WithBot.recBotCoe with
        | bot => exact bot_le
        | coe c =>
          rw [WithBot.coe_lt_coe] at hlt
          exact WithBot.coe_le_coe.mpr (by omega)
      have h3 := ((hex.2.2.2.2 s (j + r + 1) (-r - 1) 1 hcrit le_rfl).2.2.1)
      have hmid := h3.2.2.2.2.2.2.2.2.2
      have hyP : y ∈ (𝓛.endFiltration (j + r + 1 + (-r - 1))).toAddSubgroup := by
        rw [show j + r + 1 + (-r - 1) = j by ring]
        exact hy
      obtain ⟨x, hx, hyx⟩ := (hmid y hyP).mp (by
        change (s y).restrictScalars F ∈ (⊥ : AddSubgroup (Module.End F V))
        rw [hsy]
        rfl)
      have hxP : x ∈ 𝓛.endFiltration (j + r + 1) := by
        have hle : centralizerLattice 𝓛 (subfieldEmbedding F E V β₀) (j + r + 1) *
            adjointLattice 𝓛 (subfieldEmbedding F E V β₀) (-r - 1) ≤
              𝓛.endFiltration (j + r + 1) := by
          apply Submodule.mul_le.mpr
          intro u hu v hv
          have h := 𝓛.mul_mem_endFiltration hu.1 hv.1
          simpa using h
        exact hle hx
      refine ⟨x, hxP, ?_⟩
      have hyx' : y - adjointMap 𝒪[F] (subfieldEmbedding F E V β₀) x = 0 := hyx
      rw [sub_eq_zero] at hyx'
      rw [hyx']
      change β * x - x * β = subfieldEmbedding F E V β₀ * x - x * subfieldEmbedding F E V β₀
      rw [hβ₀S]
  -- Lemma (2.3.13): graded surjectivity of the block commutator
  have hC : ∀ i : ℤ, ∀ y ∈ M (i - r), ∃ x ∈ M i, y - Dc x ∈ M (i + 1 - r) := by
    intro i y hy
    obtain ⟨hyP, hy12⟩ := hy
    -- correct the corestriction with the block solution over `E`
    have hsyQ : s y ∈ D.chain.endFiltration (i - r) := (hQ _ _).mpr (hsP _ _ hyP)
    have hsy12 : e₁ * s y * e₂ = s y := by
      rw [← hs_left, ← hs_right, hy12]
    obtain ⟨z, hzQ, hz12, hza⟩ := hB i (s y) hsyQ hsy12
    set zt := z.restrictScalars F with hztdef
    have hzt12 : ε₁ * zt * ε₂ = zt := by
      rw [hztdef, hε₁def, hε₂def, ← hres_mul, ← hres_mul, hz12]
    have hzt1 : ε₁ * zt = zt := by rw [← hzt12, ← mul_assoc, ← mul_assoc, hε11]
    have hzt2 : zt * ε₂ = zt := by rw [← hzt12, mul_assoc, hε22]
    have hzP : zt ∈ 𝓛.endFiltration i := (hQ i z).mp hzQ
    have hDz : Dc zt = ε₁ * b * ε₁ * zt - zt * (ε₂ * b * ε₂) := by
      rw [hDform zt hzt1 hzt2, hβcomm z, sub_self, zero_add]
    -- `s(D z) = a z − z a = s y`
    have hsDz : s (Dc zt) = s y := by
      rw [hDcdef, SplitObstruction.blockCommutator_apply, hs_sub, hztdef, hs_right, hs_left, hγdef]
      rw [show ε₁ * (S.b + b) * ε₁ = e₁.restrictScalars F * ((S.b + b) * e₁.restrictScalars F) by
        rw [hε₁def]; simp only [mul_assoc]]
      rw [show ε₂ * (S.b + b) * ε₂ = e₂.restrictScalars F * ((S.b + b) * e₂.restrictScalars F) by
        rw [hε₂def]; simp only [mul_assoc]]
      rw [hs_left, hs_right, hs_left, hs_right, hs_add, ← hβdef, ← ha]
      have hz1 : e₁ * z = z := by rw [← hz12, ← mul_assoc, ← mul_assoc,
        SplitObstruction.idempotent_left_of_complement hsum h12]
      have hz2 : z * e₂ = z := by rw [← hz12, mul_assoc, SplitObstruction.idempotent_right_of_complement hsum h12]
      rw [← hza]
      have hA : e₁ * (s β + a) * z = s β * z + a * z := by
        rw [mul_add, add_mul, ← hsβ e₁, mul_assoc (s β) e₁ z, hz1, hc₁.eq, mul_assoc a e₁ z, hz1]
      have hB : z * (s β + a) * e₂ = s β * z + z * a := by
        rw [mul_add, add_mul, ← hsβ z, mul_assoc (s β) z e₂, hz2, mul_assoc z a e₂, ← hc₂.eq,
          ← mul_assoc z e₂ a, hz2]
      calc e₁ * (s β + a) * e₁ * z - z * (e₂ * (s β + a) * e₂)
          = e₁ * (s β + a) * (e₁ * z) - (z * e₂) * (s β + a) * e₂ := by
            simp only [mul_assoc]
        _ = e₁ * (s β + a) * z - z * (s β + a) * e₂ := by rw [hz1, hz2]
        _ = (s β * z + a * z) - (s β * z + z * a) := by rw [hA, hB]
        _ = a * z - z * a := by abel
    -- the remaining error lies in the kernel of the corestriction
    have hrem : y - Dc zt ∈ 𝓛.endFiltration (i - r) := by
      apply sub_mem hyP
      rw [hDz]
      exact hpert i zt hzP
    have hsrem : s (y - Dc zt) = 0 := by rw [hs_sub, hsDz, sub_self]
    obtain ⟨w, hwP, hwy⟩ := hexact (i - r) (y - Dc zt) hrem hsrem
    set x' := ε₁ * w * ε₂ with hx'def
    have hx'P : x' ∈ 𝓛.endFiltration (i + 1) := by
      have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hε₁P hwP) hε₂P
      exact 𝓛.endFiltration_antitone (by omega) h
    have hx'1 : ε₁ * x' = x' := by rw [hx'def, ← mul_assoc, ← mul_assoc, hε11]
    have hx'2 : x' * ε₂ = x' := by rw [hx'def, mul_assoc, hε22]
    have hDzW : ε₁ * Dc zt * ε₂ = Dc zt := by
      rw [hDz]
      exact hpertW zt hzt12
    have hremW : ε₁ * (y - Dc zt) * ε₂ = y - Dc zt := by
      rw [mul_sub, sub_mul, hy12, hDzW]
    have hβx' : β * x' - x' * β = y - Dc zt := by
      rw [hx'def, ← hblock, hwy, hremW]
    refine ⟨zt + x', ⟨add_mem hzP (𝓛.endFiltration_antitone (by omega) hx'P), ?_⟩, ?_⟩
    · change ε₁ * (zt + x') * ε₂ = zt + x'
      rw [mul_add, add_mul, hzt12, show ε₁ * x' * ε₂ = x' by rw [hx'1, hx'2]]
    · have hDx' := hDform x' hx'1 hx'2
      rw [hβx'] at hDx'
      have heq : y - Dc (zt + x') = -(ε₁ * b * ε₁ * x' - x' * (ε₂ * b * ε₂)) := by
        rw [map_add, hDx']
        abel
      rw [heq]
      refine ⟨neg_mem (𝓛.endFiltration_antitone (by omega) (hpert (i + 1) x' hx'P)), ?_⟩
      change ε₁ * -(ε₁ * b * ε₁ * x' - x' * (ε₂ * b * ε₂)) * ε₂ = _
      rw [mul_neg, neg_mul, hpertW x' (by rw [hx'1, hx'2])]
  -- Corollary (2.3.15): surjectivity on every step
  have hDsurj := SplitObstruction.blockFiltration_surjective 𝓛 ε₁ ε₂ (D := Dc) hC
  -- (2.3.14): the off-diagonal block of `γ` is approximately a commutator
  have hy : ∃ x ∈ M 1, ε₁ * γ * ε₂ - Dc x ∈ M (1 - r) := by
    have hγ12 : ε₁ * γ * ε₂ = ε₁ * b * ε₂ := by
      rw [hγdef, ← hβdef, mul_add, add_mul, ← hβε₁, mul_assoc β ε₁ ε₂, hε12, mul_zero,
        zero_add]
    have hyP : ε₁ * b * ε₂ ∈ 𝓛.endFiltration (-r) := by
      have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hε₁P hb) hε₂P
      simpa using h
    have hsy : s (ε₁ * b * ε₂) = 0 := by
      rw [hs_right, hs_left, ← ha, hc₁.eq, mul_assoc, h12, mul_zero]
    obtain ⟨w, hwP, hwy⟩ := hexact (-r) (ε₁ * b * ε₂) hyP hsy
    set x' := ε₁ * w * ε₂ with hx'def
    have hx'P : x' ∈ 𝓛.endFiltration 1 := by
      have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hε₁P hwP) hε₂P
      exact 𝓛.endFiltration_antitone (by omega) h
    have hx'1 : ε₁ * x' = x' := by rw [hx'def, ← mul_assoc, ← mul_assoc, hε11]
    have hx'2 : x' * ε₂ = x' := by rw [hx'def, mul_assoc, hε22]
    have hW : ε₁ * (ε₁ * b * ε₂) * ε₂ = ε₁ * b * ε₂ := by
      rw [show ε₁ * (ε₁ * b * ε₂) * ε₂ = (ε₁ * ε₁) * b * (ε₂ * ε₂) by simp only [mul_assoc],
        hε11, hε22]
    have hβx' : β * x' - x' * β = ε₁ * b * ε₂ := by
      rw [hx'def, ← hblock, hwy, hW]
    refine ⟨x', ⟨hx'P, show ε₁ * x' * ε₂ = x' by rw [hx'1, hx'2]⟩, ?_⟩
    have hDx' := hDform x' hx'1 hx'2
    rw [hβx'] at hDx'
    have heq : ε₁ * γ * ε₂ - Dc x' = -(ε₁ * b * ε₁ * x' - x' * (ε₂ * b * ε₂)) := by
      rw [hγ12, hDx']
      abel
    rw [heq]
    refine ⟨neg_mem (𝓛.endFiltration_antitone (by omega) (hpert 1 x' hx'P)), ?_⟩
    change ε₁ * -(ε₁ * b * ε₁ * x' - x' * (ε₂ * b * ε₂)) * ε₂ = _
    rw [mul_neg, neg_mul, hpertW x' (by rw [hx'1, hx'2])]
  -- the `(2,1)`-block of `γ`
  have hz : ε₂ * γ * ε₁ ∈ 𝓛.endFiltration (-r) := by
    have hγ21 : ε₂ * γ * ε₁ = ε₂ * b * ε₁ := by
      rw [hγdef, ← hβdef, mul_add, add_mul, ← hβε₂, mul_assoc β ε₂ ε₁, hε21, mul_zero,
        zero_add]
    rw [hγ21]
    have h := 𝓛.mul_mem_endFiltration (𝓛.mul_mem_endFiltration hε₂P hb) hε₁P
    simpa using h
  exact SplitObstruction.not_isField_of_blockCommutator 𝓛 hεsum hε12 hε₁P hε₂P hε₁ne hε₂ne hz hDsurj hy

end Langlands.BushnellKutzko.PureApproximation
