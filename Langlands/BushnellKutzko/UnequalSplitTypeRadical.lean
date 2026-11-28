import Langlands.BushnellKutzko.UnequalSplitTypeLeviTransfer
import Langlands.BushnellKutzko.TameCorestrictionKernel
import Langlands.BushnellKutzko.SimpleHLayerCentralizer

/-! # The radical of the shallow lower-corner pairing

On the lower corner of the H layer at depth `m`, orthogonality to both
`𝔔^{r−m}𝔑_{−r}` and `𝔅` under the commutator pairing for `β + c` forces depth
`m+1` when the corestricted commutator is injective on the graded lower corner. -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- `tr(y (b x − x b)) = tr(−(b y − y b) x)`. -/
theorem trace_mul_commutator (b x y : A) :
    LinearMap.trace F V (y * (b * x - x * b)) = LinearMap.trace F V (-((b * y - y * b) * x)) := by
  have h : LinearMap.trace F V (y * x * b) = LinearMap.trace F V (b * y * x) := by
    rw [LinearMap.trace_mul_comm, ← mul_assoc]
  rw [mul_sub, map_sub, ← mul_assoc, ← mul_assoc, h, map_neg, sub_mul, map_sub, neg_sub]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- An endomorphism commuting with the action of `E` commutes with the image of every
element of `E`. -/
theorem commute_of_mem_fieldCommutant {E : Type*} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] {y : A} (hy : y ∈ StratumEquivalence.fieldCommutant E) (a : E) :
    y * subfieldEmbedding F E V a = subfieldEmbedding F E V a * y := by
  ext v
  exact hy a v

/-- **Orthogonality to `𝔔^{r−m}𝔑_{−r}` and `𝔅`.** An element `x ∈ e₂ 𝔥^m e₁` orthogonal to both
lattices lies in `𝔥^{m+1}`. -/
theorem mem_simpleHLayer_succ_of_orthogonal {E : Type*} [Field E] [Algebra F E] [Module E V]
    [IsScalarTower F E V] (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hs : S.IsSimple)
    (q : S.DefiningSequenceChoice) {βE : E}
    (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    (i : ℕ) (hcrit : ((i + 1 : ℕ) : ℤ) < finiteCriticalDepth S.chain S.n S.b)
    {c : A} (hc : c ∈ S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)))
    {e₁ e₂ : A} (he₁B : e₁ ∈ centralizerLattice S.chain S.b 0)
    (he₂B : e₂ ∈ centralizerLattice S.chain S.b 0) (he₁₁ : e₁ * e₁ = e₁) (he₂₂ : e₂ * e₂ = e₂)
    (hinj : ∀ x : A, x ∈ centralizerLattice S.chain S.b ((i + 1 : ℕ) : ℤ) → e₂ * x * e₁ = x →
      (s (c * x - x * c)).restrictScalars F ∈ S.chain.endFiltration 1 →
      x ∈ S.chain.endFiltration ((i + 1 + 1 : ℕ) : ℤ))
    {x : A} (hx : x ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1)) (hx21 : e₂ * x * e₁ = x)
    (h1 : ∀ y ∈ centralizerLattice S.chain S.b
        (finiteCriticalDepth S.chain S.n S.b - ((i + 1 : ℕ) : ℤ)) *
        adjointLattice S.chain S.b (-finiteCriticalDepth S.chain S.n S.b),
      traceCharacter ψF (y * ((S.b + c) * x - x * (S.b + c))) = 1)
    (h2 : ∀ y ∈ centralizerLattice S.chain S.b 0,
      traceCharacter ψF (y * ((S.b + c) * x - x * (S.b + c))) = 1) :
    x ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1 + 1) := by
  have := S.chain.finiteDimensional
  set r := finiteCriticalDepth S.chain S.n S.b with hr
  have hxP : x ∈ S.chain.endFiltration ((i + 1 : ℕ) : ℤ) := hx.2
  have hP1 : ∀ {u v : A} {a b : ℤ}, u ∈ S.chain.endFiltration a → v ∈ S.chain.endFiltration b →
      1 ≤ a + b → u * v ∈ S.chain.endFiltration 1 := fun hu hv hab =>
    S.chain.endFiltration_antitone hab (S.chain.mul_mem_endFiltration hu hv)
  have hcx : c * x - x * c ∈ S.chain.endFiltration 0 := by
    refine sub_mem ?_ ?_
    · simpa using S.chain.mul_mem_endFiltration hc hxP
    · simpa using S.chain.mul_mem_endFiltration hxP hc
  -- splitting off the twist
  have hsplit : ∀ y : A, traceCharacter ψF (y * ((S.b + c) * x - x * (S.b + c))) =
      traceCharacter ψF (-((S.b * y - y * S.b) * x)) *
        traceCharacter ψF (y * (c * x - x * c)) := by
    intro y
    rw [show y * ((S.b + c) * x - x * (S.b + c)) =
      y * (S.b * x - x * S.b) + y * (c * x - x * c) by noncomm_ring,
      AddChar.map_add_eq_mul, traceCharacter_apply, trace_mul_commutator, ← traceCharacter_apply]
  -- Step 1: the dual form of (3.1.16)
  have hstep1 : x ∈ centralizerLattice S.chain S.b ((i + 1 : ℕ) : ℤ) ⊔
      simpleHLayer S.chain S.n S.b q.tail (i + 1 + 1) := by
    refine mem_centralizer_sup_of_adjoint_orthogonal S h0 hs q hβES hβE s hψ i hx ?_
    intro y hy
    have hyP : y ∈ S.chain.endFiltration (r - ((i + 1 : ℕ) : ℤ)) :=
      (centralizerLattice_mul_adjointLattice_le_inf S.chain S.b hcrit.le hy).2
    have hc1 : traceCharacter ψF (y * (c * x - x * c)) = 1 :=
      traceCharacter_eq_one S.chain hψ (hP1 hyP hcx (by omega))
    have h := h1 y hy
    rw [hsplit, hc1, mul_one, AddChar.map_neg_eq_inv, inv_eq_one] at h
    exact h
  -- Step 2: the centralizer part lies in `𝔓^{m+1}`
  obtain ⟨q₀, hq₀, h₀, hh₀, hx₀⟩ := Submodule.mem_sup.mp hstep1
  set qq := e₂ * q₀ * e₁ with hqq
  set hh := e₂ * h₀ * e₁ with hhh
  have hxdec : x = qq + hh := by
    rw [← hx21, ← hx₀, hqq, hhh]; noncomm_ring
  have hqqQ : qq ∈ centralizerLattice S.chain S.b ((i + 1 : ℕ) : ℤ) := by
    have h1' := SimpleStratumLattice.centralizer_mul_le S.chain S.b 0 ((i + 1 : ℕ) : ℤ)
    have h2' := SimpleStratumLattice.centralizer_mul_le S.chain S.b ((i + 1 : ℕ) : ℤ) 0
    have ha := h1' (Submodule.mul_mem_mul he₂B hq₀)
    rw [zero_add] at ha
    have hb2 := h2' (Submodule.mul_mem_mul ha he₁B)
    rw [add_zero] at hb2
    exact hb2
  have hqq21 : e₂ * qq * e₁ = qq := by
    rw [hqq]
    calc e₂ * (e₂ * q₀ * e₁) * e₁ = (e₂ * e₂) * q₀ * (e₁ * e₁) := by noncomm_ring
      _ = _ := by rw [he₂₂, he₁₁]
  have hhhH : hh ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1 + 1) := by
    have h' := (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q (i + 1 + 1) he₂B hh₀).1
    exact (mul_mem_simpleHLayer_of_mem_centralizer S h0 hs q (i + 1 + 1) he₁B h').2
  have hhhP : hh ∈ S.chain.endFiltration ((i + 1 + 1 : ℕ) : ℤ) := hhhH.2
  have hqqP : qq ∈ S.chain.endFiltration ((i + 1 + 1 : ℕ) : ℤ) := by
    refine hinj qq hqqQ hqq21 ?_
    have hcrit' := TameCorestriction.restrictScalars_mem_endFiltration_iff_trace s S.chain
      hE 0 (c * qq - qq * c)
    rw [show (1 : ℤ) - 0 = 1 by ring] at hcrit'
    refine hcrit'.mpr ?_
    intro y hy hyE
    have hyB : y ∈ centralizerLattice S.chain S.b 0 := by
      refine ⟨hy, ?_⟩
      change adjointMap 𝒪[F] S.b y = 0
      have := commute_of_mem_fieldCommutant hyE βE
      rw [hβES] at this
      change S.b * y - y * S.b = 0
      rw [this, sub_self]
    have hmem : c * qq - qq * c ∈ additiveDual (traceCharacter ψF)
        (centralizerLattice S.chain S.b 0 : Set A) := by
      intro y' hy'
      have h := h2 y' hy'
      have hcomm : S.b * y' - y' * S.b = 0 := hy'.2
      rw [hsplit, hcomm, zero_mul, neg_zero, AddChar.map_zero_eq_one, one_mul] at h
      have hhh1 : traceCharacter ψF (y' * (c * hh - hh * c)) = 1 := by
        refine traceCharacter_eq_one S.chain hψ ?_
        have hch : c * hh - hh * c ∈ S.chain.endFiltration 1 :=
          sub_mem (hP1 hc hhhP (by push_cast; omega)) (hP1 hhhP hc (by push_cast; omega))
        simpa using S.chain.mul_mem_endFiltration hy'.1 hch
      rw [hxdec, show y' * (c * (qq + hh) - (qq + hh) * c) =
        y' * (c * qq - qq * c) + y' * (c * hh - hh * c) by noncomm_ring,
        AddChar.map_add_eq_mul, hhh1, mul_one] at h
      rwa [traceCharacter_apply, LinearMap.trace_mul_comm, ← traceCharacter_apply]
    exact (mem_additiveDual_iff_trace ψF hψ _ _).mp hmem y hyB
  have hqqH : qq ∈ simpleHLayer S.chain S.n S.b q.tail (i + 1 + 1) := by
    obtain ⟨-, ⟨-, -, -, -, hQH, -, -, -⟩, -⟩ := simpleStratumLatticeProperties F V S h0 hs q
    refine ⟨hQH ⟨S.chain.endFiltration_antitone (by positivity) hqqP, hqqQ.2⟩, hqqP⟩
  rw [hxdec]
  exact add_mem hqqH hhhH

end Langlands.BushnellKutzko.SplitBlocks
