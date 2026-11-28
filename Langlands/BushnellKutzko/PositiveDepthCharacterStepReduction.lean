import Langlands.BushnellKutzko.SplitTypeExistenceSteps
import Langlands.BushnellKutzko.SimpleCharacterRestrictionStatement
import Langlands.BushnellKutzko.SimpleStratumGroupPropertiesProof
import Langlands.BushnellKutzko.AdditiveDualityProof
import Langlands.BushnellKutzko.SimpleCharacterExtension
import Langlands.BushnellKutzko.HeisenbergCharacterLocalData
import Langlands.BushnellKutzko.PureStratumApproximationNonsplitTransfer
import Langlands.Representation.Twist.Definitions
import Langlands.BushnellKutzko.SimpleCharacterSequence

/-! # The positive-depth step of BK93 (8.1.5) from its cases

This module states four propositions used in the positive-depth part of the proof of
Bushnell–Kutzko (8.1.5) (BK93, printed pp. 270–275). These four propositions and the imported
`SimpleCharacterRestrictionStatement` are the premises of `positiveDepthCharacterStepReduction`,
which derives `PositiveDepthCharacterStepStatement` from them. The four propositions are not
proved here. -/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uE uV uπ uρ

section TwistedCharacter

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

/-- The character `ϑ = θ ψ_c` of `H^{j+1}(β,𝔄)`: the product of a character `θ` of
`H^{j+1}(β,𝔄)` and the restriction of `ψ_c` along `H^{j+1}(β,𝔄) ≤ U^{j+1}(𝔄)`, for
`c ∈ 𝔓^{-(j+1)}`. -/
def traceTwistedCharacter (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F V) (q : S.DefiningSequenceChoice) (j : ℕ)
    (θ : simpleHGroup S.chain S.n S.b q.tail (j + 1) →* ℂˣ)
    (c : S.chain.endFiltration (-((j + 1 : ℕ) : ℤ))) :
    simpleHGroup S.chain S.n S.b q.tail (j + 1) →* ℂˣ :=
  θ * (filtrationTraceCharacter S.chain ψF hψ (Nat.succ_pos j) c.2).comp
    (Subgroup.inclusion (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (j + 1)))

end TwistedCharacter

/-- **BK93 (8.1.7)**, for characters. Let `[𝔄, n, m, β]` be simple with `m = j + 1 ≥ 1`,
`θ ∈ C(𝔄, m − 1, β)` and `c ∈ 𝔓^{-m}`, and let `π` be an irreducible smooth representation that
contains `ϑ = θ ψ_c` on `H^m(β, 𝔄)`. If `K ≤ U^m(𝔄)` and `χ` is a character of `K` agreeing
with `ϑ` on `K ∩ H^m(β, 𝔄)`, then `π` contains `χ`. BK93 take `K` open and `χ` an irreducible
representation of `K`; for a character the openness of `K` is not needed. -/
def PositiveDepthCharacterPropagationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F (Fin n → F)), S.IsSimple → ∀ (q : S.DefiningSequenceChoice) (j : ℕ),
    S.r = (j : ℤ) + 1 →
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail j,
    ∀ c : S.chain.endFiltration (-((j + 1 : ℕ) : ℤ)),
    ∀ π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F), π.IsIrreducible →
      ContainsAutCharacter π (traceTwistedCharacter ψF hψ S q j θ c) →
    ∀ K : Subgroup (Module.End F (Fin n → F))ˣ, K ≤ S.chain.unitFiltration (j + 1) →
    ∀ χ : K →* ℂˣ,
      (∀ (g : K) (hg : (g : (Module.End F (Fin n → F))ˣ) ∈
          simpleHGroup S.chain S.n S.b q.tail (j + 1)),
        χ g = traceTwistedCharacter ψF hψ S q j θ c ⟨g, hg⟩) →
      ContainsAutCharacter π χ

/-- **BK93 (8.1.10)–(8.1.13).** Let `[𝔄, n, m, β]` be simple with `m = j + 1 ≥ 1`,
`θ ∈ C(𝔄, m − 1, β)`, `c ∈ 𝔓^{-m}` and `s` a tame corestriction relative to `E = F[β]`. If the
derived stratum `[𝔅, m, m − 1, s(c)]` is not fundamental, then every irreducible smooth `π`
containing `θ ψ_c` contains a simple character of a simple stratum `T` of smaller depth
`T.r / e(T) < m / e(𝔄)`. -/
def NonfundamentalDerivedCharacterStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F (Fin n → F)) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) (j : ℕ),
    S.r = (j : ℤ) + 1 →
    let E := elementAlgebra S.b
    letI : Field E := hS.1.1.fst.toField
    letI : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail j,
    ∀ (c : S.chain.endFiltration (-((j + 1 : ℕ) : ℤ)))
      (s : TameCorestriction 𝒪[F] F E (Fin n → F)),
      ¬ (S.chain.corestrictedStratum hS.1.1.snd s (j + 1 : ℕ) c).IsFundamental →
      ∀ π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F), π.IsIrreducible →
        ContainsAutCharacter π (traceTwistedCharacter ψF hψ S q j θ c) →
        ∃ T : Stratum 𝒪[F] F (Fin n → F), ContainsSimpleCharacter ψF π T ∧
          T.r * (S.chain.period : ℤ) < S.r * (T.chain.period : ℤ)

/-- **BK93 (8.1.14)–(8.1.15).** As `NonfundamentalDerivedCharacterStatement`, when the derived
stratum `[𝔅, m, m − 1, s(c)]` is nonsplit fundamental. -/
def NonsplitDerivedCharacterStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ) (ψF : AddChar F ℂ) (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F (Fin n → F)) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) (j : ℕ),
    S.r = (j : ℤ) + 1 →
    let E := elementAlgebra S.b
    letI : Field E := hS.1.1.fst.toField
    letI : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail j,
    ∀ (c : S.chain.endFiltration (-((j + 1 : ℕ) : ℤ)))
      (s : TameCorestriction 𝒪[F] F E (Fin n → F)),
      (S.chain.corestrictedStratum hS.1.1.snd s (j + 1 : ℕ) c).IsNonsplit →
      ∀ π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F), π.IsIrreducible →
        ContainsAutCharacter π (traceTwistedCharacter ψF hψ S q j θ c) →
        ∃ T : Stratum 𝒪[F] F (Fin n → F), ContainsSimpleCharacter ψF π T ∧
          T.r * (S.chain.period : ℤ) < S.r * (T.chain.period : ℤ)

/-- **BK93, proof of (8.1.5), printed pp. 274–275.** Let `[𝔄, n, m, β]` be simple with
`m = j + 1 ≥ 1`, and suppose `d = gcd(m, e(𝔅 | 𝔬_E)) > 1`, where `𝔅` is the hereditary
`𝔬_E`-order of the centralizer chain. For every `θ ∈ C(𝔄, m, β)` there are a simple stratum `T`
(in the source, `[𝔄', n/d, m/d, β]` on the chain `{L_{id}}`) with `0 ≤ T.r < m` and the same
depth `T.r / e(T) = m / e(𝔄)`, and `θ' ∈ C(T)` of `H^{T.r+1}(T)`, such that
`H^{T.r+1}(T) ≤ U^{m+1}(𝔄)` and `θ'` agrees with `θ` on `H^{m+1}(β, 𝔄) ∩ H^{T.r+1}(T)`. -/
def CoarseChainCharacterStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (V : Type uV) [AddCommGroup V] [Module F V]
    (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (S : Stratum 𝒪[F] F V) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) (j : ℕ),
    S.r = (j : ℤ) + 1 →
    let E := elementAlgebra S.b
    letI : Field E := hS.1.1.fst.toField
    letI : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
    1 < Nat.gcd (j + 1) (S.chain.subfieldChain E hS.1.1.snd).period →
    ∀ θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail (j + 1),
    ∃ T : Stratum 𝒪[F] F V, T.IsSimple ∧ 0 ≤ T.r ∧ T.r < S.r ∧
      T.r * (S.chain.period : ℤ) = S.r * (T.chain.period : ℤ) ∧
      ∃ q' : T.DefiningSequenceChoice,
      ∃ θ' ∈ simpleCharacters ψF T.chain T.n T.b q'.tail T.r.toNat,
        simpleHGroup T.chain T.n T.b q'.tail (T.r.toNat + 1) ≤
          S.chain.unitFiltration (j + 2) ∧
        characterAgreesOn (simpleHGroup S.chain S.n S.b q.tail (j + 2) ⊓
          simpleHGroup T.chain T.n T.b q'.tail (T.r.toNat + 1)) θ θ' (fun _ => 1)

/-- The positive-depth step of BK93 (8.1.5) from the restriction properties of simple
characters, (8.1.7), the nonfundamental and nonsplit cases of the derived stratum and the coarse
chain. -/
def PositiveDepthCharacterStepReductionStatement : Prop :=
  SimpleCharacterRestrictionStatement.{uF, uF} →
  PositiveDepthCharacterPropagationStatement.{uF, uπ} →
  NonfundamentalDerivedCharacterStatement.{uF, uπ} →
  NonsplitDerivedCharacterStatement.{uF, uπ} →
  CoarseChainCharacterStatement.{uF, uF} →
  PositiveDepthCharacterStepStatement.{uF, uπ, uρ}

/-! ### Common eigencharacters -/

section Eigencharacter

private theorem exists_common_eigenspace {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*}
    (f : ι → Module.End ℂ V) (M : Submodule ℂ V) [FiniteDimensional ℂ M]
    (hM : ∀ i, ∀ x ∈ M, f i x ∈ M)
    (hcomm : ∀ i k, ∀ x ∈ M, f i (f k x) = f k (f i x)) (hM0 : M ≠ ⊥) (s : Finset ι) :
    ∃ W : Submodule ℂ V, W ≤ M ∧ W ≠ ⊥ ∧ (∀ i, ∀ x ∈ W, f i x ∈ W) ∧
      ∀ i ∈ s, ∃ c : ℂ, ∀ x ∈ W, f i x = c • x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨M, le_rfl, hM0, hM, by simp⟩
  | insert a s ha ih =>
    obtain ⟨W, hWM, hW0, hWinv, hWs⟩ := ih
    have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWM
    have : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
    let g : Module.End ℂ W := (f a).restrict (hWinv a)
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue g
    obtain ⟨x, hx⟩ := hc.exists_hasEigenvector
    have hgx : f a (x : V) = c • (x : V) := by
      have := hx.apply_eq_smul
      exact congrArg Subtype.val this
    let W' : Submodule ℂ V := W ⊓ LinearMap.ker (f a - c • 1)
    have hmemW' : ∀ y, y ∈ W' ↔ y ∈ W ∧ f a y = c • y := by
      intro y
      simp only [W', Submodule.mem_inf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
    refine ⟨W', inf_le_left.trans hWM, ?_, ?_, ?_⟩
    · rw [Submodule.ne_bot_iff]
      refine ⟨x, (hmemW' _).2 ⟨x.2, hgx⟩, ?_⟩
      intro h0
      exact hx.2 (Subtype.ext h0)
    · intro i y hy
      rw [hmemW'] at hy ⊢
      refine ⟨hWinv i y hy.1, ?_⟩
      rw [hcomm a i y (hWM hy.1), hy.2, map_smul]
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact ⟨c, fun y hy => ((hmemW' y).1 hy).2⟩
      · obtain ⟨d, hd⟩ := hWs i hi
        exact ⟨d, fun y hy => hd y ((hmemW' y).1 hy).1⟩

private theorem exists_eigencharacter {G : Type*} [Group G] (N : Subgroup G) [N.FiniteIndex]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V)
    (hcomm : ∀ g h : G, g * h * g⁻¹ * h⁻¹ ∈ N) {v : V} (hv : v ≠ 0)
    (hN : ∀ n ∈ N, ρ n v = v) :
    ∃ w : V, w ≠ 0 ∧ ∃ χ : G →* ℂˣ, (∀ n ∈ N, χ n = 1) ∧ ∀ g, ρ g w = (χ g : ℂ) • w := by
  classical
  have hnormal : ∀ g : G, ∀ n ∈ N, g⁻¹ * n * g ∈ N := by
    intro g n hn
    have h := N.mul_mem (hcomm g⁻¹ n) hn
    simpa [mul_assoc] using h
  let e : G ⧸ N → V := fun x => ρ (Quotient.out x) v
  let M : Submodule ℂ V := Submodule.span ℂ (Set.range e)
  have : FiniteDimensional ℂ M := FiniteDimensional.span_of_finite ℂ (Set.finite_range e)
  have hgen : ∀ g : G, ρ g v ∈ M := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g
    have : g = Quotient.out (QuotientGroup.mk g : G ⧸ N) * (h : G)⁻¹ := by
      rw [hh]; group
    rw [this, map_mul, Module.End.mul_apply, hN _ (N.inv_mem h.2)]
    exact Submodule.subset_span ⟨_, rfl⟩
  have hM : ∀ g : G, ∀ x ∈ M, ρ g x ∈ M := by
    intro g x hx
    have : M ≤ M.comap (ρ g) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      change ρ g (ρ (Quotient.out y) v) ∈ M
      rw [← Module.End.mul_apply, ← map_mul]
      exact hgen _
    exact this hx
  have hNM : ∀ n ∈ N, ∀ x ∈ M, ρ n x = x := by
    intro n hn x hx
    have : M ≤ LinearMap.ker (ρ n - 1) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      change (ρ n - 1) (ρ (Quotient.out y) v) = 0
      rw [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, ← Module.End.mul_apply,
        ← map_mul]
      have : n * Quotient.out y = Quotient.out y * ((Quotient.out y)⁻¹ * n * Quotient.out y) := by
        group
      rw [this, map_mul, Module.End.mul_apply, hN _ (hnormal _ n hn)]
    have h := this hx
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  have hcommM : ∀ g h : G, ∀ x ∈ M, ρ g (ρ h x) = ρ h (ρ g x) := by
    intro g h x hx
    have hk : g⁻¹ * h⁻¹ * g * h ∈ N := by simpa using hcomm g⁻¹ h⁻¹
    have : g * h = h * g * (g⁻¹ * h⁻¹ * g * h) := by group
    rw [← Module.End.mul_apply, ← map_mul, this, map_mul, Module.End.mul_apply,
      hNM _ hk x hx, map_mul, Module.End.mul_apply]
  have : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hM0 : M ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨v, by simpa using hgen 1, hv⟩
  obtain ⟨W, hWM, hW0, -, hWs⟩ := exists_common_eigenspace (fun x : G ⧸ N => ρ (Quotient.out x))
    M (fun x => hM _) (fun x y => hcommM _ _) hM0 Finset.univ
  obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).1 hW0
  have hscalar : ∀ g : G, ∃ c : ℂ, ρ g w = c • w := by
    intro g
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul N g
    have hg : g = Quotient.out (QuotientGroup.mk g : G ⧸ N) * (h : G)⁻¹ := by
      rw [hh]; group
    obtain ⟨c, hc⟩ := hWs (QuotientGroup.mk g) (Finset.mem_univ _)
    refine ⟨c, ?_⟩
    rw [hg, map_mul, Module.End.mul_apply, hNM _ (N.inv_mem h.2) w (hWM hwW)]
    exact hc w hwW
  choose c hc using hscalar
  have huniq : ∀ a b : ℂ, a • w = b • w → a = b := fun a b h => smul_left_injective ℂ hw0 h
  let χ₀ : G →* ℂ :=
    { toFun := c
      map_one' := huniq _ _ (by rw [← hc, map_one, Module.End.one_apply, one_smul])
      map_mul' := fun g h => huniq _ _ (by
        rw [← hc, map_mul, Module.End.mul_apply, hc h, map_smul, hc g, smul_smul, mul_comm]) }
  refine ⟨w, hw0, χ₀.toHomUnits, ?_, ?_⟩
  · intro n hn
    apply Units.ext
    change c n = 1
    exact huniq _ _ (by rw [← hc, one_smul, hNM n hn w (hWM hwW)])
  · intro g
    exact hc g

/-- A character that is trivial on the kernel of a homomorphism `f` into a commutative group
is the pullback along `f` of a character of the target. -/
private theorem exists_character_extension_of_ker {G A : Type*} [Group G] [CommGroup A]
    (f : G →* A) (χ : G →* ℂˣ) (h : ∀ g, f g = 1 → χ g = 1) :
    ∃ χ' : A →* ℂˣ, ∀ g, χ' (f g) = χ g := by
  have hle : f.ker ≤ χ.ker := fun g hg => h g hg
  let χ₁ : f.range →* ℂˣ :=
    (QuotientGroup.lift f.ker χ hle).comp
      (QuotientGroup.quotientKerEquivRange f).symm.toMonoidHom
  obtain ⟨χ₂, hχ₂⟩ := exists_complexCharacter_extension f.range χ₁
  refine ⟨χ₂, fun g => ?_⟩
  have h1 : χ₂ (f g) = χ₁ ⟨f g, g, rfl⟩ := DFunLike.congr_fun hχ₂ ⟨f g, g, rfl⟩
  rw [h1]
  have h2 : (QuotientGroup.quotientKerEquivRange f).symm ⟨f g, g, rfl⟩ = (g : G ⧸ f.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [χ₁, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h2]
  rfl

private theorem units_inv_smul_smul {M : Type*} [AddCommGroup M] [Module ℂ M] (a b : ℂˣ)
    (hab : a = b) (y : M) : (a⁻¹ : ℂˣ) • ((b : ℂ) • y) = y := by
  subst hab
  rw [Units.smul_def, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]

private theorem eq_mul_smul_of_inv_smul_eq {M : Type*} [AddCommGroup M] [Module ℂ M] (a : ℂˣ)
    (b c : ℂ) (y z : M) (hbc : b = c) (h : (a⁻¹ : ℂˣ) • y = c • z) : y = ((a : ℂ) * b) • z := by
  subst hbc
  rw [mul_smul, ← h, Units.smul_def, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    one_smul]

end Eigencharacter

/-! ### From a simple character in `C(𝔄, m, β)` to a character `θ ψ_c` of `H^m` -/

section StepA

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "Aut" => (Module.End F (Fin n → F))ˣ

/-- `H^k(β, 𝔄) ∩ U^{k+1}(𝔄) ⊆ H^{k+1}(β, 𝔄)`. -/
private theorem mem_simpleHGroup_succ_of_mem (S : Stratum 𝒪[F] F (Fin n → F)) (hS : S.IsSimple)
    (q : S.DefiningSequenceChoice) (h0 : 0 ≤ S.r) (k : ℕ) {g : Aut}
    (hg1 : g ∈ simpleHGroup S.chain S.n S.b q.tail k)
    (hg2 : g ∈ S.chain.unitFiltration (k + 1)) :
    g ∈ simpleHGroup S.chain S.n S.b q.tail (k + 1) := by
  have hS0 := Stratum.isSimple_atDepthZero hS h0
  obtain ⟨hcarrier, -⟩ :=
    simpleStratumGroupProperties F (Fin n → F) (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl hS0
      (q.atDepthZero h0)
  have h1 : (simpleHGroup S.chain S.n S.b q.tail k : Set Aut) =
      simpleHCarrier S.chain S.n S.b q.tail k := (hcarrier k).1
  have h2 : (simpleHGroup S.chain S.n S.b q.tail (k + 1) : Set Aut) =
      simpleHCarrier S.chain S.n S.b q.tail (k + 1) := (hcarrier (k + 1)).1
  rw [← SetLike.mem_coe, h1] at hg1
  rw [← SetLike.mem_coe, h2]
  exact ⟨hg2, hg1.2⟩

/-- **BK93, proof of (8.1.5), printed p. 270.** If `π` contains `θ ∈ C(𝔄, m, β)` with `m ≥ 1`,
then `π` contains `θ' ψ_c` for some `θ' ∈ C(𝔄, m - 1, β)` extending `θ` and `c ∈ 𝔓^{-m}`. -/
private theorem exists_traceTwistedCharacter_of_contains
    (hRes : SimpleCharacterRestrictionStatement.{uF, uF})
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF)
    (S : Stratum 𝒪[F] F (Fin n → F)) (hS : S.IsSimple) (q : S.DefiningSequenceChoice) (j : ℕ)
    (hr : S.r = (j : ℤ) + 1)
    {θ : simpleHGroup S.chain S.n S.b q.tail (j + 1 + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail (j + 1))
    (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)) (hπ : ContainsAutCharacter π θ) :
    ∃ θ' ∈ simpleCharacters ψF S.chain S.n S.b q.tail j,
      (∀ (g : Aut) (hg : g ∈ simpleHGroup S.chain S.n S.b q.tail (j + 1 + 1)),
        θ' ⟨g, simpleHGroup_antitone _ _ _ _ (Nat.le_succ _) hg⟩ = θ ⟨g, hg⟩) ∧
      ∃ c : S.chain.endFiltration (-((j + 1 : ℕ) : ℤ)),
        ContainsAutCharacter π (traceTwistedCharacter ψF hψ S q j θ' c) := by
  have h0 : (0 : ℤ) ≤ S.r := by rw [hr]; positivity
  have hS0 := Stratum.isSimple_atDepthZero hS h0
  obtain ⟨-, -, -, hHJ, hcomm⟩ :=
    simpleStratumGroupProperties F (Fin n → F) (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl hS0
      (q.atDepthZero h0)
  obtain ⟨-, -, -, hd, -⟩ := hRes F (Fin n → F) ψF hψ (S.atDepthZero (h0.trans_lt S.r_lt_n)) rfl
    hS0 (q.atDepthZero h0)
  have h : simpleCharacterRestriction (S.atDepthZero (h0.trans_lt S.r_lt_n)) (q.atDepthZero h0)
      (Nat.le_succ j) '' simpleCharacters ψF S.chain S.n S.b q.tail j =
      simpleCharacters ψF S.chain S.n S.b q.tail (j + 1) :=
    hd j (by have := S.r_lt_n; change (j : ℤ) + 1 < S.n; omega)
  rw [← h] at hθ
  obtain ⟨θ', hθ', rfl⟩ := hθ
  refine ⟨θ', hθ', fun g hg => rfl, ?_⟩
  set L := S.chain with hL
  set H := simpleHGroup S.chain S.n S.b q.tail with hH
  -- `H^{m} ∩ U^{m+1}(𝔄) ⊆ H^{m+1}`
  have hdom : ∀ g : Aut, g ∈ H (j + 1) → g ∈ L.unitFiltration (j + 1 + 1) → g ∈ H (j + 1 + 1) :=
    fun g hg1 hg2 => mem_simpleHGroup_succ_of_mem S hS q h0 (j + 1) hg1 hg2
  -- `U^{m+1}(𝔄) ∩ H^m` has finite index in `H^m`
  let N : Subgroup (H (j + 1)) := (L.unitFiltration (j + 1 + 1)).subgroupOf (H (j + 1))
  have hNfin : N.FiniteIndex := by
    have hU : (L.unitFiltration (j + 1 + 1)).relIndex (L.unitFiltration (j + 1)) ≠ 0 := by
      have he := Subgroup.relIndex_mul_relIndex (L.unitFiltration (j + 1 + 1))
        (L.unitFiltration (j + 1)) (L.unitFiltration 1) (L.unitFiltration_antitone (by omega))
        (L.unitFiltration_antitone (by omega))
      have hfin := (L.unitFiltration_finiteIndex_in_one (j + 1)).index_ne_zero
      intro h0'
      apply hfin
      change (L.unitFiltration (j + 1 + 1)).relIndex (L.unitFiltration 1) = 0
      rw [← he, h0', zero_mul]
    refine ⟨?_⟩
    change (L.unitFiltration (j + 1 + 1)).relIndex (H (j + 1)) ≠ 0
    exact fun h' => hU (Subgroup.relIndex_eq_zero_of_le_right
      (simpleHGroup_le_unitFiltration _ _ _ _ _) h')
  -- commutators of `H^m` lie in `H^{2m} ⊆ U^{m+1}(𝔄)`
  have hcommN : ∀ g h : H (j + 1), g * h * g⁻¹ * h⁻¹ ∈ N := by
    intro g h
    rw [Subgroup.mem_subgroupOf]
    have hJ : ∀ x : H (j + 1), (x : Aut) ∈ simpleJGroup S.chain S.n S.b q.tail (j + 1) :=
      fun x => (hHJ (j + 1)).1 x.2
    have hc := hcomm (j + 1) (j + 1) (by omega) (by omega)
      (Subgroup.commutator_mem_commutator (hJ g) (hJ h))
    rw [commutatorElement_def] at hc
    have hc' : (g : Aut) * h * (g : Aut)⁻¹ * (h : Aut)⁻¹ ∈ H (j + 1 + 1) :=
      simpleHGroup_antitone _ _ _ _ (by omega) hc
    simpa using simpleHGroup_le_unitFiltration _ _ _ _ _ hc'
  obtain ⟨v, hv0, hv⟩ := hπ
  let toG : Aut →* GeneralLinear n F := Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom
  let ρ : Representation ℂ (H (j + 1)) π :=
    Langlands.twist θ'⁻¹ (π.representation.comp (toG.comp (H (j + 1)).subtype))
  have hρ : ∀ g : H (j + 1), ∀ x : π,
      ρ g x = ((θ' g)⁻¹ : ℂˣ) • π.representation (toG g) x := fun g x => rfl
  have hfix : ∀ x ∈ N, ρ x v = v := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hx2 := hdom x x.2 hx
    have h1 := hv ⟨x, hx2⟩
    rw [hρ]
    change ((θ' x)⁻¹ : ℂˣ) • π.representation (Matrix.GeneralLinearGroup.toLin.symm (x : Aut)) v = v
    rw [h1]
    exact units_inv_smul_smul _ _ rfl v
  have := hNfin
  obtain ⟨w, hw0, χ, hχN, hχw⟩ := exists_eigencharacter N ρ hcommN hv0 hfix
  -- extend `χ` from `H^m` to `U^m(𝔄)`, trivially on `U^{m+1}(𝔄)`
  let φ := L.unitFiltrationToQuotient (i := j + 1) (j := j + 1 + 1) (by omega)
  let f := φ.comp (Subgroup.inclusion (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail
    (j + 1)))
  obtain ⟨χ₂, hχ₂⟩ := exists_character_extension_of_ker f χ (by
    intro g hg
    apply hχN
    rw [Subgroup.mem_subgroupOf]
    have := (L.mem_ker_unitFiltrationToQuotient (i := j + 1) (j := j + 1 + 1) (by omega)
      (Subgroup.inclusion (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (j + 1)) g)).1
      hg
    exact this)
  let χ₃ : L.unitFiltration (j + 1) →* ℂˣ := χ₂.comp φ
  have hχ₃ : ∀ g : L.unitFiltration (j + 1),
      (g : Aut) ∈ L.unitFiltration (j + 1 + 1) → χ₃ g = 1 := by
    intro g hg
    have : φ g = 1 := (L.mem_ker_unitFiltrationToQuotient (i := j + 1) (j := j + 1 + 1)
      (by omega) g).2 hg
    change χ₂ (φ g) = 1
    rw [this, map_one]
  obtain ⟨b, hb, hχb⟩ := ((additiveDuality F (Fin n → F) L ψF hψ.1 hψ.2).2 (j + 1) j
    (by omega) (by omega)).2.2 χ₃ hχ₃
  refine ⟨⟨b, hb⟩, w, hw0, fun u => ?_⟩
  have hu := hχw u
  rw [hρ] at hu
  have hψu : (filtrationTraceCharacter S.chain ψF hψ (Nat.succ_pos j) hb
      (Subgroup.inclusion (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (j + 1)) u) :
        ℂ) = χ u := by
    rw [filtrationTraceCharacter_apply, ← hχb, ← hχ₂ u]
    rfl
  change π.representation (toG u) w = ((θ' u * _ : ℂˣ) : ℂ) • w
  rw [Units.val_mul]
  exact eq_mul_smul_of_inv_smul_eq _ _ _ _ w hψu hu

end StepA

/-! ### The trichotomy for the derived stratum -/

section Trichotomy

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E] [FiniteDimensional F E]
  {V : Type uV} [AddCommGroup V] [Module E V]

/-- A fundamental stratum over `𝔬_E` that is not split is nonsplit: its polynomial `φ_b` is a
positive power of a single monic irreducible polynomial (BK93 (2.3.3)). -/
private theorem isNonsplit_of_not_isSplit (D : Stratum (subfieldIntegers F E) E V)
    (hfund : D.IsFundamental) (hns : ¬ D.IsSplit) : D.IsNonsplit := by
  classical
  have := D.chain.finiteDimensional
  have := D.chain.nontrivialSpace
  have : IsDiscreteValuationRing (subfieldIntegers F E) :=
    subfieldIntegers_isDiscreteValuationRing F E
  have hinj : Function.Injective (algebraMap (subfieldIntegers F E) E) := Subtype.val_injective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (subfieldIntegers F E)
  let π : RingPrimeElement (subfieldIntegers F E) :=
    ⟨ϖ, hϖ.ne_zero, by rw [IsLocalRing.ringJacobson_eq_maximalIdeal, hϖ.maximalIdeal_eq]⟩
  have hmax : (Ring.jacobson (subfieldIntegers F E)).IsMaximal := by
    rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
    exact IsLocalRing.maximalIdeal.isMaximal _
  let : Field (subfieldIntegers F E ⧸ Ring.jacobson (subfieldIntegers F E)) :=
    Ideal.Quotient.field _
  have hmon := PureApproximation.reduceIntegralPolynomial_monic (O := subfieldIntegers F E) hinj
    (LinearMap.charpoly_monic (D.fundamentalElement π))
  have hφmon : (D.fundamentalPolynomial π).Monic := hmon.1
  have hφdeg : 0 < (D.fundamentalPolynomial π).natDegree := by
    unfold Stratum.fundamentalPolynomial
    rw [hmon.2, LinearMap.charpoly_natDegree]
    exact Module.finrank_pos
  obtain ⟨p, m, hpm, hpi, hm, hφp⟩ := PureApproximation.exists_eq_pow_of_not_two_factors hφmon
    hφdeg (fun ⟨p, q, hp, hq, hpi, hqi, hpq, hpd, hqd⟩ =>
      hns ⟨hfund, π, p, q, hp, hq, hpi, hqi, hpq, hpd, hqd⟩)
  exact ⟨hfund, π, p, m, hpm, hpi, hm, hφp⟩

end Trichotomy

section DerivedCases

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

set_option maxHeartbeats 1000000 in
/-- For a simple stratum `[𝔄, n, m, β]` with `m ≥ 1` and `c ∈ 𝔓^{-m}`, there is a tame
corestriction `s` for which the derived stratum `[𝔅, m, m−1, s(c)]` is not fundamental, or is
nonsplit, or is split with `gcd(m, e(𝔅 | 𝔬_E)) = 1`, or `gcd(m, e(𝔅 | 𝔬_E)) > 1`.
Elaborating the three predicates on the derived stratum over `F[β]` is expensive, hence the
raised heartbeat limit. -/
private theorem exists_derivedStratum_cases (S : Stratum 𝒪[F] F (Fin n → F)) (hS : S.IsSimple)
    (j : ℕ) :
    let E := elementAlgebra S.b
    letI : Field E := hS.1.1.fst.toField
    letI : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
    ∀ c : S.chain.endFiltration (-((j + 1 : ℕ) : ℤ)),
    ∃ s : TameCorestriction 𝒪[F] F E (Fin n → F),
      ¬ (S.chain.corestrictedStratum hS.1.1.snd s (j + 1 : ℕ) c).IsFundamental ∨
      (S.chain.corestrictedStratum hS.1.1.snd s (j + 1 : ℕ) c).IsNonsplit ∨
      (Nat.Coprime (j + 1) (S.chain.subfieldChain E hS.1.1.snd).period ∧
        (S.chain.corestrictedStratum hS.1.1.snd s (j + 1 : ℕ) c).IsSplit) ∨
      1 < Nat.gcd (j + 1) (S.chain.subfieldChain E hS.1.1.snd).period := by
  intro E c
  let : Field E := hS.1.1.fst.toField
  let : FiniteDimensional F E := S.chain.finiteDimensional_subfield E
  obtain ⟨s⟩ := (tameCorestriction F (Fin n → F) E).1
  refine ⟨s, or_iff_not_imp_left.2 fun hfund => or_iff_not_imp_left.2 fun hns =>
    or_iff_not_imp_right.2 fun hgcd => ⟨?_, ?_⟩⟩
  · exact le_antisymm (not_lt.1 hgcd) (Nat.gcd_pos_of_pos_left _ (Nat.succ_pos j))
  · by_contra hsplit
    exact hns (isNonsplit_of_not_isSplit _ (not_not.1 hfund) hsplit)

end DerivedCases

/-! ### A contained character as a contained pair -/

section CharacterPair

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "Aut" => (Module.End F (Fin n → F))ˣ
local notation "toAut" => (Matrix.GeneralLinearGroup.toLin : GeneralLinear n F ≃* Aut)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- If `π` contains a character `χ` of a subgroup `U` of `Aut_F(F^n)`, then `π` contains a smooth
pair `(K, ρ)` in matrix coordinates whose transport along `toLin` is isomorphic to `(U, χ)`. -/
private theorem exists_containsType_of_containsAutCharacter
    (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)) {U : Subgroup Aut} (χ : U →* ℂˣ)
    (hπ : ContainsAutCharacter π χ) :
    ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
      IsPairIsomorphic (glRepresentationToAut ρ) (BushnellKutzko.characterRepresentation χ) := by
  obtain ⟨v, hv0, hv⟩ := hπ
  let K : Subgroup (GeneralLinear n F) := U.comap (toAut).toMonoidHom
  let χK : K →* ℂˣ :=
    χ.comp (((toAut).toMonoidHom.comp K.subtype).codRestrict U fun k => k.2)
  have hχK : ∀ k : K, π.representation (k : GeneralLinear n F) v = (χK k : ℂ) • v := by
    intro k
    have h := hv ⟨toAut k, k.2⟩
    rwa [MulEquiv.symm_apply_apply] at h
  let ρr : Representation ℂ K (ULift.{uρ} ℂ) :=
    { toFun := fun k => ((χK k : ℂˣ) : ℂ) • LinearMap.id
      map_one' := by
        rw [map_one, Units.val_one, one_smul]
        rfl
      map_mul' := fun a b => LinearMap.ext fun x => by
        simp only [map_mul, Units.val_mul, Module.End.mul_apply, LinearMap.smul_apply,
          LinearMap.id_apply, mul_smul] }
  have hρr : ∀ (k : K) (z : ULift.{uρ} ℂ), ρr k z = ((χK k : ℂˣ) : ℂ) • z := fun _ _ => rfl
  have hsmooth : IsSmooth ρr := by
    obtain ⟨O, hO⟩ := π.isSmooth v
    rw [fixedVectors, Representation.mem_invariants] at hO
    intro z
    refine ⟨OpenSubgroup.comap K.subtype continuous_subtype_val O, ?_⟩
    rw [fixedVectors, Representation.mem_invariants]
    intro g
    have hgO : ((g : K) : GeneralLinear n F) ∈ O := OpenSubgroup.mem_comap.1 g.2
    have h1 : π.representation ((g : K) : GeneralLinear n F) v = v := hO ⟨_, hgO⟩
    have hχ1 : ((χK (g : K) : ℂˣ) : ℂ) = 1 := by
      have h3 : ((χK (g : K) : ℂˣ) : ℂ) • v = (1 : ℂ) • v := by
        rw [← hχK, one_smul]
        exact h1
      exact smul_left_injective ℂ hv0 h3
    change ρr (g : K) z = z
    rw [hρr, hχ1, one_smul]
  refine ⟨K, SmoothRep.of ρr hsmooth, ?_, ?_⟩
  · let Φ : ULift.{uρ} ℂ →ₗ[ℂ] π :=
      LinearMap.toSpanSingleton ℂ π v ∘ₗ ULift.moduleEquiv.toLinearMap
    have hΦ : ∀ z : ULift.{uρ} ℂ, Φ z = z.down • v := fun _ => rfl
    refine ⟨⟨Φ, fun k => ?_⟩, ?_⟩
    · apply LinearMap.ext
      intro z
      change Φ (ρr k z) = π.representation (k : GeneralLinear n F) (Φ z)
      rw [hρr, hΦ, hΦ, map_smul, hχK, smul_smul, ULift.smul_down, smul_eq_mul, mul_comm]
    · intro h0
      have h := LinearMap.congr_fun (congrArg Representation.IntertwiningMap.toLinearMap h0)
        (ULift.up 1)
      apply hv0
      change Φ (ULift.up 1) = 0 at h
      rwa [hΦ, one_smul] at h
  · have hKU : glSubgroupToAut K = U :=
      Subgroup.map_comap_eq_self_of_surjective (toAut).surjective U
    refine ⟨hKU, ⟨Representation.Equiv.mk ULift.moduleEquiv fun u => ?_⟩⟩
    apply LinearMap.ext
    intro z
    have hu : χK ((glSubgroupToAutEquiv K).symm ((MulEquiv.subgroupCongr hKU).symm u)) = χ u := by
      have h1 : (((glSubgroupToAutEquiv K) ((glSubgroupToAutEquiv K).symm
          ((MulEquiv.subgroupCongr hKU).symm u)) : glSubgroupToAut K) : Aut) =
          (((MulEquiv.subgroupCongr hKU).symm u : glSubgroupToAut K) : Aut) := by
        rw [MulEquiv.apply_symm_apply]
      change χ ⟨toAut ((glSubgroupToAutEquiv K).symm ((MulEquiv.subgroupCongr hKU).symm u)), _⟩ =
        χ u
      congr 1
      exact Subtype.ext h1
    change (ρr ((glSubgroupToAutEquiv K).symm ((MulEquiv.subgroupCongr hKU).symm u)) z).down =
      ((χ u : ℂˣ) : ℂ) * z.down
    rw [hρr, ULift.smul_down, smul_eq_mul, hu]

end CharacterPair

/-! ### Induction on a bound for the stratum index -/

section Induction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The depth comparison is transitive through a stratum of the same depth. -/
private theorem depth_lt_of_eq_of_lt {S T T' : Stratum 𝒪[F] F (Fin n → F)}
    (hTeq : T.r * (S.chain.period : ℤ) = S.r * (T.chain.period : ℤ))
    (hlt : T'.r * (T.chain.period : ℤ) < T.r * (T'.chain.period : ℤ)) :
    T'.r * (S.chain.period : ℤ) < S.r * (T'.chain.period : ℤ) := by
  have heT : (0 : ℤ) < T.chain.period := by exact_mod_cast T.chain.period_pos
  have heS : (0 : ℤ) < S.chain.period := by exact_mod_cast S.chain.period_pos
  refine lt_of_mul_lt_mul_right ?_ heT.le
  calc T'.r * (S.chain.period : ℤ) * T.chain.period
      = (T'.r * T.chain.period) * S.chain.period := by ring
    _ < (T.r * T'.chain.period) * S.chain.period := mul_lt_mul_of_pos_right hlt heS
    _ = (T.r * S.chain.period) * T'.chain.period := by ring
    _ = (S.r * T.chain.period) * T'.chain.period := by rw [hTeq]
    _ = S.r * T'.chain.period * T.chain.period := by ring

/-- The positive-depth step of BK93 (8.1.5) follows from `SimpleCharacterRestrictionStatement`
and the four propositions above, by induction on a natural-number bound for the stratum index
`m = S.r`. -/
theorem positiveDepthCharacterStepReduction :
    PositiveDepthCharacterStepReductionStatement.{uF, uπ, uρ} := by
  intro hRes hProp hNonfund hNonsplit hCoarse F _ _ _ _ n _hn ψF hψ π hπ S hr0 hSπ
  suffices h : ∀ k : ℕ, ∀ S : Stratum 𝒪[F] F (Fin n → F), S.r.toNat < k → 0 < S.r →
      ContainsSimpleCharacter ψF π S →
      (∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
        ∃ x y : ℚ, IsUnequalPositiveSplitType (V := Fin n → F) ψF x y (glRepresentationToAut ρ)) ∨
      ∃ T : Stratum 𝒪[F] F (Fin n → F), ContainsSimpleCharacter ψF π T ∧
        T.r * (S.chain.period : ℤ) < S.r * (T.chain.period : ℤ) from
    h (S.r.toNat + 1) S (Nat.lt_succ_self _) hr0 hSπ
  intro k
  induction k with
  | zero => exact fun S h => absurd h (Nat.not_lt_zero _)
  | succ k ih =>
    intro S hSk hr0 hSπ
    obtain ⟨hS, -, q, hθ⟩ := hSπ
    obtain ⟨j, hj⟩ : ∃ j : ℕ, S.r = (j : ℤ) + 1 := ⟨S.r.toNat - 1, by omega⟩
    have hjk : S.r.toNat = j + 1 := by omega
    rw [hjk] at hθ
    obtain ⟨θ, hθ, hπθ⟩ := hθ
    obtain ⟨θ', hθ', hres, c, hc⟩ :=
      exists_traceTwistedCharacter_of_contains hRes hψ S hS q j hj hθ π hπθ
    obtain ⟨s, hcase⟩ := exists_derivedStratum_cases S hS j c
    rcases hcase with hfund | hns | ⟨hcop, hsplit⟩ | hgcd
    · exact Or.inr (hNonfund F n ψF hψ S hS q j hj θ' hθ' c s hfund π hπ hc)
    · exact Or.inr (hNonsplit F n ψF hψ S hS q j hj θ' hθ' c s hns π hπ hc)
    · -- BK93 (8.1.3): `(H^m(β, 𝔄), θ' ψ_c)` is a split type
      obtain ⟨K, ρ, hK, hiso⟩ := exists_containsType_of_containsAutCharacter.{uF, uπ, uρ} π _ hc
      exact Or.inl ⟨K, ρ, hK, _, _, hψ, S, q, j, hS, hj, rfl, rfl, hcop, θ', hθ', c, s, hsplit,
        hiso⟩
    · -- the coarser chain: a contained simple character of the same depth and smaller `m`
      obtain ⟨T, hT, hT0, hTlt, hTeq, q', θ'', hθ'', hTle, hagree⟩ :=
        hCoarse F (Fin n → F) ψF hψ S hS q j hj hgcd θ hθ
      have hπT : ContainsSimpleCharacter ψF π T := by
        refine ⟨hT, hT0, q', θ'', hθ'', ?_⟩
        refine hProp F n ψF hψ S hS q j hj θ' hθ' c π hπ hc _
          (hTle.trans (S.chain.unitFiltration_antitone (by omega))) θ'' ?_
        intro g hg
        have hg2 : (g : (Module.End F (Fin n → F))ˣ) ∈ S.chain.unitFiltration (j + 1 + 1) := hTle g.2
        have hgH : (g : (Module.End F (Fin n → F))ˣ) ∈ simpleHGroup S.chain S.n S.b q.tail (j + 1 + 1) :=
          mem_simpleHGroup_succ_of_mem S hS q (by omega) (j + 1) hg hg2
        have e1 : traceTwistedCharacter ψF hψ S q j θ' c ⟨g, hg⟩ = θ ⟨g, hgH⟩ := by
          have hψ1 := filtrationTraceCharacter_eq_one S.chain ψF hψ (Nat.succ_pos j) c.2
            (Subgroup.inclusion (simpleHGroup_le_unitFiltration S.chain S.n S.b q.tail (j + 1))
              ⟨g, hg⟩) hg2
          unfold traceTwistedCharacter
          rw [MonoidHom.mul_apply, MonoidHom.comp_apply, hψ1, mul_one]
          exact hres g hgH
        rw [e1]
        obtain ⟨h1, h2, hθθ⟩ := hagree ⟨g, hgH, g.2⟩
        rw [mul_one] at hθθ
        exact (Units.ext hθθ).symm
      have heT : (0 : ℤ) < T.chain.period := by exact_mod_cast T.chain.period_pos
      have heS : (0 : ℤ) < S.chain.period := by exact_mod_cast S.chain.period_pos
      have hTpos : 0 < T.r := by
        have h1 : 0 < S.r * (T.chain.period : ℤ) := mul_pos hr0 heT
        rw [← hTeq] at h1
        exact pos_of_mul_pos_left h1 heS.le
      have hTk : T.r.toNat < k := by omega
      rcases ih T hTk hTpos hπT with h | ⟨T', hT', hlt⟩
      · exact Or.inl h
      · exact Or.inr ⟨T', hT', depth_lt_of_eq_of_lt hTeq hlt⟩

end Induction

end Langlands.BushnellKutzko
