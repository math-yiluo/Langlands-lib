import Langlands.BushnellKutzko.CharacterTypeJacquetTransport
import Langlands.BushnellKutzko.ShiftedLowerCornerTransfer
import Langlands.BushnellKutzko.ShiftedSimpleLowerHTransfer
import Langlands.BushnellKutzko.SimpleCharacterLoweringReduction
import Langlands.BushnellKutzko.SimpleStratumLabelStep
import Langlands.BushnellKutzko.UnequalPositiveSplitTypeJacquetStatement
import Langlands.BushnellKutzko.UnequalSplitTypeAdjust
import Langlands.BushnellKutzko.UnequalSplitTypeBlocks
import Langlands.BushnellKutzko.UnequalSplitTypeSecondTransfer
import Langlands.BushnellKutzko.UnequalSplitTypeShiftElement

/-! # Jacquet nonvanishing for unequal positive levels -/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.SplitBlocks

universe uF uE uV uW uπ uρ

section Endomorphisms

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]
  {E : Type uE} [Field E] [Algebra F E] [Module E V] [IsScalarTower F E V]
  [FiniteDimensional F E] {W : Type uW} [AddCommGroup W] [Module ℂ W]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ
local notation "H[" S "," q "]" => simpleHGroup (Stratum.chain S) (Stratum.n S) (Stratum.b S)
  (Stratum.DefiningSequenceChoice.tail q)

private def twist (S : Stratum 𝒪[F] F V) (t : List A) (i : ℕ) {ψF : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψF) (θ : simpleHGroup S.chain S.n S.b t (i + 1) →* ℂˣ)
    (c : S.chain.endFiltration (-((i + 1 : ℕ) : ℤ))) :
    simpleHGroup S.chain S.n S.b t (i + 1) →* ℂˣ :=
  θ * (filtrationTraceCharacter S.chain ψF hψ (Nat.succ_pos i) c.2).comp
    (Subgroup.inclusion (simpleHGroup_le_unitFiltration S.chain S.n S.b t (i + 1)))

private theorem twist_apply (S : Stratum 𝒪[F] F V) (t : List A) (i : ℕ) {ψF : AddChar F ℂ}
    (hψ : IsBKAdditiveCharacter ψF) (θ : simpleHGroup S.chain S.n S.b t (i + 1) →* ℂˣ)
    (c : S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)))
    (h : simpleHGroup S.chain S.n S.b t (i + 1)) :
    (twist S t i hψ θ c h : ℂ) = (θ h : ℂ) * elementCharacter (traceCharacter ψF) (c : A) (h : G) := by
  rw [twist, MonoidHom.mul_apply, Units.val_mul, MonoidHom.comp_apply, filtrationTraceCharacter_apply]
  rfl

omit [FiniteDimensional F E] in
set_option maxHeartbeats 800000 in
private theorem not_le_relations_of_split_twist
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (i : ℕ) (hin : (i : ℤ) + 1 < S.n)
    (hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF) {θ : H[S,q] (i + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i)
    {βE : E} (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer)
    (R : RestrictedBlockData S.chain E) (h₂₁ : R.e₂ * R.e₁ = 0)
    (he₁₁ : R.e₁ * R.e₁ = R.e₁) (he₂₂ : R.e₂ * R.e₂ = R.e₂)
    (c : S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)))
    (hc₁ : Commute (c : A) R.e₁) (hc₂ : Commute (c : A) R.e₂)
    (hc₁₂ : R.e₁ * (c : A) * R.e₂ = 0) (hc₂₁ : R.e₂ * (c : A) * R.e₁ = 0)
    (hshift : s (R.ζ * (R.e₁ * (c : A) * R.e₁) * R.ζ' - R.e₁ * (c : A) * R.e₁) = 0)
    (hinj : ∀ x : A, x ∈ centralizerLattice S.chain S.b ((i + 1 : ℕ) : ℤ) → R.e₂ * x * R.e₁ = x →
      (s ((c : A) * x - x * c)).restrictScalars F ∈ S.chain.endFiltration 1 →
      x ∈ S.chain.endFiltration ((i + 1 + 1 : ℕ) : ℤ))
    (ρ : Representation ℂ G W)
    [FiniteDimensional ℂ (characterSubspace ρ (H[S,q] (i + 1)) (twist S q.tail i hψ θ c))]
    (hstart : ¬ characterSubspace ρ (H[S,q] (i + 1)) (twist S q.tail i hψ θ c) ≤
      Jacquet.relations ρ ((twist S q.tail i hψ θ c).ker.map (H[S,q] (i + 1)).subtype)) :
    ¬ characterSubspace ρ (H[S,q] (i + 1)) (twist S q.tail i hψ θ c) ≤
      Jacquet.relations ρ (blockUnipotent R.e₁ R.e₂ h₂₁ ⊤) := by
  let H := H[S,q] (i + 1)
  let ϑ := twist S q.tail i hψ θ c
  have hϑ (h : H) : (ϑ h : ℂ) = (θ h : ℂ) *
      elementCharacter (traceCharacter ψF) (c : A) (h : G) := twist_apply S q.tail i hψ θ c h
  have hcentral {a : A} {k : ℤ} (ha : a ∈ S.chain.endFiltration k)
      (hab : Commute a (subfieldEmbedding F E V βE)) : a ∈ centralizerLattice S.chain S.b k := by
    refine ⟨ha, LinearMap.mem_ker.mpr (sub_eq_zero.mpr ?_)⟩
    rw [← hβES]
    exact hab.eq.symm
  have he₁ := hcentral R.e₁_mem (R.e₁_comm βE)
  have he₂ := hcentral R.e₂_mem (R.e₂_comm βE)
  have hζ := hcentral R.ζ_mem (R.ζ_comm βE)
  have hζ' := hcentral R.ζ'_mem (R.ζ'_comm βE)
  obtain ⟨z, y, hz, hz', hyM, hyz, hyϑ, hcov⟩ :=
    exists_shift_element S h0 hS q i hin hcrit hψ hθ hβES hβE s c.2 R.add_eq R.mul_eq h₂₁
      he₁ R.e₂_mem R.ζ_mem R.ζ'_mem R.ζ_mul_ζ' R.ζ'_mul_ζ R.e₁_mul_ζ R.ζ_mul_e₁
      R.e₁_mul_ζ' R.ζ'_mul_e₁ (hβES ▸ (R.ζ_comm βE).eq) (hβES ▸ (R.e₂_comm βE).eq)
      hc₁₂ hc₂₁ hshift ϑ hϑ
  refine unequal_not_le_relations_blockUnipotent S q i hψ hθ ϑ hϑ h₂₁ hc₂₁ ρ hstart y hyM ?_
  intro j v hv hvM
  let M := blockFiltrationUnipotent S.chain h₂₁ (j - 1)
  have hM : M ≤ blockUnipotent R.e₁ R.e₂ h₂₁ ⊤ := blockUnipotent_mono le_top
  have hshifted (h : H) : ρ (z⁻¹ * (h : G) * z) v =
      ((θ h : ℂ) * elementCharacter (traceCharacter ψF) (c : A) (z⁻¹ * (h : G) * z)) • v := by
    let k := z⁻¹ * (h : G) * z
    have hconj : z * k * z⁻¹ = (h : G) := by dsimp [k]; group
    have hkz : z * k * z⁻¹ ∈ H := hconj.symm ▸ h.2
    have hky : y * k * y⁻¹ ∈ H := (hyz k).mpr hkz
    have hval : y⁻¹ * (y * k * y⁻¹) * y = k := by group
    have hact := hv ⟨_, hky⟩
    change ρ (y⁻¹ * (y * k * y⁻¹) * y) v = _ at hact
    rw [hval, hyϑ k hky hkz, show (⟨_, hkz⟩ : H) = h from Subtype.ext hconj] at hact
    exact hact
  let K := lowerBlockSimpleHGroup S q R.add_eq he₁ he₂ (i + 1) (Nat.succ_pos i)
  let ϑK : K →* ℂˣ := ϑ.comp (Subgroup.inclusion (show K ≤ H from fun _ hk => hk.1))
  have hϑK (k : K) : (ϑK k : ℂ) = (θ ⟨k, k.2.1⟩ : ℂ) *
      elementCharacter (traceCharacter ψF) (c : A) k := hϑ ⟨k, k.2.1⟩
  obtain ⟨w, hw, hwM⟩ : ∃ w : W, (∀ k : K, ρ k w = (ϑK k : ℂ) • w) ∧
      w ∉ Jacquet.relations ρ M := by
    by_cases hi : i = 0
    · subst i
      exact exists_isotypic_of_shiftedSimpleLowerH F V S h0 hS q ψF hψ hin hcrit θ hθ
        R.e₁ R.e₂ R.ζ R.ζ' c R.add_eq R.mul_eq h₂₁ he₁ he₂ hζ hζ' R.ζ_mul_ζ'
        R.e₁_mul_ζ R.ζ_mul_e₁ R.e₁_mul_ζ' R.ζ'_mul_e₁ hc₁ hc₂ c.2 z hz hz'
        W ρ M hM ϑK hϑK v hshifted hvM
    · refine exists_isotypic_of_shiftedHOverlap F V S h0 hS q ψF hψ i (by omega)
        (by simpa only [Nat.cast_add, Nat.cast_one] using hin) hcrit θ hθ
        R.e₁ R.e₂ R.ζ R.ζ' c R.add_eq R.mul_eq h₂₁ he₁ he₂ hζ hζ' R.ζ_mul_ζ' R.e₁_mul_ζ'
        hc₁ hc₂ c.2 z hz hz' W ρ M hM ϑK hϑK v ?_ hvM
      intro k hk
      have hky := (hyz (k : G)).mpr hk
      have hchar := (hyϑ (k : G) hky hk).symm.trans
        (congrArg (fun a : ℂˣ => (a : ℂ)) (hcov ⟨k, k.2.1⟩ hky))
      have hz'k : z⁻¹ * (z * (k : G) * z⁻¹) * z = (k : G) := by group
      have ha := hshifted ⟨_, hk⟩
      change ρ (z⁻¹ * (z * (k : G) * z⁻¹) * z) v =
        ((θ ⟨_, hk⟩ : ℂ) * elementCharacter (traceCharacter ψF) (c : A)
          (z⁻¹ * (z * (k : G) * z⁻¹) * z)) • v at ha
      rw [hz'k, hchar] at ha
      exact ha
  exact exists_isotypic_of_lowerBlock S h0 hS q hβES hβE s hE hψ i hin hcrit hθ ϑ c.2 hϑ
    R.add_eq h₂₁ he₁ he₂ he₁₁ he₂₂ hc₁.symm.eq hc₂.symm.eq hinj ρ M hM
    (fun k hk => hw ⟨k, k.2, hk⟩) hwM

set_option maxHeartbeats 1200000 in
private theorem not_le_relations_of_corestricted_split
    (S : Stratum 𝒪[F] F V) (h0 : S.r = 0) (hS : S.IsSimple) (q : S.DefiningSequenceChoice)
    (i : ℕ) (hin : (i : ℤ) + 1 < S.n)
    (hcrit : (((i + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b)
    {ψF : AddChar F ℂ} (hψ : IsBKAdditiveCharacter ψF) {θ : H[S,q] (i + 1) →* ℂˣ}
    (hθ : θ ∈ simpleCharacters ψF S.chain S.n S.b q.tail i)
    {βE : E} (hβES : subfieldEmbedding F E V βE = S.b) (hβE : Algebra.adjoin F ({βE} : Set E) = ⊤)
    (s : TameCorestriction 𝒪[F] F E V) (hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ S.chain.stabilizer)
    (c : S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)))
    (hcop : Nat.Coprime (i + 1) (S.chain.subfieldChain E hE).period)
    (hsplit : (S.chain.corestrictedStratum hE s (i + 1 : ℕ) c).IsSplit)
    (ρ : Representation ℂ G W)
    [FiniteDimensional ℂ (characterSubspace ρ (H[S,q] (i + 1)) (twist S q.tail i hψ θ c))]
    (hstart : ¬ characterSubspace ρ (H[S,q] (i + 1)) (twist S q.tail i hψ θ c) ≤
      Jacquet.relations ρ ((twist S q.tail i hψ θ c).ker.map (H[S,q] (i + 1)).subtype)) :
    ∃ (e₁ e₂ : A) (h₂₁ : e₂ * e₁ = 0), e₁ + e₂ = 1 ∧ e₁ * e₂ = 0 ∧ e₁ ≠ 0 ∧ e₂ ≠ 0 ∧
      ¬ characterSubspace ρ (H[S,q] (i + 1)) (twist S q.tail i hψ θ c) ≤
        Jacquet.relations ρ (blockUnipotent e₁ e₂ h₂₁ ⊤) := by
  obtain ⟨B⟩ := nonempty_splitBlockData_corestricted S.chain hE s (Nat.succ_pos i) c hcop hsplit
  let R := B.restrict S.chain hE rfl
  have h₂₁ : R.e₂ * R.e₁ = 0 := congrArg (LinearMap.restrictScalars F) B.e₂_mul_e₁
  have he₁₁ : R.e₁ * R.e₁ = R.e₁ := congrArg (LinearMap.restrictScalars F) B.e₁_mul_e₁
  have he₂₂ : R.e₂ * R.e₂ = R.e₂ := congrArg (LinearMap.restrictScalars F) B.e₂_mul_e₂
  let d : S.chain.endFiltration (-((i + 1 : ℕ) : ℤ)) :=
    ⟨R.e₁ * (c : A) * R.e₁ + R.e₂ * (c : A) * R.e₂,
      add_mem
        (mul_mul_mem_endFiltration S.chain R.e₁_mem c.2 R.e₁_mem (by simp))
        (mul_mul_mem_endFiltration S.chain R.e₂_mem c.2 R.e₂_mem (by simp))⟩
  have hsd : s (d : A) = s c := B.corestriction_diagonal s rfl
  have hscd : s ((c : A) - d) = 0 := by
    rw [map_sub, hsd, sub_self]
  have hd₁ : Commute (d : A) R.e₁ := by
    change (_ + _) * R.e₁ = R.e₁ * (_ + _)
    simp only [add_mul, mul_add, mul_assoc, he₁₁, h₂₁, mul_zero]
    simp only [← mul_assoc, he₁₁, R.mul_eq, zero_mul, add_zero]
  have hd₂ : Commute (d : A) R.e₂ := by
    change (_ + _) * R.e₂ = R.e₂ * (_ + _)
    simp only [add_mul, mul_add, mul_assoc, he₂₂, R.mul_eq, mul_zero, zero_add]
    simp only [← mul_assoc, he₂₂, h₂₁, zero_mul, zero_add]
  have hd₁₂ : R.e₁ * (d : A) * R.e₂ = 0 := by
    rw [← hd₁.eq, mul_assoc, R.mul_eq, mul_zero]
  have hd₂₁ : R.e₂ * (d : A) * R.e₁ = 0 := by
    rw [← hd₂.eq, mul_assoc, h₂₁, mul_zero]
  have hshift : s (R.ζ * (R.e₁ * (d : A) * R.e₁) * R.ζ' - R.e₁ * (d : A) * R.e₁) = 0 :=
    B.corestriction_shift_sub s hsd
  have hinj (x : A) (hx : x ∈ centralizerLattice S.chain S.b ((i + 1 : ℕ) : ℤ))
      (hx₂₁ : R.e₂ * x * R.e₁ = x)
      (hcx : (s ((d : A) * x - x * d)).restrictScalars F ∈ S.chain.endFiltration 1) :
      x ∈ S.chain.endFiltration ((i + 1 + 1 : ℕ) : ℤ) := by
    rw [← hβES] at hx
    simpa only [Nat.cast_add, Nat.cast_one] using
      B.graded_commutator_lower_restrict S.chain hE s c hsd hβE hx hx₂₁ hcx
  obtain ⟨g, hg, hgchar⟩ := exists_conj_twist_character S h0 hS q i hin hcrit hψ hθ
    hβES hβE s c.2 d.2 hscd
  let H := H[S,q] (i + 1)
  let χ := twist S q.tail i hψ θ c
  let χ' := twist S q.tail i hψ θ d
  let α := MulAut.conj g
  let ρ' := ρ.comp α.toMonoidHom
  let κ := conjEndo H g (fun k hk => (Subgroup.mem_normalizer_iff.mp hg k).mp hk)
  have hκ (h : H) : χ (κ h) = χ' h := by
    apply Units.ext
    change (twist S q.tail i hψ θ c (κ h) : ℂ) = (twist S q.tail i hψ θ d h : ℂ)
    rw [twist_apply, twist_apply]
    exact hgchar h (κ h).2
  have hκsurj : Function.Surjective κ := by
    intro h
    refine ⟨⟨α.symm (h : G), (Subgroup.mem_normalizer_iff''.mp hg (h : G)).mp h.2⟩, ?_⟩
    apply Subtype.ext
    exact α.apply_symm_apply (h : G)
  have hsub : characterSubspace ρ' H χ' = characterSubspace ρ H χ := by
    ext v
    constructor
    · intro hv k
      obtain ⟨h, rfl⟩ := hκsurj k
      change ρ' (h : G) v = (χ (κ h) : ℂ) • v
      rw [hκ]
      exact hv h
    · intro hv h
      change ρ (κ h : G) v = (χ' h : ℂ) • v
      rw [← hκ]
      exact hv (κ h)
  have hker : (χ'.ker.map H.subtype).map α.toMonoidHom ≤ χ.ker.map H.subtype := by
    rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
    refine ⟨κ h, ?_, rfl⟩
    exact MonoidHom.mem_ker.mpr ((hκ h).trans (MonoidHom.mem_ker.mp hh))
  have hstart' : ¬ characterSubspace ρ' H χ' ≤ Jacquet.relations ρ' (χ'.ker.map H.subtype) := by
    rw [hsub, relations_comp_mulEquiv]
    exact fun h => hstart (h.trans (Jacquet.relations_mono ρ hker))
  have : FiniteDimensional ℂ (characterSubspace ρ' H χ') := by
    rw [hsub]
    infer_instance
  have hmain := not_le_relations_of_split_twist S h0 hS q i hin hcrit hψ hθ hβES hβE
    s hE R h₂₁ he₁₁ he₂₂ d hd₁ hd₂ hd₁₂ hd₂₁ hshift hinj ρ' hstart'
  let C := (LinearMap.GeneralLinearGroup.toLinearEquiv g).conjRingEquiv
  have hsum : C R.e₁ + C R.e₂ = 1 := by rw [← map_add, R.add_eq, map_one]
  have h12 : C R.e₁ * C R.e₂ = 0 := by rw [← map_mul, R.mul_eq, map_zero]
  have h21 : C R.e₂ * C R.e₁ = 0 := by rw [← map_mul, h₂₁, map_zero]
  refine ⟨C R.e₁, C R.e₂, h21, hsum, h12, ?_, ?_, ?_⟩
  · exact fun h => R.e₁_ne (C.injective (h.trans C.map_zero.symm))
  · exact fun h => R.e₂_ne (C.injective (h.trans C.map_zero.symm))
  · change ¬ characterSubspace ρ H χ ≤ _
    rw [← hsub]
    intro h
    apply hmain
    change characterSubspace ρ' H χ' ≤ Jacquet.relations ρ' _
    rw [relations_comp_mulEquiv]
    refine h.trans (Jacquet.relations_mono _ ?_)
    intro u hu
    let w := α.symm u
    refine ⟨w, ?_, α.apply_symm_apply u⟩
    have hCu : C (w : A) = (u : A) := congrArg Units.val (α.apply_symm_apply u)
    refine ⟨C.injective ?_, AddSubgroup.mem_top _⟩
    simpa only [map_mul, map_sub, map_one, hCu] using hu.1

end Endomorphisms

set_option maxHeartbeats 1200000 in
/-- **BK93 (8.2.5)(iv), unequal positive levels.** A split type of level `(x,y)` with `x > y > 0`
in an irreducible admissible smooth representation gives a nonzero proper Jacquet module. -/
theorem unequalPositiveSplitTypeJacquet : UnequalPositiveSplitTypeJacquetStatement.{uF, uπ, uρ} := by
  intro F _ _ _ _ n _ ψF _ π _ hadm K ρ x y htype hc
  have hK := IsGLSplitType.isCompact_isOpen (n := n) (K := K) (ψF := ψF) (ρ := ρ)
    (Or.inl (Or.inr ⟨x, y, htype⟩))
  obtain ⟨hψ, T, q, j, hT, hr, -, -, hcop, θ, hθ, c, s, hsplit, hiso⟩ := htype
  let V := Fin n → F
  let E := elementAlgebra T.b
  let : Field E := hT.1.1.fst.toField
  let : FiniteDimensional F E := T.chain.finiteDimensional_subfield E
  have hE : ∀ a : Eˣ, subfieldUnits F E V a ∈ T.chain.stabilizer := hT.1.1.snd
  let βE : E := ⟨T.b, Algebra.self_mem_adjoin_singleton F T.b⟩
  have hβES : subfieldEmbedding F E V βE = T.b := by ext v; rfl
  have hβE : Algebra.adjoin F ({βE} : Set E) = ⊤ := SimpleStratumLabel.adjoin_generator_eq_top T.b
  have h0 : 0 ≤ T.r := by omega
  let S := T.lowerIndex 0 h0
  have hS : S.IsSimple := hT.lowerIndex h0
  let q' := q.lowerIndex h0
  have hin : (j : ℤ) + 1 < S.n := by
    change (j : ℤ) + 1 < T.n
    rw [← hr]
    exact T.r_lt_n
  have hcrit : (((j + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth S.chain S.b := by
    change (((j + 1 : ℕ) : ℤ) : WithTop ℤ) < simpleCriticalDepth T.chain T.b
    simpa only [hr, Nat.cast_add, Nat.cast_one] using
      Stratum.IsSimple.lt_simpleCriticalDepth (S := T) hT
  have hθ' : ∃ θ' ∈ simpleCharacters ψF S.chain S.n S.b q'.tail j,
      IsPairIsomorphic (glRepresentationToAut ρ) (characterRepresentation (twist S q'.tail j hψ θ' c)) := by
    change ∃ θ' ∈ simpleCharacters ψF T.chain T.n T.b (q.lowerIndex h0).tail j,
      IsPairIsomorphic (glRepresentationToAut ρ)
        (characterRepresentation (twist T (q.lowerIndex h0).tail j hψ θ' c))
    rw [Stratum.DefiningSequenceChoice.lowerIndex_tail]
    exact ⟨θ, hθ, hiso⟩
  obtain ⟨θ', hθ', hiso'⟩ := hθ'
  refine jacquet_nonvanishing_of_characterType π hadm ρ (twist S q'.tail j hψ θ' c) hiso'
    hK.1 hK.2 hc ?_
  intro π' _ hstart
  exact not_le_relations_of_corestricted_split S rfl hS q' j hin hcrit hψ hθ' hβES hβE
    s hE c hcop hsplit π' hstart

end Langlands.BushnellKutzko.SplitBlocks
