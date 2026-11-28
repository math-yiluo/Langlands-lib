import Langlands.BushnellKutzko.SmoothStratumContainment
import Langlands.BushnellKutzko.SplitTypeExistenceSteps
import Langlands.BushnellKutzko.DiagonalPositiveSplitType
import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.BushnellKutzko.NonsplitRefinementProof
import Langlands.BushnellKutzko.SimpleCharacterRestrictionHigh
import Langlands.BushnellKutzko.SimpleCharacterRestrictionCutoff
import Langlands.BushnellKutzko.SimpleCharacterTransferHigh
import Langlands.BushnellKutzko.SimpleCharacterTransferRelative
import Langlands.BushnellKutzko.SimpleCharacterTransferSequences

/-! # The positive-level initial step of BK93 (8.1.5)

A proof of `PositiveLevelInitialStepStatement`: an irreducible smooth representation `π` of
`GL_N(F)` with no nonzero vector fixed by any `U^1(𝔄)` contains a split type of level `(x, x)`
or a simple character of a simple stratum (BK93 (8.1.5), printed p. 268).

A nonzero vector of `π` is fixed by some `U^{l+1}(𝔄)`. Among all such pairs take one of minimal
normalized level `m / e(𝔄)` with `gcd(m, e(𝔄)) = 1` (`exists_minimal_fixed_level`); then
`U^m(𝔄)` acts on a nonzero vector by `ψ_b` with `b ∈ 𝔓^{-m}`
(`LatticeChain.exists_traceCharacter_eigenvector`), and the stratum `[𝔄, m, m-1, b]` is
fundamental (`LatticeChain.not_isNilpotent_add_of_minimal`). If it is split, `(U^m(𝔄), ψ_b)` is a
split type of level `(m/e, m/e)`. Otherwise it is nonsplit, and BK93 (2.3.4)
(`PureApproximation.nonsplitRefinement`) gives a simple stratum `[𝔅, n', n'-1, c]` whose
character `ψ_c` of `U^{n'}(𝔅) = H^{n'}(c, 𝔅)` is a simple character contained in `π`.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uπ uρ uV

/-! ### Simple characters of terminal defining sequences -/

section Terminal

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem Stratum.terminalDefiningSequence_tail (S : Stratum 𝒪[F] F V) (hS : S.IsSimple)
    (h : criticalExponent S.chain S.b = ((-S.n : ℤ) : WithBot ℤ) ∨
      criticalExponent S.chain S.b = ⊥) :
    (S.terminalDefiningSequence hS h).tail = [] :=
  rfl

/-- A simple stratum `[𝔄, n, n-1, β]` has critical exponent `-n` or `-∞`, so it has a defining
sequence of length one. -/
theorem Stratum.criticalExponent_eq_of_isSimple [FiniteDimensional F V] (S : Stratum 𝒪[F] F V)
    (hS : S.IsSimple) (hr : S.r = S.n - 1) :
    criticalExponent S.chain S.b = ((-S.n : ℤ) : WithBot ℤ) ∨
      criticalExponent S.chain S.b = ⊥ := by
  cases h : criticalExponent S.chain S.b with
  | bot => exact .inr rfl
  | coe k =>
    left
    have hlow := neg_n_le_criticalExponent minimalCriticalExponent S hS.1 h
    have hup := hS.2
    rw [h] at hup
    have hup' := WithBot.coe_lt_coe.mp hup
    rw [show k = -S.n by omega]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The membership condition of `C(𝔄, m, β)` for the empty tail. -/
theorem mem_simpleCharacters_of_tail_eq_nil (ψF : AddChar F ℂ) (L : LatticeChain 𝒪[F] F V)
    (n : ℤ) (β : A) {tail : List A} (htail : tail = []) (m : ℕ)
    (θ : simpleHGroup L n β tail (m + 1) →* ℂˣ)
    (h₁ : ∀ g : simpleHGroup L n β tail (m + 1),
      (g : G) ∈ L.unitFiltration (simpleHCutoff n).toNat →
        (θ g : ℂ) = elementCharacter (traceCharacter ψF) β g)
    (h₂ : factorsThroughCentralizerDet β θ) :
    θ ∈ simpleCharacters ψF L n β tail m := by
  subst htail
  exact ⟨h₁, h₂⟩

/-- **The trace character of a pure element factors through the determinant at high depth.**
Let `[𝔄, n, r, β]` be pure, so that `E = F[β]` is a field, and let `n < 2k`. Then on
`U^k(𝔄) ∩ B_β^×`, where `B_β = End_E(V)`, the character `ψ_β` is a function of the
`E`-determinant: the determinant condition of BK93 (3.2.1), printed p. 98, holds for `ψ_β`.
The computation `det(1 + x) ≡ 1 + tr_E(x)` is `elementCharacter_eq_relativeDet_of_highDepth`. -/
theorem factorsThroughCentralizerDet_elementCharacterHom (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (S : Stratum 𝒪[F] F V) (hS : S.IsPure) {k : ℕ}
    (hk : S.n < 2 * (k : ℤ)) (hb : S.b ∈ S.chain.endFiltration (-S.n))
    (hk1 : 1 ≤ -S.n + ((k : ℤ) + k)) {H : Subgroup G} (hH : H ≤ S.chain.unitFiltration k) :
    factorsThroughCentralizerDet S.b (elementCharacterHom S.chain ψF hψ hb hk1 hH) := by
  obtain ⟨⟨hE, hnormalize⟩, hval⟩ := hS
  let E := elementAlgebra S.b
  let : Field E := hE.toField
  let := S.chain.finiteDimensional
  let := S.chain.finiteDimensional_subfield E
  let := LocalField.FiniteExtension.normedField F E
  let := LocalField.FiniteExtension.valuativeRel F E
  let := LocalField.FiniteExtension.isLocalField F E
  let C := S.chain.relativeLatticeChain hnormalize (isIntegral_iff_mem_spectralInteger F E)
  have hC := S.chain.mem_relativeLatticeChain hnormalize (isIntegral_iff_mem_spectralInteger F E)
  have hgen := subfieldEmbedding_elementGenerator S.b hE
  have hb0 : elementGenerator S.b ≠ 0 := by
    intro h0
    have h : S.b = 0 := congrArg Subtype.val h0
    rw [h, S.chain.valuation_zero] at hval
    exact WithTop.top_ne_coe hval
  refine (factorsThroughCentralizerDet_iff hE _).mpr ?_
  intro x hx
  apply Units.ext
  rw [Units.val_one]
  change elementCharacter (traceCharacter ψF) S.b
    (relativeEndUnits E (x : (Module.End E V)ˣ)) = 1
  have hxk : (x : (Module.End E V)ˣ) ∈ C.unitFiltration k :=
    (S.chain.mem_unitFiltration_restrictScalars_iff C hC k x).mp (hH x.2)
  have htr := elementCharacter_eq_relativeDet_of_highDepth S.chain C hC ψF hψ
    (elementGenerator S.b) hb0 S.n (by rw [hgen]; exact hval) k hk x hxk
  rw [hgen] at htr
  have hdet : LinearMap.det ((x : (Module.End E V)ˣ) : Module.End E V) = 1 :=
    congrArg Units.val hx
  rw [htr, hdet, sub_self, mul_zero, map_zero, AddChar.map_zero_eq_one]

end Terminal

/-! ### The two branches in `GL_N(F)` -/

section Branches

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {n : ℕ}

local notation "Aut" => (Module.End F (Fin n → F))ˣ
set_option quotPrecheck false in
local notation "toG" => (Matrix.GeneralLinearGroup.toLin (n := Fin n) (R := F)).symm

/-- A character `χ` of a group, acting by scalars on `ULift ℂ`. -/
def liftedCharacterRepresentation {H : Type*} [Group H] (χ : H →* ℂˣ) :
    Representation ℂ H (ULift.{uρ} ℂ) where
  toFun h := (χ h : ℂ) • LinearMap.id
  map_one' := by
    rw [map_one, Units.val_one, one_smul]
    rfl
  map_mul' h h' := by
    refine LinearMap.ext fun z => ?_
    simp [mul_smul]
    exact smul_comm _ _ _

theorem liftedCharacterRepresentation_apply {H : Type*} [Group H] (χ : H →* ℂˣ) (h : H)
    (z : ULift.{uρ} ℂ) : liftedCharacterRepresentation χ h z = (χ h : ℂ) • z :=
  rfl

/-- **The split branch** (BK93 (8.1.5), printed p. 268). Let `[𝔄, n, n-1, b]` be a split
fundamental stratum with `n > 0` and `gcd(n, e(𝔄)) = 1`, and let `U^n(𝔄)` act on a nonzero vector
of `π` by `ψ_b`. Then `π` contains a pair `(K, ρ)` in `GL_N(F)` whose transport to `Aut_F(F^N)` is
a split type of level `(n/e(𝔄), n/e(𝔄))` (BK93 (8.1.1)): `K` is the preimage of `U^n(𝔄)` and `ρ`
is `ψ_b` on a one-dimensional space. -/
theorem exists_containsType_diagonalPositiveSplitType (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (S : Stratum 𝒪[F] F (Fin n → F)) (hn : 0 < S.n) (hS : S.IsSplit)
    (hcop : Nat.Coprime S.n.toNat S.chain.period) {v : π} (hv0 : v ≠ 0)
    (hv : ∀ u ∈ S.chain.unitFiltration S.n.toNat,
      π.representation (toG u) v = elementCharacter (traceCharacter ψF) S.b u • v) :
    ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K), ContainsType π ρ ∧
      ∃ x : ℚ, IsDiagonalPositiveSplitType (V := Fin n → F) ψF x (glRepresentationToAut ρ) := by
  have hm : 0 < S.n.toNat := by omega
  have hb : S.b ∈ S.chain.endFiltration (-(S.n.toNat : ℤ)) := by
    rw [Int.toNat_of_nonneg hn.le]
    exact PureApproximation.mem_endFiltration_of_le_valuation S.chain
      (by exact_mod_cast S.valuation_ge)
  let χ := filtrationTraceCharacter S.chain ψF hψ hm hb
  let U := S.chain.unitFiltration S.n.toNat
  let toAut : GeneralLinear n F →* Aut := (Matrix.GeneralLinearGroup.toLin).toMonoidHom
  let K : Subgroup (GeneralLinear n F) := U.comap toAut
  let χK : K →* ℂˣ := χ.comp (toAut.subgroupComap U)
  have hχK : ∀ k : K, (χK k : ℂ) =
      elementCharacter (traceCharacter ψF) S.b (Matrix.GeneralLinearGroup.toLin (k : _)) :=
    fun k => filtrationTraceCharacter_apply S.chain ψF hψ hm hb _
  let ρ0 : Representation ℂ K (ULift.{uρ} ℂ) := liftedCharacterRepresentation χK
  -- smoothness: `U^{n+1}(𝔄)` acts trivially
  have hsmooth : IsSmooth ρ0 := by
    intro z
    let _ : TopologicalSpace (Module.End F (Fin n → F)) := endTopology
    let U1 := S.chain.unitFiltration (S.n.toNat + 1)
    let K1 : Subgroup K := (U1.comap toAut).subgroupOf K
    have hopen : IsOpen (K1 : Set K) :=
      ((isOpen_unitFiltration S.chain (S.n.toNat + 1)).preimage
        generalLinearToLinContinuous.continuous).preimage continuous_subtype_val
    refine ⟨⟨K1, hopen⟩, (Representation.mem_invariants _ z).mpr fun g => ?_⟩
    change (χK (g : K) : ℂ) • z = z
    have h1 : χK (g : K) = 1 :=
      filtrationTraceCharacter_eq_one S.chain ψF hψ hm hb _ (g.2 : _)
    rw [h1, Units.val_one, one_smul]
  let ρ : SmoothRep.{0, uF, uρ} ℂ K := SmoothRep.of ρ0 hsmooth
  refine ⟨K, ρ, ?_, _, hψ, S, hn, hS, hcop, rfl, ?_⟩
  · -- `z ↦ z • v` is a nonzero intertwiner
    let φ : ULift.{uρ} ℂ →ₗ[ℂ] π :=
      (LinearMap.toSpanSingleton ℂ π v).comp ULift.moduleEquiv.toLinearMap
    have hφ : ∀ z : ULift.{uρ} ℂ, φ z = z.down • v := fun z => rfl
    refine ⟨⟨φ, fun k => LinearMap.ext fun z => ?_⟩, fun h0 => hv0 ?_⟩
    · change φ ((χK k : ℂ) • z) = π.representation (k : GeneralLinear n F) (φ z)
      have hk : toG (Matrix.GeneralLinearGroup.toLin (k : GeneralLinear n F)) =
          (k : GeneralLinear n F) :=
        MulEquiv.symm_apply_apply _ _
      rw [hφ, hφ, map_smul, ← hk, hv (Matrix.GeneralLinearGroup.toLin (k : GeneralLinear n F)) k.2,
        hχK]
      change (elementCharacter (traceCharacter ψF) S.b
          (Matrix.GeneralLinearGroup.toLin (k : GeneralLinear n F)) * z.down) • v = _
      rw [mul_smul]
      exact smul_comm _ _ _
    · have h := congrArg (fun f : ρ.representation.IntertwiningMap
          (π.representation.comp K.subtype) => f.toLinearMap (ULift.up 1)) h0
      simpa [hφ] using h
  · -- the transported pair is `(U^n(𝔄), ψ_b)`
    have hKU : glSubgroupToAut K = U :=
      Subgroup.map_comap_eq_self_of_surjective (Matrix.GeneralLinearGroup.toLin).surjective U
    have hkey : ∀ y : glSubgroupToAut K,
        Matrix.GeneralLinearGroup.toLin ((glSubgroupToAutEquiv K).symm y : GeneralLinear n F) =
          (y : Aut) := fun y =>
      congrArg Subtype.val ((glSubgroupToAutEquiv K).apply_symm_apply y)
    refine ⟨hKU, ⟨Representation.Equiv.mk ULift.moduleEquiv fun g => LinearMap.ext fun z => ?_⟩⟩
    change ((χK ((glSubgroupToAutEquiv K).symm ((MulEquiv.subgroupCongr hKU).symm g)) : ℂ) •
        z).down = (χ g : ℂ) * z.down
    rw [hχK, hkey, filtrationTraceCharacter_apply]
    rfl

/-- **The nonsplit branch** (BK93 (8.1.5), printed p. 268, with (2.3.4)). Let `[𝔄, n, n-1, b]` be
a nonsplit fundamental stratum with `n > 0`, and let `U^n(𝔄)` act on a nonzero vector of `π` by
`ψ_b`. Then `π` contains a simple character of a simple stratum `[𝔅, n', n'-1, c]`: the character
`ψ_c` of `H^{n'}(c, 𝔅) = U^{n'}(𝔅)`, for the defining sequence of length one. -/
theorem exists_containsSimpleCharacter_of_isNonsplit (ψF : AddChar F ℂ)
    (hψ : IsBKAdditiveCharacter ψF) (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F))
    (S : Stratum 𝒪[F] F (Fin n → F)) (hn : 0 < S.n) (hS : S.IsNonsplit) {v : π} (hv0 : v ≠ 0)
    (hv : ∀ u ∈ S.chain.unitFiltration S.n.toNat,
      π.representation (toG u) v = elementCharacter (traceCharacter ψF) S.b u • v) :
    ∃ T : Stratum 𝒪[F] F (Fin n → F), ContainsSimpleCharacter ψF π T := by
  classical
  obtain ⟨T, hT, hTr, hcoset, hper, -⟩ :=
    PureApproximation.nonsplitRefinement F (Fin n → F) S hS
  have hSr : S.r = S.n - 1 := hS.1.1
  have hTn : 0 < T.n := by
    have h1 : (0 : ℤ) < S.chain.period := by exact_mod_cast S.chain.period_pos
    have h2 : (0 : ℤ) < T.chain.period := by exact_mod_cast T.chain.period_pos
    by_contra h
    have h3 : T.n * (S.chain.period : ℤ) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) h1.le
    have h4 : 0 < S.n * (T.chain.period : ℤ) := Int.mul_pos hn h2
    omega
  -- `S.b ∈ T.b + 𝔓^{1-n'}(𝔅)` and `𝔓^{1-n}(𝔄) ⊆ 𝔓^{1-n'}(𝔅)`
  have hbT : S.b - T.b ∈ T.chain.endFiltration (1 - T.n) := by
    have h := hcoset (show S.b - S.b ∈ S.chain.endFiltration (-S.r) by
      rw [sub_self]; exact zero_mem _)
    change S.b - T.b ∈ T.chain.endFiltration (-T.r) at h
    rwa [show -T.r = 1 - T.n by omega] at h
  have hsub : S.chain.endFiltration (1 - S.n) ≤ T.chain.endFiltration (1 - T.n) := by
    intro y hy
    have h1 := hcoset (show S.b + y - S.b ∈ S.chain.endFiltration (-S.r) by
      rw [add_sub_cancel_left, show -S.r = 1 - S.n by omega]; exact hy)
    change S.b + y - T.b ∈ T.chain.endFiltration (-T.r) at h1
    rw [show -T.r = 1 - T.n by omega] at h1
    have h3 := sub_mem h1 hbT
    rwa [show S.b + y - T.b - (S.b - T.b) = y by abel] at h3
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  have hdual := LatticeChain.endFiltration_one_sub_le hϖ S.chain T.chain hsub
  rw [sub_sub_cancel, sub_sub_cancel] at hdual
  -- `U^{n'}(𝔅) ⊆ U^n(𝔄)`
  set k := T.n.toNat with hkdef
  have hk : (k : ℤ) = T.n := Int.toNat_of_nonneg hTn.le
  have hU : T.chain.unitFiltration k ≤ S.chain.unitFiltration S.n.toNat :=
    S.chain.unitFiltration_le_of_endFiltration_le T.chain (by omega) (by
      rw [hk, Int.toNat_of_nonneg hn.le]
      exact hdual)
  -- the simple character `ψ_c` of `H^{n'}(c, 𝔅) = U^{n'}(𝔅)`
  let q := T.terminalDefiningSequence hT (T.criticalExponent_eq_of_isSimple hT hTr)
  have hrk : T.r.toNat + 1 = k := by omega
  have hH : simpleHGroup T.chain T.n T.b q.tail (T.r.toNat + 1) = T.chain.unitFiltration k := by
    rw [simpleHGroup_eq_unitFiltration_at_high_index q (by omega), hrk]
  have hTb : T.b ∈ T.chain.endFiltration (-T.n) :=
    PureApproximation.mem_endFiltration_of_le_valuation T.chain
      (by exact_mod_cast T.valuation_ge)
  have hk1 : 1 ≤ -T.n + ((k : ℤ) + k) := by omega
  let θ := elementCharacterHom T.chain ψF hψ hTb hk1 hH.le
  refine ⟨T, hT, by omega, q, θ, ?_, v, hv0, fun u => ?_⟩
  · exact mem_simpleCharacters_of_tail_eq_nil ψF T.chain T.n T.b
      (T.terminalDefiningSequence_tail hT _) _ θ (fun g _ => rfl)
      (factorsThroughCentralizerDet_elementCharacterHom ψF hψ T hT.1 (by omega) hTb hk1 hH.le)
  · have huk : (u : Aut) ∈ T.chain.unitFiltration k := hH.le u.2
    change π.representation (toG (u : Aut)) v =
      elementCharacter (traceCharacter ψF) T.b (u : Aut) • v
    rw [hv _ (hU huk)]
    congr 1
    have h1 := elementCharacter_eq_one_of_depth T.chain ψF hψ hbT
      (show 1 ≤ (1 - T.n) + (k : ℤ) by omega) huk
    rw [elementCharacter_apply] at h1 ⊢
    rw [elementCharacter_apply,
      show S.b * (((u : Aut) : Module.End F (Fin n → F)) - 1) =
        T.b * (((u : Aut) : Module.End F (Fin n → F)) - 1) +
          (S.b - T.b) * (((u : Aut) : Module.End F (Fin n → F)) - 1) by
          rw [← add_mul]; congr 1; abel,
      AddChar.map_add_eq_mul, h1, mul_one]

end Branches

/-! ### Proof of the positive-level initial step -/

set_option quotPrecheck false in
/-- **BK93 (8.1.5), positive level (printed p. 268).** An irreducible smooth representation of
`GL_N(F)` with no nonzero vector fixed by any `U^1(𝔄)` contains a split type of level `(x, x)` or a
simple character of a simple stratum. -/
theorem positiveLevelInitialStep : PositiveLevelInitialStepStatement.{uF, uπ, uρ} := by
  intro F _ _ _ _ n hn ψF hψ π hirr hnone
  -- a nonzero vector of `π`
  have : Nontrivial π := by
    have : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F))
        π.representation.asModule :=
      (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
    exact IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F))
      π.representation.asModule
  obtain ⟨w, hw⟩ := exists_ne (0 : π)
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  -- it is fixed by `U^{l+1}(𝔄)` for the standard chain and some `l`
  have hex : ∃ (𝓛 : LatticeChain 𝒪[F] F (Fin (n' + 1) → F)) (l : ℕ) (w : π), w ≠ 0 ∧
      ∀ u ∈ 𝓛.unitFiltration (l + 1),
        π.representation ((Matrix.GeneralLinearGroup.toLin (n := Fin (n' + 1)) (R := F)).symm u)
          w = w := by
    obtain ⟨K0, hK0⟩ := π.isSmooth w
    obtain ⟨N, hN, hKN⟩ :=
      Conductor.exists_pos_principalLevelOpenSubgroup_subset F n' K0.mem_nhds_one
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
    refine ⟨LatticeChain.standard hϖ (Fin (n' + 1)), N - 1, w, hw, fun u hu => ?_⟩
    rw [Nat.sub_add_cancel hN] at hu
    have hh : (Matrix.GeneralLinearGroup.toLin.symm u : GeneralLinear (n' + 1) F) ∈ K0 :=
      hKN (unitSubgroup_stdChain_le hϖ n' N _ (by rwa [MulEquiv.apply_symm_apply]))
    exact (Representation.mem_invariants _ w).mp hK0 ⟨_, hh⟩
  -- no nonzero vector is fixed by any `U^1(𝔄)`
  have hnone' : ∀ (𝓛 : LatticeChain 𝒪[F] F (Fin (n' + 1) → F)) (w : π), w ≠ 0 →
      ¬ ∀ u ∈ 𝓛.unitFiltration 1,
        π.representation ((Matrix.GeneralLinearGroup.toLin (n := Fin (n' + 1)) (R := F)).symm u)
          w = w := by
    intro 𝓛 w hw0 hfix
    refine hnone 𝓛 ⟨w, hw0, fun u => ?_⟩
    rw [hfix _ u.2, MonoidHom.one_apply, Units.val_one, one_smul]
  -- a fundamental stratum at the minimal normalized level
  obtain ⟨𝓛, m, w, hm1, hcop, hw0, hwfix, hmin⟩ :=
    exists_minimal_fixed_level π.representation hex hnone'
  obtain ⟨b, hb, v, hv0, hv⟩ :=
    𝓛.exists_traceCharacter_eigenvector π.representation ψF hψ.1 hψ.2 hm1 hw0 hwfix
  have hnil := 𝓛.not_isNilpotent_add_of_minimal π.representation ψF hψ.1 hm1 hb hv0 hv hmin
  let S : Stratum 𝒪[F] F (Fin (n' + 1) → F) :=
    ⟨𝓛, m, (m : ℤ) - 1, b, by omega,
      by exact_mod_cast PureApproximation.le_valuation_of_mem 𝓛 hb⟩
  have hSn : 0 < S.n := by
    change (0 : ℤ) < m
    omega
  have hSm : S.n.toNat = m := Int.toNat_natCast m
  have hfund : S.IsFundamental := by
    refine ⟨by change (m : ℤ) - 1 = m - 1; rfl, fun x hx => ?_⟩
    have hx' : x - b ∈ 𝓛.endFiltration (1 - (m : ℤ)) := by
      have h : x - b ∈ 𝓛.endFiltration (-((m : ℤ) - 1)) := hx
      rwa [neg_sub] at h
    have h := hnil (x - b) hx'
    rwa [add_sub_cancel] at h
  have hv' : ∀ u ∈ S.chain.unitFiltration S.n.toNat,
      π.representation ((Matrix.GeneralLinearGroup.toLin (n := Fin (n' + 1)) (R := F)).symm u)
        v = elementCharacter (traceCharacter ψF) S.b u • v := by
    rw [hSm]
    exact hv
  by_cases hsplit : S.IsSplit
  · left
    exact exists_containsType_diagonalPositiveSplitType ψF hψ π S hSn hsplit
      (by rw [hSm]; exact hcop) hv0 hv'
  · right
    exact exists_containsSimpleCharacter_of_isNonsplit ψF hψ π S hSn
      (S.isNonsplit_of_not_isSplit hfund hsplit) hv0 hv'

end Langlands.BushnellKutzko
