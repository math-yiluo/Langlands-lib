import Langlands.Correspondence.HenniartExtensionDeterminant
import Langlands.Correspondence.HenniartExtensionInputs
import Langlands.Correspondence.HenniartTwistBridge
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof
import Langlands.LocalField.SmoothCharacterNormProof

/-!
# Supercuspidal classes as unramified twists of unitary classes

Henniart (1993), §4.3: every supercuspidal class of `GL_n(K)` is an unramified
twist of a unitary class whose central character has finite order. A real power
of `|det|` makes the class unitarizable (the published
`supercuspidalRepRealUnitarization`). Its central character then has modulus one,
and a further twist by an unramified character of modulus one makes the central
character trivial at the uniformizer. A character of `K^×` with open kernel that
is trivial at the uniformizer has finite order, because the norm-one units are
compact.
-/

noncomputable section

namespace Langlands.Henniart.Extension

open Langlands.Correspondence Langlands.VirtualRepresentation StableMap

universe uK uW uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

local instance henniartUnitaryTwistFieldTopology : TopologicalSpace K.Carrier :=
  K.canonicalTopologicalData.topology

local instance henniartUnitaryTwistGLTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n K.Carrier) :=
  K.canonicalGeneralLinearTopology n

/-- A character of `K^×` with open kernel that is trivial at the uniformizer has
finite order. -/
theorem isOfFinOrder_of_isOpen_ker_of_uniformizer (ω : K.Carrierˣ →* ℂˣ)
    (hω : IsOpen (ω.ker : Set K.Carrierˣ))
    (h1 : ω K.canonicalTopologicalData.uniformizerUnit = 1) : IsOfFinOrder ω := by
  set T := K.canonicalTopologicalData
  let := T.valuativeRel
  let := T.localField
  let C : Subgroup K.Carrierˣ := T.ordUnits.ker
  have hC : IsCompact (C : Set K.Carrierˣ) := by
    have h := T.isCompact_normalizedAbs_eq_one_units
    convert h using 1
    ext a
    change T.ord (a : K.Carrier) = 0 ↔ T.normalizedAbs (a : K.Carrier) = 1
    exact T.ord_eq_zero_iff_normalizedAbs a
  have : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let U : Subgroup C := ω.ker.subgroupOf C
  have hU : IsOpen (U : Set C) := Subgroup.subgroupOf_isOpen C ω.ker hω
  have : Finite (C ⧸ U) := Subgroup.quotient_finite_of_isOpen U hU
  refine isOfFinOrder_iff_pow_eq_one.mpr
    ⟨U.index, Nat.pos_of_ne_zero U.index_ne_zero_of_finite, ?_⟩
  apply MonoidHom.ext
  intro a
  set k := T.ord (a : K.Carrier)
  have hk : a * T.uniformizerUnit ^ (-k) ∈ C := by
    change T.ord ((a * T.uniformizerUnit ^ (-k) : K.Carrierˣ) : K.Carrier) = 0
    rw [Units.val_mul, T.ord_mul a.ne_zero (Units.ne_zero _)]
    simp only [Units.val_zpow_eq_zpow_val, PadicField.TopologicalData.uniformizerUnit_val,
      T.ord_zpow, T.ord_uniformizer, mul_one, k, add_neg_cancel]
  have hmem := U.pow_index_mem ⟨_, hk⟩
  have h2 : ω (a * T.uniformizerUnit ^ (-k)) ^ U.index = 1 := by
    have h := Subgroup.mem_subgroupOf.mp hmem
    rw [Subgroup.coe_pow, MonoidHom.mem_ker, map_pow] at h
    exact h
  rw [map_mul, map_zpow, h1, one_zpow, mul_one] at h2
  rw [MonoidHom.pow_apply, MonoidHom.one_apply]
  exact h2

/-- Twisting supercuspidal classes depends only on the character. -/
theorem supercuspidalClassTwist_congr {n : ℕ} {χ χ' : GeneralLinear n K.Carrier →* ℂˣ}
    (h : χ = χ') (hχ : IsOpen (χ.ker : Set (GeneralLinear n K.Carrier)))
    (hχ' : IsOpen (χ'.ker : Set (GeneralLinear n K.Carrier)))
    (hdet : (GeneralLinear.determinant : GeneralLinear n K.Carrier →* K.Carrierˣ).ker ≤ χ.ker)
    (hdet' : (GeneralLinear.determinant : GeneralLinear n K.Carrier →* K.Carrierˣ).ker ≤ χ'.ker)
    (a : GeneralLinear.SupercuspidalClass.{uV, uK} (F := K.Carrier) (n := n)) :
    GeneralLinear.SupercuspidalClass.twist χ hχ hdet a =
      GeneralLinear.SupercuspidalClass.twist χ' hχ' hdet' a := by
  subst h
  rfl

/-- Every supercuspidal class of `GL_n(K)` is the unramified twist of a unitary
class with central character of finite order. -/
theorem exists_unitaryFiniteOrderTwist (π : PadicSupercuspidal.Basis.{uK, uV} K) :
    ∃ (z : ℂˣ) (π₀ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K),
      HasFiniteOrderCentralCharacter K π₀ ∧
        PadicSupercuspidal.unramifiedTwistBasisEquiv K z π₀.val = π := by
  set T := K.canonicalTopologicalData
  rcases π with ⟨n, c⟩
  obtain ⟨A, rfl⟩ := Quotient.exists_rep c
  obtain ⟨t, hBu, -⟩ := supercuspidalRepRealUnitarization K T (n : ℕ) n.pos A
  let B := GeneralLinear.SupercuspidalRep.twist (T.determinantPowerCharacter n t)
    (T.isOpen_ker_determinantPowerCharacter n t)
    (T.ker_determinant_le_ker_determinantPowerCharacter n t) A
  have hB : Langlands.IsUnitarizable B.obj.representation := hBu
  -- The real power twist is the unramified twist by `z₁`.
  set z₁ : ℂˣ := Langlands.realPowerCharacter T.normalizedAbsUnits t T.uniformizerUnit
  have hBA : (⟨n, B.isoClass⟩ : PadicSupercuspidal.Basis.{uK, uV} K) =
      PadicSupercuspidal.unramifiedTwistBasisEquiv K z₁ ⟨n, Quotient.mk _ A⟩ := by
    refine congrArg (Sigma.mk n) ?_
    change GeneralLinear.SupercuspidalClass.twist _ _ _ (Quotient.mk _ A) =
      GeneralLinear.SupercuspidalClass.twist _ _ _ (Quotient.mk _ A)
    exact supercuspidalClassTwist_congr K (T.realPowerDeterminant_eq_unramifiedCharacter n t)
      _ _ _ _ _
  let π₁ : PadicSupercuspidal.UnitaryBasis.{uK, uV} K := ⟨⟨n, B.isoClass⟩, hB⟩
  -- The Schur central character of `B`.
  let := K.canonicalGeneralLinearTopologicalGroup (n : ℕ)
  obtain ⟨χc, ⟨hlc, hact⟩, -⟩ :=
    admissibleSchur_centralCharacter B.obj.representation B.property.2.1 B.property.1
  let ω₁ : K.Carrierˣ →* ℂˣ :=
    χc.comp (GeneralLinear.scalarToCenter (n := (n : ℕ)) (R := K.Carrier))
  have hω₁ : IsOpen (ω₁.ker : Set K.Carrierˣ) := by
    have hcont : Continuous (GeneralLinear.scalarToCenter (n := (n : ℕ)) (R := K.Carrier)) :=
      continuous_induced_rng.mpr
        (GeneralLinear.scalarContinuous (n := (n : ℕ)) (R := K.Carrier)).continuous
    have hset : (ω₁.ker : Set K.Carrierˣ) =
        GeneralLinear.scalarToCenter (n := (n : ℕ)) (R := K.Carrier) ⁻¹' (χc ⁻¹' {1}) := by
      ext a
      rfl
    rw [hset]
    exact (hlc.isOpen_fiber 1).preimage hcont
  have hact₁ (a : K.Carrierˣ) (v : B.obj) :
      B.obj.representation (GeneralLinear.scalar a) v = (ω₁ a : ℂ) • v :=
    hact (GeneralLinear.scalarToCenter a) v
  have hnorm : ∀ a, ‖(ω₁ a : ℂ)‖ = 1 := by
    obtain ⟨bB⟩ := hB
    let := B.property.1
    let : Nontrivial B.obj := IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (GeneralLinear (n : ℕ) K.Carrier)) B.obj.representation.asModule
    obtain ⟨v, hv⟩ := exists_ne (0 : B.obj)
    exact fun a => norm_eq_one_of_invariantPositiveForm bB hv (hact₁ a v)
  -- A modulus-one unramified twist killing the central value at the uniformizer.
  set u : ℂˣ := ω₁ T.uniformizerUnit
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((u⁻¹ : ℂˣ) : ℂ) n.pos
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [zero_pow n.ne_zero] at hx
    exact (Units.ne_zero _) hx.symm
  set w : ℂˣ := Units.mk0 x hx0
  have hw : ‖(w : ℂ)‖ = 1 := by
    have h := congrArg norm hx
    rw [norm_pow, Units.val_inv_eq_inv_val, norm_inv, hnorm, inv_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) n.ne_zero).mp h
  have hwu : w ^ (n : ℕ) * u = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0, hx, Units.val_one,
      Units.val_inv_eq_inv_val, inv_mul_cancel₀ (Units.ne_zero u)]
  obtain ⟨π₀, -, hπ₀⟩ := unitaryCharacterTwist_fieldUnramified K hw π₁
  obtain ⟨b₀, hb₀⟩ := π₀
  simp only at hπ₀
  subst hπ₀
  let ω₀ : K.Carrierˣ →* ℂˣ := T.unramifiedCharacter w ^ (n : ℕ) * ω₁
  have hω₀ : IsOpen (ω₀.ker : Set K.Carrierˣ) := by
    let := T.valuativeRel
    let := T.localField
    apply Subgroup.isOpen_mono (H₁ := (T.unramifiedCharacter w).ker ⊓ ω₁.ker)
    · intro a ha
      rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mem_ker] at ha
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.pow_apply, ha.1, ha.2, one_pow,
        one_mul]
    · rw [Subgroup.coe_inf]
      exact (T.isOpen_ker_unramifiedCharacter w).inter hω₁
  have hω₀1 : ω₀ T.uniformizerUnit = 1 := by
    rw [MonoidHom.mul_apply, MonoidHom.pow_apply, T.unramifiedCharacter_uniformizer]
    exact hwu
  refine ⟨(w * z₁)⁻¹, ⟨_, hb₀⟩, ⟨ω₀, fun a => ?_, isOfFinOrder_of_isOpen_ker_of_uniformizer K ω₀
    hω₀ hω₀1⟩, ?_⟩
  · have h₁ : SupercuspidalCentralActsBy K (n := n) B.isoClass a (ω₁ a) :=
      (supercuspidalCentralActsBy_iff K B a (ω₁ a)).mpr (hact₁ a)
    exact supercuspidalCentralActsBy_twist K h₁ (fieldUnramified K w)
  · change PadicSupercuspidal.unramifiedTwistBasisEquiv K (w * z₁)⁻¹
      (PadicSupercuspidal.unramifiedTwistBasisEquiv K w ⟨n, B.isoClass⟩) = _
    rw [hBA, ← PadicSupercuspidal.unramifiedTwistBasisEquiv_symm, Equiv.symm_apply_eq]
    exact congrArg (fun e : PadicSupercuspidal.Basis.{uK, uV} K ≃ _ => e ⟨n, Quotient.mk _ A⟩)
      (PadicSupercuspidal.unramifiedTwistBasisEquiv_mul K w z₁)

/-- Henniart (1993), §4.3, together with the unitarity of supercuspidal
representations with unitary central character, for the actual class spaces. -/
theorem supercuspidalUnitaryFiniteOrderTwist :
    SupercuspidalUnitaryFiniteOrderTwistStatement.{uK, uV} :=
  fun _ _ K π => exists_unitaryFiniteOrderTwist K π

end Langlands.Henniart.Extension
