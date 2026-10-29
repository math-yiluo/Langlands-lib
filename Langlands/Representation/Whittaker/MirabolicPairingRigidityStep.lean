import Langlands.Representation.Whittaker.MirabolicPairingRigidityElementary
import Langlands.Representation.Derivative.MirabolicMinusIrreducibleStatement
import Langlands.Representation.Derivative.MirabolicMinusPairingTransferStatement

/-!
# The induction step of mirabolic twisted pairing rigidity

The radical-generated case of `MirabolicTwistedPairingRigidityStatement` in rank
`m + 2` is reduced to rank `m + 1` through the unnormalized Bernstein–Zelevinsky
functor `Φ⁻` of the Library. The reduction uses two statements about `Φ⁻`
(`PhiMinusIrreducibleStatement` and `PhiMinusPairingTransferStatement`) and the
functional multiplicity statement in ranks `m + 1` and `m + 2`.
-/

noncomputable section

namespace Langlands.Whittaker.MirabolicRigidity

open GeneralLinear HarmonicAnalysis RankinSelberg

universe uF uV uW

/-! ### Elementary lemmas -/

section Elementary

variable {G : Type*} [Monoid G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Shifting the exponent by one multiplies the spectral point by `q`. -/
theorem spectralPoint_sub_one {q : ℕ} (hq : 0 < q) (s : ℂ) :
    spectralPoint q (s - 1) = (q : ℂ) * spectralPoint q s := by
  unfold spectralPoint
  have hq' : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  rw [neg_sub, sub_eq_add_neg, Complex.cpow_add _ _ hq', Complex.cpow_one]

theorem eq_zero_of_bot_eq_top {ρ : Representation ℂ G V}
    (h : (⊥ : Subrepresentation ρ) = ⊤) (v : V) : v = 0 := by
  have hv : v ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
  rw [← h] at hv
  exact (Submodule.mem_bot ℂ).mp hv

/-- A form vanishes when its left representation is zero. -/
theorem forms_eq_zero_of_bot_eq_top_left {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} {χ : G → ℂ}
    (h : (⊥ : Subrepresentation ρ) = ⊤) (β : InvariantBilinear.forms ρ σ χ) : β = 0 := by
  apply Subtype.ext
  ext v w
  simp [eq_zero_of_bot_eq_top h v]

/-- A form vanishes when its right representation is zero. -/
theorem forms_eq_zero_of_bot_eq_top_right {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} {χ : G → ℂ}
    (h : (⊥ : Subrepresentation σ) = ⊤) (β : InvariantBilinear.forms ρ σ χ) : β = 0 := by
  apply Subtype.ext
  ext v w
  simp [eq_zero_of_bot_eq_top h w]

/-- The dichotomy plus a nonzero carrier is irreducibility. -/
theorem isIrreducible_of_dichotomy {ρ : Representation ℂ G V}
    (h : ∀ σ : Subrepresentation ρ, σ = ⊥ ∨ σ = ⊤) (hne : (⊥ : Subrepresentation ρ) ≠ ⊤) :
    ρ.IsIrreducible :=
  { exists_pair_ne := ⟨⊥, ⊤, hne⟩
    eq_bot_or_eq_top := h }

/-- A module with a nonzero element of which every element is a multiple is a line. -/
theorem nonempty_linearEquiv_of_multiples {L : Type*} [AddCommGroup L] [Module ℂ L]
    {ℓ : L} (hℓ : ℓ ≠ 0) (h : ∀ ℓ' : L, ∃ c : ℂ, ℓ' = c • ℓ) : Nonempty (L ≃ₗ[ℂ] ℂ) := by
  have hspan : Submodule.span ℂ {ℓ} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨c, rfl⟩ := h x
    exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self ℓ)
  exact ⟨((LinearEquiv.toSpanNonzeroSingleton ℂ L ℓ hℓ).trans
    (LinearEquiv.ofTop _ hspan)).symm⟩

end Elementary

/-! ### Transfer of Whittaker functionals through `Φ⁻` -/

section Transfer

open GeneralLinear.Mirabolic

variable {F : Type uF} [CommRing F]

/-- An upper unipotent matrix of `mirabolic (m + 1) F` has mirabolic upper-left block. -/
theorem upperUnipotent_mem_plusSubgroup {m : ℕ} (n : Mirabolic.upperUnipotent (m + 1) F) :
    n.val ∈ plusSubgroup m F := by
  intro j
  have hn := n.property
  rw [mem_upperUnipotent] at hn
  change n.val.val.val (Fin.last m).castSucc j.castSucc = _
  by_cases hj : j = Fin.last m
  · subst j
    simpa using hn.2 (Fin.last m).castSucc
  · have hjlt : j.castSucc < (Fin.last m).castSucc :=
      Fin.castSucc_lt_castSucc_iff.mpr (lt_of_le_of_ne (Fin.le_last j) hj)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hj)]
    exact hn.1 hjlt

/-- The upper-left block of an upper unipotent matrix is upper unipotent. -/
theorem plusProjection_mem_upperUnipotent {m : ℕ} (n : Mirabolic.upperUnipotent (m + 1) F) :
    plusProjection (⟨n.val, upperUnipotent_mem_plusSubgroup n⟩ : plusSubgroup m F) ∈
      Mirabolic.upperUnipotent m F := by
  have hn := n.property
  rw [mem_upperUnipotent] at hn
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · exact hn.1 (Fin.castSucc_lt_castSucc_iff.mpr hij)
  · exact hn.2 i.castSucc

/-- The upper unipotent factor of the radical-successor decomposition. -/
def upperUnipotentBlock {m : ℕ} (n : Mirabolic.upperUnipotent (m + 1) F) : Mirabolic.upperUnipotent m F :=
  ⟨_, plusProjection_mem_upperUnipotent n⟩

theorem upperUnipotent_eq_radicalElement_mul_successor {m : ℕ}
    (n : Mirabolic.upperUnipotent (m + 1) F) :
    (n : mirabolic (m + 1) F) =
      (radicalElement (lastColumn n.val)).val * successor (upperUnipotentBlock n).val :=
  plus_eq_radicalElement_mul_successor ⟨n.val, upperUnipotent_mem_plusSubgroup n⟩

variable [TopologicalSpace F]

/-- The standard character factors through the radical-successor decomposition. -/
theorem mirabolicCharacter_succ (ψ : UnitaryAdditiveCharacter F) {m : ℕ}
    (n : Mirabolic.upperUnipotent (m + 1) F) :
    (mirabolicCharacter ψ (m + 1) n : ℂ) =
      (Derivative.Mirabolic.theta ψ m (radicalElement (lastColumn n.val)) : ℂ) *
        (mirabolicCharacter ψ m (upperUnipotentBlock n) : ℂ) := by
  rw [mirabolicCharacter_apply, mirabolicCharacter_apply, standardCharacter_apply,
    standardCharacter_apply, Derivative.Mirabolic.theta_radicalElement,
    Fin.sum_univ_castSucc, AddChar.map_add_eq_mul, mul_comm]
  congr 1

end Transfer

section PadicTransfer

open GeneralLinear.Mirabolic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A nonzero Whittaker functional on `Φ⁻ ξ` gives a nonzero Whittaker functional on `ξ`. -/
theorem exists_functional_ne_zero_of_phiMinus (T : F.TopologicalData) (m : ℕ) :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier)
      (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (hs : IsSmooth ξ)
      (ℓ : functionals (Mirabolic.upperUnipotent m F.Carrier) (mirabolicCharacter ψ m)
        ((Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)).representation),
      ℓ ≠ 0 →
        ∃ ℓ' : functionals (Mirabolic.upperUnipotent (m + 1) F.Carrier) (mirabolicCharacter ψ (m + 1)) ξ,
          ℓ' ≠ 0 := by
  let := T.topology
  intro ψ ξ hs ℓ hℓ
  let A := SmoothRep.of ξ hs
  let q := Derivative.Mirabolic.phiMinusQuotient T ψ m A
  refine ⟨⟨ℓ.val.comp q, ?_⟩, ?_⟩
  · intro n v
    change ℓ.val (q (ξ (n : mirabolic (m + 1) F.Carrier) v)) = _ * ℓ.val (q v)
    rw [upperUnipotent_eq_radicalElement_mul_successor n, map_mul, Module.End.mul_apply]
    have h1 := Derivative.Mirabolic.phiMinusQuotient_radical T ψ m A
      (radicalElement (lastColumn n.val)) (ξ (successor (upperUnipotentBlock n).val) v)
    have h2 : q (ξ (successor (upperUnipotentBlock n).val) v) =
        ((Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj A).representation
          (upperUnipotentBlock n).val (q v) := rfl
    change ℓ.val (q (ξ (radicalElement (lastColumn n.val)).val
      (ξ (successor (upperUnipotentBlock n).val) v))) = _
    rw [h1]
    refine (ℓ.val.map_smul _ _).trans ?_
    rw [smul_eq_mul]
    change _ * ℓ.val (q (ξ (successor (upperUnipotentBlock n).val) v)) = _
    rw [h2, ℓ.property (upperUnipotentBlock n) (q v), mirabolicCharacter_succ, mul_assoc]
    rfl
  · have hℓ' : ℓ.val ≠ 0 := fun h => hℓ (Subtype.ext h)
    intro h0
    apply hℓ'
    apply LinearMap.ext
    intro y
    obtain ⟨v, rfl⟩ := Derivative.Mirabolic.phiMinusQuotient_surjective T ψ m A y
    exact congrArg (fun f : functionals (Mirabolic.upperUnipotent (m + 1) F.Carrier)
      (mirabolicCharacter ψ (m + 1)) ξ => f.val v) h0

end PadicTransfer

/-! ### Recognition through `Φ⁻` -/

section Recognition

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- If `Φ⁻ ξ` is irreducible and equivalent to the compact model in rank `m + 1`,
then `ξ` is equivalent to the compact model in rank `m + 2`. -/
theorem nonempty_equiv_of_phiMinus (T : F.TopologicalData) (m : ℕ)
    (hM : MirabolicFunctionalMultiplicityStatement.{uF, uV} F T m)
    (hN : MirabolicFunctionalMultiplicityStatement.{uF, uV} F T (m + 1)) :
    letI := T.topology
    letI : IsTopologicalRing F.Carrier := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (hs : IsSmooth ξ),
      ξ.IsIrreducible →
      ((Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj
        (SmoothRep.of ξ hs)).representation.IsIrreducible →
      Nonempty (((Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj
        (SmoothRep.of ξ hs)).representation.Equiv (mirabolicCompactInduced ψ m)) →
      Nonempty (ξ.Equiv (mirabolicCompactInduced ψ (m + 1))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ ξ hs hirr hXi he
  let X := (Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)
  obtain ⟨eL⟩ := (hM ψ X X.representation X.isSmooth hXi).2.1.mpr he
  have hℓ : eL.symm 1 ≠ 0 := by
    intro h
    have := congrArg eL h
    simp at this
  obtain ⟨ℓ', hℓ'⟩ := exists_functional_ne_zero_of_phiMinus T m ψ ξ hs (eL.symm 1) hℓ
  have hN1 := hN ψ V ξ hs hirr
  exact hN1.2.1.mp (nonempty_linearEquiv_of_multiples hℓ' (fun ℓ'' => hN1.1 ℓ' ℓ'' hℓ'))

end Recognition

/-! ### The induction step -/

/-- The radical-generated case in rank `m + 2` follows from rigidity in rank
`m + 1`, the two `Φ⁻` statements and functional multiplicity in ranks `m + 1`
and `m + 2`. -/
theorem radicalGeneratedPairingRigidity_succ {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (m : ℕ)
    (hS : MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T m)
    (hI : Derivative.Mirabolic.PhiMinusIrreducibleStatement.{uF, uV} F T m)
    (hI' : Derivative.Mirabolic.PhiMinusIrreducibleStatement.{uF, uW} F T m)
    (hP : Derivative.Mirabolic.PhiMinusPairingTransferStatement.{uF, uV, uW} F T m)
    (hM : MirabolicFunctionalMultiplicityStatement.{uF, uV} F T m)
    (hM' : MirabolicFunctionalMultiplicityStatement.{uF, uW} F T m)
    (hN : MirabolicFunctionalMultiplicityStatement.{uF, uV} F T (m + 1))
    (hN' : MirabolicFunctionalMultiplicityStatement.{uF, uW} F T (m + 1)) :
    RadicalGeneratedPairingRigidity.{uF, uV, uW} F T (m + 1) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ W _ _ ξ ξ' hs hirr hs' hirr' hg _
  let X := (Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)
  let Y := (Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ' hs')
  have hq : 0 < T.residueCardinality :=
    lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  by_cases hX : (⊥ : Subrepresentation X.representation) = ⊤
  · refine ⟨∅, fun s _ β hβ => ?_⟩
    obtain ⟨β', hβ'⟩ := hP ψ V W ξ ξ' hs hs' hg s β hβ
    exact absurd (forms_eq_zero_of_bot_eq_top_left hX β') hβ'
  by_cases hY : (⊥ : Subrepresentation Y.representation) = ⊤
  · refine ⟨∅, fun s _ β hβ => ?_⟩
    obtain ⟨β', hβ'⟩ := hP ψ V W ξ ξ' hs hs' hg s β hβ
    exact absurd (forms_eq_zero_of_bot_eq_top_right hY β') hβ'
  have hXi : X.representation.IsIrreducible :=
    isIrreducible_of_dichotomy (hI ψ V ξ hs hirr) hX
  have hYi : Y.representation.IsIrreducible :=
    isIrreducible_of_dichotomy (hI' ψ W ξ' hs' hirr') hY
  obtain ⟨E, hE⟩ := hS ψ X Y X.representation Y.representation X.isSmooth hXi Y.isSmooth hYi
  refine ⟨E.image (fun z => z / (T.residueCardinality : ℂ)), fun s hsE β hβ => ?_⟩
  have hsE' : spectralPoint T.residueCardinality (s - 1) ∉ E := by
    intro h
    apply hsE
    refine Finset.mem_image.mpr ⟨_, h, ?_⟩
    have hq' : (T.residueCardinality : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
    rw [spectralPoint_sub_one hq, mul_div_cancel_left₀ _ hq']
  obtain ⟨β', hβ'⟩ := hP ψ V W ξ ξ' hs hs' hg s β hβ
  obtain ⟨eX, eY⟩ := hE (s - 1) hsE' β' hβ'
  exact ⟨nonempty_equiv_of_phiMinus T m hM hN ψ V ξ hs hirr hXi eX,
    nonempty_equiv_of_phiMinus T m hM' hN' ψ W ξ' hs' hirr' hYi eY⟩

/-- Rigidity in every rank follows from the two `Φ⁻` statements and functional
multiplicity in every rank. -/
theorem mirabolicTwistedPairingRigidity_of_phiMinus {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData)
    (hI : ∀ m, Derivative.Mirabolic.PhiMinusIrreducibleStatement.{uF, uV} F T m)
    (hI' : ∀ m, Derivative.Mirabolic.PhiMinusIrreducibleStatement.{uF, uW} F T m)
    (hP : ∀ m, Derivative.Mirabolic.PhiMinusPairingTransferStatement.{uF, uV, uW} F T m)
    (hM : ∀ n, MirabolicFunctionalMultiplicityStatement.{uF, uV} F T n)
    (hM' : ∀ n, MirabolicFunctionalMultiplicityStatement.{uF, uW} F T n) (n : ℕ) :
    MirabolicTwistedPairingRigidityStatement.{uF, uV, uW} F T n := by
  induction n with
  | zero =>
    apply mirabolicTwistedPairingRigidity_of_radicalGenerated
    let := T.topology
    let := T.valuativeRel
    let := T.localField
    intro ψ V _ _ W _ _ ξ ξ' _ hirr _ hirr' _ _
    exact ⟨∅, fun _ _ _ _ => ⟨rankOne_equiv ψ ξ hirr, rankOne_equiv ψ ξ' hirr'⟩⟩
  | succ m ih =>
    exact mirabolicTwistedPairingRigidity_of_radicalGenerated F T (m + 1)
      (radicalGeneratedPairingRigidity_succ F T m ih (hI m) (hI' m) (hP m) (hM m) (hM' m)
        (hM (m + 1)) (hM' (m + 1)))

end Langlands.Whittaker.MirabolicRigidity
