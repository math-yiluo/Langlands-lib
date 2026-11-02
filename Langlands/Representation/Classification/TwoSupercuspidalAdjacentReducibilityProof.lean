import Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityStatement
import Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapProof
import Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof
import Langlands.Representation.Classification.ExponentFamily
import Langlands.Representation.Classification.TwistedProductCharacterTwistProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.SupercuspidalContragredientAux
import Langlands.Representation.Unitary.UnitarizabilityContinuationProof
import Langlands.Representation.Induction.CompactScalarProof
import Langlands.Representation.Tensor.UnitaryProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Smooth.Admissibility.EquivalenceProof
import Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof
import Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof

/-!
# Reducibility of adjacent two-supercuspidal products

Zelevinsky 1980, Proposition 1.11(b), reducibility step, from the published
analytic inputs: unitarizability continuation, non-unitarizability for large
exponents, the irreducible product swap, nonadjacent irreducibility and real
unitarization of supercuspidals.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory MeasureTheory

namespace Langlands.Classification

open GeneralLinear PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

section Twists

variable {r : ℕ}

/-- Successive determinant-power twists compose additively. -/
private def segmentFactorSegmentFactorIso
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (a b c : ℝ) (h : b + a = c) :
    letI := T.topology
    T.segmentFactor (T.segmentFactor A a) b ≅ T.segmentFactor A c := by
  letI := T.topology
  refine SmoothRep.mkIso (equivOfRepresentationEq ?_)
  change twist (realPowerCharacter (T.determinantNorm r) b)
      (twist (realPowerCharacter (T.determinantNorm r) a) A.representation) =
    twist (realPowerCharacter (T.determinantNorm r) c) A.representation
  rw [twist_twist, ← realPowerCharacter_add, h]

/-- The twist by `ν ^ 0` is the identity. -/
private def segmentFactorZeroIso
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) :
    letI := T.topology
    T.segmentFactor A 0 ≅ A := by
  letI := T.topology
  refine SmoothRep.mkIso (equivOfRepresentationEq ?_)
  change twist (realPowerCharacter (T.determinantNorm r) 0) A.representation = A.representation
  rw [realPowerCharacter_zero, twist_one]

/-- Three successive determinant-power twists compose additively. -/
private def segmentFactorTripleIso
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (a b c d : ℝ) (h : c + b + a = d) :
    letI := T.topology
    T.segmentFactor (T.segmentFactor (T.segmentFactor A a) b) c ≅ T.segmentFactor A d := by
  letI := T.topology
  refine SmoothRep.mkIso (equivOfRepresentationEq ?_)
  change twist (realPowerCharacter (T.determinantNorm r) c)
      (twist (realPowerCharacter (T.determinantNorm r) b)
        (twist (realPowerCharacter (T.determinantNorm r) a) A.representation)) =
    twist (realPowerCharacter (T.determinantNorm r) d) A.representation
  rw [twist_twist, twist_twist, ← realPowerCharacter_add, ← realPowerCharacter_add, h]

/-- Isomorphic real determinant twists of an irreducible admissible
representation of positive rank have equal exponents. -/
private theorem exponent_eq_of_iso (hr : 0 < r)
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier))
    (hAa : letI := T.topology; A.IsAdmissible)
    (hAi : letI := T.topology; A.IsIrreducible) (a b : ℝ)
    (e : letI := T.topology; T.segmentFactor A a ≅ T.segmentFactor A b) : a = b := by
  letI := T.topology
  have e' : A ≅ T.segmentFactor A (b - a) :=
    (segmentFactorZeroIso F T A).symm ≪≫
      (segmentFactorSegmentFactorIso F T A a (-a) 0 (by ring)).symm ≪≫
      SmoothRep.twistIso _ (T.isOpen_ker_determinantPowerCharacter r (-a)) e ≪≫
      segmentFactorSegmentFactorIso F T A b (-a) (b - a) (by ring)
  have := IntegralTwistFreeness.exponent_eq_zero_of_equiv T r hr A hAa hAi (b - a)
    (SmoothRep.equivOfIso e')
  linarith

end Twists

private theorem nontrivial_of_isIrreducible {G : Type*} [Group G]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (hρ : ρ.IsIrreducible) : Nontrivial V := by
  have := hρ
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have : Subsingleton (Submodule ℂ V) := (Submodule.subsingleton_iff ℂ).mpr hV
  exact (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
    (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

section TwoBlocks

variable {k : ℕ} (hk : 0 < k)

/-- The product functor on two isomorphisms of factors. -/
private def twoBlockProductIso
    {α α' β β' : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)}
    (e₀ : α ≅ α') (e₁ : β ≅ β') :
    letI := T.topology
    (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
        (twoBlockFactors hk hk α β) ≅
      (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
        (twoBlockFactors hk hk α' β') := by
  letI := T.topology
  refine (T.normalizedProductInductionFunctor _).mapIso (Pi.isoMk fun i => ?_)
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
  · exact e₀
  · exact e₁

/-- The twisted product of two equal blocks is the product of the twisted blocks. -/
private theorem twistedProductInduced_twoBlocks
    (A : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)) (a b : ℝ) :
    letI := T.topology
    T.twistedProductInduced (Shahidi.twoBlocks k k hk hk) (twoBlockFactors hk hk A A) ![a, b] =
      (T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
        (twoBlockFactors hk hk (T.segmentFactor A a) (T.segmentFactor A b)) := by
  letI := T.topology
  unfold twistedProductInduced
  congr 1
  funext i
  refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> rfl

end TwoBlocks

/-- The twist `ν ^ s ρ` of an actual supercuspidal representation. -/
private abbrev scTwist {k : ℕ} (s : ℝ)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) :
    letI := T.topology
    SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k) :=
  letI := T.topology
  SupercuspidalRep.twist (T.determinantPowerCharacter k s)
    (T.isOpen_ker_determinantPowerCharacter k s)
    (T.ker_determinant_le_ker_determinantPowerCharacter k s) ρ

/-- If `ν^a ρ ≅ ν (ν^b ρ)` for a supercuspidal `ρ` of positive rank, then
`a = 1 + b`. -/
private theorem exponent_eq_of_class_eq {k : ℕ} (hk : 0 < k)
    (ρ : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k)) (a b : ℝ)
    (h : letI := T.topology
      (⟨k, (scTwist F T a ρ).isoClass⟩ :
          Σ d : ℕ, SupercuspidalClass.{uV, uF} (F := F.Carrier) (n := d)) =
        ⟨k, T.supercuspidalClassRealPowerTwist k 1 (scTwist F T b ρ).isoClass⟩) :
    a = 1 + b := by
  letI := T.topology
  have h' := (Sigma.mk.inj_iff.mp h).2
  rw [heq_iff_eq] at h'
  obtain ⟨e⟩ := (SupercuspidalRep.isoClass_eq_iff (scTwist F T a ρ)
    (scTwist F T 1 (scTwist F T b ρ))).mp h'
  have e' : T.segmentFactor ρ.obj a ≅ T.segmentFactor ρ.obj (1 + b) :=
    (ObjectProperty.ι _).mapIso e ≪≫ segmentFactorSegmentFactorIso F T ρ.obj b 1 (1 + b) rfl
  exact exponent_eq_of_iso F T hk ρ.obj ρ.property.2.1 ρ.property.1 a (1 + b) e'

section Members

variable {k : ℕ} (hk : 0 < k)

/-- For `s ≤ 0` with `s ≠ -1/2`, the member `ν^s ρ₀ × ν^(-s) ρ₀` is irreducible. -/
private theorem member_isIrreducible
    (ρ0 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (s : ℝ) (hs : s ≤ 0) (hs2 : s ≠ -(1 / 2)) :
    letI := T.topology
    (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
      (twoBlockFactors hk hk ρ0.obj ρ0.obj) ![s, -s]).IsIrreducible := by
  letI := T.topology
  rw [twistedProductInduced_twoBlocks F T hk]
  refine twoSupercuspidalNonadjacentProductIrreducible.{uF, uV} F T k k hk hk
    (scTwist F T s ρ0) (scTwist F T (-s) ρ0) ?_ ?_
  · intro h
    have := exponent_eq_of_class_eq F T hk ρ0 (-s) s h
    exact hs2 (by linarith)
  · intro h
    have := exponent_eq_of_class_eq F T hk ρ0 s (-s) h
    linarith

/-- An irreducible member is isomorphic to the member at the opposite parameter. -/
private theorem member_swap
    (A0 : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (hA0 : letI := T.topology; A0.IsIrreducible) (s : ℝ)
    (h : letI := T.topology
      (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
        (twoBlockFactors hk hk A0 A0) ![s, -s]).IsIrreducible) :
    letI := T.topology
    Nonempty (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
        (twoBlockFactors hk hk A0 A0) ![s, -s] ≅
      T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
        (twoBlockFactors hk hk A0 A0) ![-s, -(-s)]) := by
  letI := T.topology
  have hfac (a : ℝ) : (T.segmentFactor A0 a).IsIrreducible :=
    (SmoothRep.isIrreducible_twist_iff _ _ A0).mpr hA0
  rw [twistedProductInduced_twoBlocks F T hk] at h
  rw [twistedProductInduced_twoBlocks F T hk, twistedProductInduced_twoBlocks F T hk, neg_neg]
  exact irreducibleTwoFactorProductSwap F T k hk _ _ (hfac s) (hfac (-s)) h

/-- Every member is admissible. -/
private theorem member_isAdmissible
    (A0 : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier))
    (hA0 : letI := T.topology; IsAdmissible A0.representation) (s : ℝ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + k)
    IsAdmissible (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
      (twoBlockFactors hk hk A0 A0) ![s, -s]).representation := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + k)
  have hf : ∀ i, IsAdmissible (T.twistedBlocks (Shahidi.twoBlocks k k hk hk)
      (twoBlockFactors hk hk A0 A0) ![s, -s] i).representation := by
    intro i
    refine (isAdmissible_twist_iff _ _ (T.isOpen_ker_determinantPowerCharacter _ _)).mpr ?_
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
    · exact hA0
    · exact hA0
  exact Parabolic.normalizedInductionAdmissibility F T _ _ _
    (FiniteTensor.isAdmissible_external _ hf)

/-- The exponent family at `s` is the member at `s`. -/
private theorem member_equiv
    (A0 : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (k + k)
    ∀ (K : OpenSubgroup (GeneralLinear (k + k) F.Carrier))
      (hK : IsCompact (K : Set (GeneralLinear (k + k) F.Carrier)))
      (hPK : ∀ g : GeneralLinear (k + k) F.Carrier,
        ∃ (q : (Shahidi.twoBlocks k k hk hk).parabolic F.Carrier) (x : K),
          g = (q : GeneralLinear (k + k) F.Carrier) * (x : GeneralLinear (k + k) F.Carrier))
      (s : ℝ),
      Nonempty (((T.exponentHeight (Shahidi.twoBlocks k k hk hk) ![1, -1] K hK hPK).family
          (twist (T.parabolicHalfModulus (Shahidi.twoBlocks k k hk hk))
            (((Shahidi.twoBlocks k k hk hk).blockTensor
              (fun i => (twoBlockFactors hk hk A0 A0 i).representation)).comp
              ((Shahidi.twoBlocks k k hk hk).leviProjection F.Carrier))) s).Equiv
        (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
          (twoBlockFactors hk hk A0 A0) ![s, -s]).representation) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (k + k)
  intro K hK hPK s
  have hu : (fun i => s * (![1, -1] : Fin 2 → ℝ) i) = ![s, -s] := by
    funext i
    fin_cases i <;> simp
  rw [← hu]
  exact ⟨T.exponentFamilyEquiv (Shahidi.twoBlocks k k hk hk) (twoBlockFactors hk hk A0 A0)
    ![1, -1] K hK hPK s⟩

end Members

/-- Case `ρ' ≅ νρ`, analytic core: for an actual unitarizable supercuspidal
`ρ₀`, the product `ν^(-1/2) ρ₀ × ν^(1/2) ρ₀` is reducible. -/
theorem unitaryHalfProduct_not_isIrreducible
    (k : ℕ) (hk : 0 < k)
    (ρ0 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (hρ0 : letI := T.topology; IsUnitarizable ρ0.obj.representation) :
    letI := T.topology
    ¬ (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
        (twoBlockFactors hk hk ρ0.obj ρ0.obj) ![-(1 / 2 : ℝ), -(-(1 / 2 : ℝ))]).IsIrreducible := by
  letI := T.topology
  intro hhalf
  let B := Shahidi.twoBlocks k k hk hk
  let A := twoBlockFactors hk hk ρ0.obj ρ0.obj
  let P : ℝ → SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (k + k) F.Carrier) :=
    fun s => T.twistedProductInduced B A ![s, -s]
  -- Irreducibility on `J = (-∞, 0]`.
  have hirr : ∀ s ∈ Set.Iic (0 : ℝ), (P s).IsIrreducible := by
    intro s hs
    by_cases hs2 : s = -(1 / 2)
    · subst hs2
      exact hhalf
    · exact member_isIrreducible F T hk ρ0 s hs hs2
  -- The common compact picture.
  obtain ⟨K, hK, hPK, hμ⟩ := glParabolicCompactScalarIntegral p F T (k + k) (by omega) B
  letI := T.generalLinearTopologicalGroup (k + k)
  letI : MeasurableSpace K := borel K
  obtain ⟨μ, hHaar, _hprob, hscalar⟩ := hμ
  have := hHaar
  have hAu : ∀ i, IsUnitarizable (A i).representation := by
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i
    · exact hρ0
    · exact hρ0
  obtain ⟨bT, -⟩ := FiniteTensor.invariantPositiveForm.{0, uF, uV}
    (Fin B.length) (fun i => GeneralLinear (B.size i) F.Carrier)
    (fun i => (A i : Type uV)) (fun i => (A i).representation)
    (fun i => Classical.choice (hAu i))
  let σL := B.blockTensor (fun i => (A i).representation)
  let H := T.exponentHeight B ![1, -1] K hK hPK
  let σ := twist (T.parabolicHalfModulus B) (σL.comp (B.leviProjection F.Carrier))
  let π : ℝ → Representation ℂ (GeneralLinear (k + k) F.Carrier)
      (Induction.SmoothFunctions (B.parabolic F.Carrier) σ) := fun s => H.family σ s
  have E : ∀ s, Nonempty ((π s).Equiv (P s).representation) :=
    member_equiv F T hk ρ0.obj K hK hPK
  -- The compact pairing between the members at `s` and `-s`.
  let c := (T.normalizedIntegralForm B σL bT K.toSubgroup μ hPK hscalar).toInnerProductCore
  have hc : ∀ (s : ℝ) (g : GeneralLinear (k + k) F.Carrier)
      (v w : Induction.SmoothFunctions (B.parabolic F.Carrier) σ),
      c.inner (π s g v) (π (-s) g w) = c.inner v w := fun s g v w =>
    T.normalizedIntegralForm_family_neg B σL bT K.toSubgroup μ hPK hscalar H s g v w
  have hforms : ∀ s ∈ Set.Iic (0 : ℝ),
      ∃ b : Induction.SmoothFunctions (B.parabolic F.Carrier) σ →ₗ⋆[ℂ]
          Induction.SmoothFunctions (B.parabolic F.Carrier) σ →ₗ[ℂ] ℂ, b ≠ 0 ∧
        ∀ (g : GeneralLinear (k + k) F.Carrier) (v w : _),
          b (π s g v) (π s g w) = b v w := by
    intro s hs
    let e : (π s).Equiv (π (-s)) :=
      (E s).some.trans ((SmoothRep.equivOfIso
        (member_swap F T hk ρ0.obj ρ0.property.1 s (hirr s hs)).some).trans
          (E (-s)).some.symm)
    have : Nontrivial (Induction.SmoothFunctions (B.parabolic F.Carrier) σ) :=
      nontrivial_of_isIrreducible ((isIrreducible_iff_of_equiv (E s).some).mpr (hirr s hs))
    exact ⟨pairingSesquilinear c e.toLinearMap,
      pairingSesquilinear_ne_zero c e.toLinearEquiv,
      pairingSesquilinear_invariant c (hc s) e⟩
  have hres := unitarizabilityContinuation.{uF, max uF uV} (GeneralLinear (k + k) F.Carrier)
    (Induction.SmoothFunctions (B.parabolic F.Carrier) σ) π (Set.Iic 0) K hK
    isPreconnected_Iic
    (fun s _ t _ g hg => H.family_apply_eq_of_mem σ s t hg)
    (fun s _ => isAdmissible_of_equiv (E s).some.symm
      (member_isAdmissible F T hk ρ0.obj ρ0.property.2.1 s))
    (fun s hs => (isIrreducible_iff_of_equiv (E s).some).mpr (hirr s hs))
    hforms
    (fun g v ℓ => (H.continuous_family_apply σ g v ℓ).continuousOn)
    0 (Set.mem_Iic.mpr le_rfl)
    ⟨T.familyZeroForm B σL bT K.toSubgroup μ hPK hscalar H⟩
    (-(k : ℝ) / 2 - 1) (by
      change -(k : ℝ) / 2 - 1 ≤ 0
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith)
  exact twoBlockLargeExponentNonUnitarizable F T k hk ρ0.obj ρ0.property.1 hρ0 (-(k : ℝ) / 2 - 1) (by linarith)
    ((isUnitarizable_iff_of_equiv (E _).some).mp hres)

/-- Case `ρ' ≅ νρ`: the product `ρ × ρ'` is reducible. -/
theorem adjacentProduct_not_isIrreducible
    (k : ℕ) (hk : 0 < k)
    (ρ ρ' : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := k))
    (h : letI := T.topology
      ρ'.isoClass = T.supercuspidalClassRealPowerTwist k 1 ρ.isoClass) :
    letI := T.topology
    ¬ ((T.normalizedProductInductionFunctor (Shahidi.twoBlocks k k hk hk)).obj
      (twoBlockFactors hk hk ρ.obj ρ'.obj)).IsIrreducible := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  intro hX
  obtain ⟨t, ht⟩ := supercuspidalRealUnitarization p F T k hk ρ.obj ρ.obj.representation
    ρ.property.1 ρ.property.2
  let ρ0 := scTwist F T t ρ
  refine unitaryHalfProduct_not_isIrreducible F T k hk ρ0 ht ?_
  let χ : Induction.SmoothCharacter ℂ F.Carrierˣ :=
    ⟨realPowerCharacter T.normalizedAbsUnits (1 / 2 - t),
      isOpen_ker_realPowerCharacter _ T.isOpen_ker_normalizedAbsUnits _⟩
  let C := T.segmentFactor ρ0.obj (1 / 2 - t)
  -- `ρ × ρ'` is the product of the two blocks `ν^(∓1/2) C`.
  have e₀ : ρ.obj ≅ T.segmentFactor C (-(1 / 2)) :=
    (segmentFactorTripleIso F T ρ.obj t (1 / 2 - t) (-(1 / 2)) 0 (by ring) ≪≫
      segmentFactorZeroIso F T ρ.obj).symm
  obtain ⟨e'⟩ := (SupercuspidalRep.isoClass_eq_iff ρ' (scTwist F T 1 ρ)).mp h
  have e₁ : ρ'.obj ≅ T.segmentFactor C (-(-(1 / 2))) :=
    (ObjectProperty.ι _).mapIso e' ≪≫
      (segmentFactorTripleIso F T ρ.obj t (1 / 2 - t) (-(-(1 / 2))) 1 (by ring)).symm
  have hY : (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
      (twoBlockFactors hk hk C C) ![-(1 / 2 : ℝ), -(-(1 / 2 : ℝ))]).IsIrreducible := by
    rw [twistedProductInduced_twoBlocks F T hk]
    exact (isIrreducible_iff_of_equiv
      (SmoothRep.equivOfIso (twoBlockProductIso F T hk e₀ e₁))).mp hX
  -- The blocks `ν^(∓1/2) C` are the twists of the blocks `ν^(∓1/2) ρ₀` by `χ ∘ det`.
  have hfam : (fun i => (twoBlockFactors hk hk ρ0.obj ρ0.obj i).twist
      (χ.toMonoidHom.comp determinant)
      (χ.isOpen_ker.preimage (T.generalLinearDeterminant
        ((Shahidi.twoBlocks k k hk hk).size i)).continuous)) =
      twoBlockFactors hk hk C C := by
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun j => j.elim0)) i <;> rfl
  have hE : Nonempty ((twist (χ.toMonoidHom.comp determinant)
      (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
        (twoBlockFactors hk hk ρ0.obj ρ0.obj)
        ![-(1 / 2 : ℝ), -(-(1 / 2 : ℝ))]).representation).Equiv
      (T.twistedProductInduced (Shahidi.twoBlocks k k hk hk)
        (twoBlockFactors hk hk C C) ![-(1 / 2 : ℝ), -(-(1 / 2 : ℝ))]).representation) := by
    rw [← hfam]
    exact twistedProductCharacterTwist.{uF, uV} F T (k + k) (by omega)
      (Shahidi.twoBlocks k k hk hk) χ (twoBlockFactors hk hk ρ0.obj ρ0.obj)
      ![-(1 / 2 : ℝ), -(-(1 / 2 : ℝ))]
  exact (Langlands.isIrreducible_twist_iff _ _).mp
    ((isIrreducible_iff_of_equiv hE.some).mpr hY)

/-- Ze80 Proposition 1.11(b), reducibility: if `ρ' ≅ νρ` or `ρ ≅ νρ'`, then the
product `ρ × ρ'` of two supercuspidal representations is reducible. -/
theorem twoSupercuspidalAdjacentProductReducible :
    TwoSupercuspidalAdjacentProductReducible.{uF, uV} F T := by
  letI := T.topology
  intro k hk ρ ρ' h
  rcases h with h | h
  · exact adjacentProduct_not_isIrreducible F T k hk ρ ρ' h
  · intro hX
    obtain ⟨e⟩ := irreducibleTwoFactorProductSwap F T k hk ρ.obj ρ'.obj ρ.property.1 ρ'.property.1 hX
    exact adjacentProduct_not_isIrreducible F T k hk ρ' ρ h
      ((isIrreducible_iff_of_equiv (SmoothRep.equivOfIso e)).mp hX)

end Langlands.Classification
