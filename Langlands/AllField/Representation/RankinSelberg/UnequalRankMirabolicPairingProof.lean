import Langlands.Representation.RankinSelberg.UnequalRankMirabolicPairingProof
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicMixedTransfer
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicPairingStatement
import Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicTowerClaim
/-!
# Proof of irreducible unequal-rank mirabolic pairing rigidity

This module proves `UnequalRankMirabolicPairingRigidityStatement` (JPSS 1983,
Section 2.11, Lemma on printed p.399). The proof is by induction on the rank `r > n`.
The step applies the unnormalized `Φ⁻` to the mirabolic representation, which
shifts the parameter by `1/2`. In the adjacent case `r = n + 1` there are two
cases. A radical-trivial representation admits a nonzero form only at finitely
many spectral values, by the Schur scalars of the center. A radical-generated
representation is reduced by the mixed transfer to a form between `Φ⁻ ξ` and
`η|_(P_n)`. The tower claim `C(n)` then handles that form.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankFunctionalEquationStatement UnequalRankMirabolicPairingRigidityStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankMirabolicPairingRigidity
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.HarmonicAnalysis hiding PadicRectangularHaarScalingStatement padicRectangularHaarScaling padicRectangularHaarScalingStatement padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement MirabolicFunctionalMultiplicityStatement mirabolicCompactMinimality mirabolicFunctionalMultiplicity mirabolicFunctionalMultiplicity_canonical mirabolicFunctionalMultiplicity_of_minimality
open Langlands.AllField.Whittaker
open Langlands.Whittaker.MirabolicRigidity hiding exists_functional_ne_zero_of_phiMinus nonempty_equiv_of_phiMinus
open Langlands.AllField.Whittaker.MirabolicRigidity

universe uF uV uW

namespace UnequalRankRigidity
open Langlands.RankinSelberg.UnequalRankRigidity hiding exists_descent_ne_zero rigidity_adjacent rigidity_of_lt
open Langlands.AllField.RankinSelberg.UnequalRankRigidity
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankFunctionalEquationStatement UnequalRankMirabolicPairingRigidityStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankMirabolicPairingRigidity
open Langlands.AllField.RankinSelberg

section Algebra

variable {F : Type uF} [Field F]

end Algebra

section Spectral

end Spectral

section Character

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  (ψ : UnitaryAdditiveCharacter F) {n : ℕ} {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

end Character

section Descent

variable {F : Type uF} [Field F]

/-- First-variable descent: a nonzero covariant form of rank `m + 1` at `s`
descends through the `θ_ψ`-coinvariants of the radical to a nonzero covariant form
of rank `m` at `s - 1/2` on the unnormalized `Φ⁻ ξ`. -/
theorem exists_descent_ne_zero (T : LocalFieldData F) {n m : ℕ} (hnm : n < m) :
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
      {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]
      (ξ : Representation ℂ (mirabolic (m + 1) F) V) (hs : IsSmooth ξ)
      (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W) (s : ℂ)
      (B : unequalRankMirabolicForms (Nat.lt_add_one_of_lt hnm) ψ abv ξ η s), B ≠ 0 →
      ∃ B' : unequalRankMirabolicForms hnm ψ abv
          ((Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj
            (SmoothRep.of ξ hs)).representation η (s - 1 / 2),
        B' ≠ 0 := by
  let := T.topology
  intro ψ abv V _ _ W _ _ ξ hs η s B hB
  let A := SmoothRep.of ξ hs
  let Θ := T.mirabolicTheta ψ m
  have hrad : ∀ (u : Mirabolic.radical (m + 1) F) (v : V),
      B.val (ξ (u : mirabolic (m + 1) F) v) = (Θ u : ℂ) • B.val v := by
    intro u v
    obtain ⟨d, rfl⟩ : ∃ d, Mirabolic.radicalElement d = u :=
      ⟨_, Mirabolic.radicalElement_coordinates u⟩
    ext w
    have e := B.property.2 (Mirabolic.radicalToUpperUnipotent (Mirabolic.radicalElement d))
      (UnequalRankCompactPairing.isCovarianceUnipotent_radical hnm d) v w
    rw [UnequalRankCompactPairing.standardCharacter_radicalElement] at e
    rw [LinearMap.smul_apply, smul_eq_mul,
      show (Θ (Mirabolic.radicalElement d) : ℂ) = ψ.complex (d (Fin.last m)) from
        Derivative.Mirabolic.theta_radicalElement ψ m d]
    exact e
  let L := Jacquet.Localization.lift ξ (Mirabolic.radical (m + 1) F) Θ B.val hrad
  have hL : ∀ v w, L (Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient T ψ m A v) w = B.val v w :=
    fun _ _ => rfl
  refine ⟨⟨L, ⟨fun g a w => ?_, fun u hu a w => ?_⟩⟩, ?_⟩
  · obtain ⟨v, rfl⟩ := Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient_surjective T ψ m A a
    change B.val (ξ (Mirabolic.successor (unequalRankEmbedding hnm g)) v) (η g w) =
      determinantWeight abv g (((m - n : ℕ) : ℂ) / 2 - (s - 1 / 2)) * B.val v w
    rw [← UnequalRankCompactPairing.unequalRankEmbedding_succ hnm,
      ← UnequalRankCompactPairing.weight_succ hnm]
    exact B.property.1 g v w
  · obtain ⟨v, rfl⟩ := Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient_surjective T ψ m A a
    change B.val (ξ (Mirabolic.successor (unequalRankUnipotentLift u)) v) w =
      (standardCharacter ψ m u : ℂ) * B.val v w
    rw [← UnequalRankCompactPairing.unequalRankUnipotentLift_successorUnipotent,
      ← UnequalRankCompactPairing.standardCharacter_successor ψ u]
    exact B.property.2 _ (UnequalRankCompactPairing.isCovarianceUnipotent_successor hnm hu) v w
  · intro h0
    apply hB
    apply Subtype.ext
    ext v w
    have h1 := LinearMap.congr_fun₂ (congrArg Subtype.val h0)
      (Langlands.AllField.Derivative.Mirabolic.phiMinusQuotient T ψ m A v) w
    exact h1

end Descent

/-- The adjacent case `r = n + 1`, with a standard Whittaker functional. -/
theorem rigidity_adjacent (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI : IsTopologicalRing F := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ (hnr : n < n + 1) (ψ : UnitaryAdditiveCharacter F)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ξ : Representation ℂ (mirabolic (n + 1) F) V)
      (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsSmooth ξ → ξ.IsIrreducible → IsAdmissible η → η.IsIrreducible →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        ∀ B : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) ξ η s, B ≠ 0 →
          Nonempty (ξ.Equiv (mirabolicCompactInduced ψ (n + 1))) ∧
          HasFunctional (N := upperUnipotent (n + 1) F)
            (θ := standardCharacter ψ n) η := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hq : 0 < T.residueCardinality :=
    lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  intro hnr ψ V _ _ W _ _ ξ η hs hirr hadm hirrη
  have hw : ∀ s : ℂ, (((n + 1 - n : ℕ) : ℂ) / 2 - s) = -(s - 1 / 2) := by
    intro s
    rw [Nat.add_sub_cancel_left]
    push_cast
    ring
  -- The Levi law of an adjacent form.
  have hlevi : ∀ (s : ℂ)
      (B : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) ξ η s)
      (g : Langlands.GeneralLinear (n + 1) F) (v : V) (w : W),
      B.val (ξ (Mirabolic.levi g) v) (η g w) =
        determinantWeight (normalizedAbsoluteValue T) g (-(s - 1 / 2)) * B.val v w := by
    intro s B g v w
    have h := B.property.1 g v w
    rw [unequalRankEmbedding_adjacent, hw] at h
    exact h
  have hne : ∀ (s : ℂ) (B : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) ξ η s),
      B ≠ 0 → B.val ≠ 0 := fun s B hB h => hB (Subtype.ext h)
  rcases radicalTrivial_or_radicalGenerated ξ hirr with ht | hg
  · -- `ξ` is radical-trivial: the Schur scalars of the center fix `q^(-s)` up to
    -- finitely many values.
    have : SecondCountableTopology
        (Langlands.GeneralLinear (n + 1 + 1) F) :=
      T.generalLinearSecondCountableTopology (n + 1 + 1)
    have : SecondCountableTopology (mirabolic (n + 1) F) :=
      Topology.IsEmbedding.subtypeVal.secondCountableTopology
    let ϖ := Langlands.LocalFactor.LocalAbelian.uniformizerUnit T
    have hϖ : normalizedAbsoluteValue T (ϖ : F) =
        (T.residueCardinality : ℝ) ^ (-1 : ℤ) := by
      rw [normalizedAbsoluteValue_apply, Langlands.LocalFactor.LocalAbelian.uniformizerUnit_coe]
      exact T.normalizedAbs_uniformizer
    let z : mirabolic (n + 1) F := leviScalar ϖ
    obtain ⟨c, hc⟩ := exists_scalar_of_commute ξ (rank_le_aleph0 ξ hs hirr) hirr z
      (apply_mul_leviScalar ht ϖ)
    let ζ : Langlands.GeneralLinear (n + 1) F := GeneralLinear.scalar ϖ
    let f : η.IntertwiningMap η :=
      { toLinearMap := η ζ
        isIntertwining' := fun g => by
          change η ζ * η g = η g * η ζ
          rw [← map_mul, ← map_mul, Matrix.GeneralLinearGroup.scalar_commute ϖ g] }
    obtain ⟨c', hc', -⟩ := admissibleSchur_scalarEndomorphism η hadm hirrη f
    have hη : ∀ y, η ζ y = c' • y := fun y =>
      congrArg (fun t : η.IntertwiningMap η => t y) hc'
    classical
    refine ⟨(Polynomial.nthRoots (n + 1) (c * c')⁻¹).toFinset.image
      (fun w => w / (T.residueCardinality : ℂ) ^ (1 / 2 : ℂ)), fun s hsE B hB => ?_⟩
    exfalso
    have hsE' := spectralPoint_sub_notMem hq (1 / 2) hsE
    obtain ⟨x, y, hxy⟩ : ∃ x y, B.val x y ≠ 0 := by
      by_contra! h0
      exact hB (Subtype.ext (LinearMap.ext fun x => LinearMap.ext fun y => h0 x y))
    have h1 := hlevi s B ζ x y
    rw [determinantWeight_scalar _ _ hq ϖ hϖ, show Mirabolic.levi ζ = z from rfl, hc x, hη y]
      at h1
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
    have hcc : c * c' = (spectralPoint T.residueCardinality (s - 1 / 2) ^ (n + 1))⁻¹ := by
      apply mul_right_cancel₀ hxy
      rw [← h1]
      ring
    apply hsE'
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (Nat.succ_pos n), hcc, inv_inv]
  · -- `ξ` is radical-generated: mixed transfer, then the tower claim `C(n)`.
    let X' := (Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ n).obj (SmoothRep.of ξ hs)
    have hρ : IsSmooth (η.comp (mirabolic n F).subtype) :=
      isSmooth_comp _ continuous_subtype_val hadm.1
    by_cases hX : (⊥ : Subrepresentation X'.representation) = ⊤
    · refine ⟨∅, fun s _ B hB => ?_⟩
      obtain ⟨β', hβ'⟩ := Langlands.AllField.RankinSelberg.UnequalRankMixedTransfer.mixedTransfer F T n ψ V W ξ η hs hadm.1 hg
        (s - 1 / 2) B.val (hlevi s B) (hne s B hB)
      exact absurd (forms_eq_zero_of_bot_eq_top_left hX β') hβ'
    have hXi : X'.representation.IsIrreducible :=
      isIrreducible_of_dichotomy
        (Langlands.AllField.Derivative.Mirabolic.phiMinusIrreducible F T n ψ V ξ hs hirr) hX
    obtain ⟨E, hE⟩ := Langlands.AllField.RankinSelberg.UnequalRankTower.towerClaim F T n ψ (le_refl n) η hadm hirrη W
      (η.comp (mirabolic n F).subtype) hρ LinearMap.id
      (UnequalRankTower.isTower_top ψ η) X' X'.representation X'.isSmooth hXi
    refine ⟨E.image (fun w => w / (T.residueCardinality : ℂ) ^ (3 / 2 : ℂ)),
      fun s hsE B hB => ?_⟩
    have hsE' : spectralPoint T.residueCardinality (s - 1 / 2 - 1) ∉ E := by
      rw [show s - 1 / 2 - 1 = s - 3 / 2 by ring]
      exact spectralPoint_sub_notMem hq (3 / 2) hsE
    obtain ⟨β', hβ'⟩ := Langlands.AllField.RankinSelberg.UnequalRankMixedTransfer.mixedTransfer F T n ψ V W ξ η hs hadm.1 hg
      (s - 1 / 2) B.val (hlevi s B) (hne s B hB)
    obtain ⟨eX, hF⟩ := hE (s - 1 / 2 - 1) hsE' β' hβ'
    exact ⟨nonempty_equiv_of_phiMinus T n (mirabolicFunctionalMultiplicity F T n)
      (mirabolicFunctionalMultiplicity F T (n + 1)) ψ V ξ hs hirr hXi eX, hF⟩

/-- All ranks `r > n`, with a standard Whittaker functional, by induction on `r`. -/
theorem rigidity_of_lt (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI : IsTopologicalRing F := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ (r : ℕ) (hnr : n + 1 ≤ r) (ψ : UnitaryAdditiveCharacter F)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ξ : Representation ℂ (mirabolic r F) V)
      (η : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W),
      IsSmooth ξ → ξ.IsIrreducible → IsAdmissible η → η.IsIrreducible →
      ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
        ∀ B : unequalRankMirabolicForms hnr ψ (normalizedAbsoluteValue T) ξ η s, B ≠ 0 →
          Nonempty (ξ.Equiv (mirabolicCompactInduced ψ r)) ∧
          HasFunctional (N := upperUnipotent (n + 1) F)
            (θ := standardCharacter ψ n) η := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hq : 0 < T.residueCardinality :=
    lt_trans Nat.zero_lt_one T.residueCardinality_gt_one
  intro r hnr
  induction r, hnr using Nat.le_induction with
  | base => exact rigidity_adjacent F T n _
  | succ m hnm ih =>
    intro ψ V _ _ W _ _ ξ η hs hirr hadm hirrη
    let X' := (Langlands.AllField.Derivative.Mirabolic.phiMinusUnnormalized T ψ m).obj (SmoothRep.of ξ hs)
    by_cases hX : (⊥ : Subrepresentation X'.representation) = ⊤
    · refine ⟨∅, fun s _ B hB => ?_⟩
      obtain ⟨B', hB'⟩ := exists_descent_ne_zero T hnm ψ _ ξ hs η s B hB
      exfalso
      apply hB'
      apply Subtype.ext
      ext a w
      rw [eq_zero_of_bot_eq_top hX a]
      simp
    have hXi : X'.representation.IsIrreducible :=
      isIrreducible_of_dichotomy
        (Langlands.AllField.Derivative.Mirabolic.phiMinusIrreducible F T m ψ V ξ hs hirr) hX
    obtain ⟨E, hE⟩ := ih ψ X' W X'.representation η X'.isSmooth hXi hadm hirrη
    refine ⟨E.image (fun w => w / (T.residueCardinality : ℂ) ^ (1 / 2 : ℂ)),
      fun s hsE B hB => ?_⟩
    obtain ⟨B', hB'⟩ := exists_descent_ne_zero T hnm ψ _ ξ hs η s B hB
    obtain ⟨eX, hF⟩ := hE (s - 1 / 2) (spectralPoint_sub_notMem hq (1 / 2) hsE) B' hB'
    exact ⟨nonempty_equiv_of_phiMinus T m (mirabolicFunctionalMultiplicity F T m)
      (mirabolicFunctionalMultiplicity F T (m + 1)) ψ V ξ hs hirr hXi eX, hF⟩

end UnequalRankRigidity

/-- JPSS (1983), Section 2.11, Lemma (printed p.399), for the actual compact and
covariance models: outside finitely many spectral values, a nonzero covariant
pairing forces the compact mirabolic model and an inverse-standard Whittaker
functional. -/
theorem unequalRankMirabolicPairingRigidity (F : Type uF) [Field F]
    (T : LocalFieldData F) (n r : ℕ) :
    UnequalRankMirabolicPairingRigidityStatement.{uF, uV, uW} F T n r := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro hnr ψ V _ _ W _ _ ξ η hs hirr hadm hirrη
  obtain ⟨E, hE⟩ := Langlands.AllField.RankinSelberg.UnequalRankRigidity.rigidity_of_lt.{uF, uV, uW} F T n r hnr ψ V W ξ η hs
    hirr hadm hirrη
  refine ⟨E, fun s hsE B hB => ?_⟩
  obtain ⟨e, hF⟩ := hE s hsE B hB
  exact ⟨e, UnequalRankRigidity.hasFunctional_inverse_of_standard ψ η hF⟩

end Langlands.AllField.RankinSelberg
