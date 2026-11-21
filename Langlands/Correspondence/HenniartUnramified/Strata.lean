import Langlands.Correspondence.HenniartUnramified.Fixed

/-! # Types of exact period and the refined Weil strata -/

noncomputable section

namespace Langlands.Henniart.Numerical

open Correspondence FiniteRepresentation FiniteRepresentation.SplitDegree Weil.Local
open VirtualRepresentation VirtualRepresentation.LocalWeil.Ramification

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {φ : localWeilGroup F}
  {hφ : localDegree F φ = Multiplicative.ofAdd (1 : ℤ)}

/-- Rank and last break of an irreducible representation containing a type of period
`m + 1`. -/
theorem rank_break_of_occurs (A : WeilObj.{uF, uW} F) (B : WType.{uF, uW} F φ hφ)
    (hB : Occurs F φ hφ A.1.representation B) {m : ℕ}
    (hp : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
      ((weilSplit F φ hφ).toClass B) = m + 1) :
    A.1.rank = (m + 1) * Module.finrank ℂ B.1 ∧
      lastBreak F A.1 = inertiaBreak F B.1.representation := by
  obtain ⟨P, hP⟩ := hB
  obtain ⟨u, ⟨e⟩⟩ :=
    (weilStage F φ hφ m).twist_equiv_typeCoind B hp A.1.representation A.2.2 P hP
  constructor
  · change Module.finrank ℂ A.1 = _
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    simp
  · rw [← lastBreak_twist F A.1 u,
      lastBreak_equiv F (A := FiniteRepresentation.of
        (Langlands.twist (unramifiedCharacter (localDegree F) u).toMonoidHom A.1.representation))
        (B := FiniteRepresentation.of ((weilStage F φ hφ m).typeCoind B hp)) e]
    exact lastBreak_typeCoind F φ hφ (weilStage F φ hφ m) B hp

/-- Types of exact period `m + 1`, rank `r` and `r · break = t` are `m + 1` times as many as
the orbits in `W_F((m + 1) r, (m + 1) t, m + 1)`. -/
theorem encard_period_goodTypes (k s m r t : ℕ) (hr : (m + 1) * r = k + 1)
    (ht : (m + 1) * t = s) :
    {x ∈ goodTypes.{uF, uW} F φ hφ r t |
        Function.minimalPeriod ((weilSplit F φ hφ).conjType 1) x = m + 1}.encard =
      (weilRefinedStratum.{uF, uW} F k s (m + 1)).encard * (m + 1 : ℕ) := by
  let S := weilStage F φ hφ m
  let R : TypeClass.{uF, uW} (weilSplit F φ hφ) →
      Weil.UnramifiedOrbitClasses.{uF, uW} (localDegree F) → Prop := fun x c =>
    ∃ (A : WeilObj.{uF, uW} F) (h : A.1.rank = k + 1),
      Weil.unramifiedOrbitClass (localDegree F) ⟨k.succPNat, weilClassOf F A h⟩ = c ∧
      ∃ B : WType.{uF, uW} F φ hφ, (weilSplit F φ hφ).toClass B = x ∧
        Occurs F φ hφ A.1.representation B
  apply encard_eq_mul_of_fibers R (m + 1)
  · -- every type of exact period lies over an orbit of the stratum
    rintro x ⟨⟨B, rfl, hgood⟩, hp⟩
    let A : WeilObj.{uF, uW} F := ⟨FiniteRepresentation.of (S.typeCoind B hp),
      S.typeCoind_continuous B hp, S.typeCoind_isIrreducible B hp⟩
    have hA : A.1.rank = k + 1 := by
      change Module.finrank ℂ (Fin (m + 1) → B.1) = k + 1
      rw [Module.finrank_pi_fintype]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      rw [hgood.1, hr]
    have hocc : Occurs F φ hφ (S.typeCoind B hp) B := by
      refine (occurs_typeCoind_iff S B hp B).mpr ⟨0, ?_⟩
      rw [Fin.val_zero, conjType_zero]
    obtain ⟨P, hP⟩ := hocc
    refine ⟨_, ⟨weilClassOf F A hA, rfl, ?_, ?_⟩, A, hA, rfl, B, rfl, P, hP⟩
    · rw [hasWeilSwan_weilClassOf]
      change (s : ℝ) = (k + 1 : ℕ) * lastBreak F (FiniteRepresentation.of (S.typeCoind B hp))
      rw [lastBreak_typeCoind F φ hφ S B hp, ← hr, ← ht]
      push_cast
      rw [← hgood.2]
      push_cast
      ring
    · exact weilTorsionNumber_eq_period F φ hφ A hA B P hP hp
  · -- functional
    rintro x ⟨-, hp⟩ c - c' - ⟨A, h, hc, B, hB, hocc⟩ ⟨A', h', hc', B', hB', hocc'⟩
    have hocc'' : Occurs F φ hφ A'.1.representation B :=
      occurs_of_class_eq (hB'.trans hB.symm) hocc'
    have hpB : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
        ((weilSplit F φ hφ).toClass B) = m + 1 := by
      rw [hB]
      exact hp
    obtain ⟨z, hz⟩ := exists_twist_of_occurs A A' B hocc hocc'' hpB
    rw [← hc, ← hc']
    exact (weilOrbit_eq_iff F A A' h h').mpr ⟨z, hz⟩
  · -- fibers
    rintro c ⟨σ, rfl, hs, ht'⟩
    obtain ⟨A, h, rfl⟩ := weilClassOf_surjective F σ
    have : Nontrivial A.1 := nontrivial_of_isIrreducible _ A.2.2
    obtain ⟨B, ⟨P, hP⟩, hpos⟩ := exists_occurring_type (D := weilSplit F φ hφ)
      A.1.representation A.2.1
      (Ramification.HerbrandBridge.continuousWeilFiniteInertiaImage F A.1 A.2.1)
    obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    have hT := weilTorsionNumber_eq_period F φ hφ A h B P hP hm'
    rw [ht'] at hT
    have hp : Function.minimalPeriod ((weilSplit F φ hφ).conjType 1)
        ((weilSplit F φ hφ).toClass B) = m + 1 := by
      rw [hm', hT]
    have hocc : Occurs F φ hφ A.1.representation B := ⟨P, hP⟩
    obtain ⟨hrank, hbreak⟩ := rank_break_of_occurs A B hocc hp
    have hgood : TypeGood F φ hφ r t B := by
      have hdim : Module.finrank ℂ B.1 = r := by
        rw [h, ← hr] at hrank
        exact (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) hrank).symm
      refine ⟨hdim, ?_⟩
      have h1 := (hasWeilSwan_weilClassOf F A h s).mp hs
      rw [hbreak, ← hr, ← ht, ← hdim] at h1
      push_cast at h1
      have hm0 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((m : ℝ) + 1) * t = ((m : ℝ) + 1) *
          ((Module.finrank ℂ B.1 : ℝ) * inertiaBreak F B.1.representation) := by
        rw [h1]
        ring
      rw [hdim] at h2
      exact (mul_left_cancel₀ hm0 h2).symm
    refine ⟨fun j => (weilSplit F φ hφ).conjType j ((weilSplit F φ hφ).toClass B), ?_,
      fun j => ⟨⟨?_, ?_⟩, A, h, rfl, (weilSplit F φ hφ).conjObj j B, rfl, ?_⟩, ?_⟩
    · intro j j' hjj
      simp only at hjj
      rw [← iterate_conjType, ← iterate_conjType] at hjj
      exact Fin.ext ((Function.iterate_eq_iterate_iff_of_lt_minimalPeriod
        (by rw [hp]; exact j.isLt) (by rw [hp]; exact j'.isLt)).mp hjj)
    · exact (conjType_mem_goodTypes j _).mpr ((mem_goodTypes_iff B).mpr hgood)
    · dsimp only
      rw [← iterate_conjType, Function.minimalPeriod_apply_iterate
        (Function.minimalPeriod_pos_iff_mem_periodicPts.mp (by rw [hp]; omega)) j, hp]
    · exact (occurs_iff_of_occurs A B hocc hp _).mpr ⟨j, rfl⟩
    · rintro x - ⟨A', h', hc', B', rfl, hocc'⟩
      obtain ⟨z, ⟨e⟩⟩ := (weilOrbit_eq_iff F A' A h' h).mp hc'
      have h1 : Occurs F φ hφ A.1.representation B' :=
        (occurs_twist_iff z).mp (occurs_of_equiv e.symm hocc')
      obtain ⟨j, hj⟩ := (occurs_iff_of_occurs A B hocc hp B').mp h1
      exact ⟨j, hj.symm⟩

/-- The torsion number of a nonempty stratum divides the Swan exponent. -/
theorem dvd_of_mem_weilRefinedStratum {k s f : ℕ}
    {c : Weil.UnramifiedOrbitClasses.{uF, uW} (localDegree F)}
    (hc : c ∈ weilRefinedStratum.{uF, uW} F k s f) : f ∣ s := by
  let φ := localGeometricFrobenius F
  have hφ : localDegree F φ = Multiplicative.ofAdd (1 : ℤ) := localGeometricFrobenius_degree F
  obtain ⟨σ, -, hs, ht⟩ := hc
  obtain ⟨A, h, rfl⟩ := weilClassOf_surjective F σ
  have : Nontrivial A.1 := nontrivial_of_isIrreducible _ A.2.2
  obtain ⟨B, ⟨P, hP⟩, hpos⟩ := exists_occurring_type (D := weilSplit F φ hφ)
    A.1.representation A.2.1
    (Ramification.HerbrandBridge.continuousWeilFiniteInertiaImage F A.1 A.2.1)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
  have hT := weilTorsionNumber_eq_period F φ hφ A h B P hP hm
  rw [ht] at hT
  subst hT
  obtain ⟨hrank, hbreak⟩ := rank_break_of_occurs A B ⟨P, hP⟩ hm
  let S := weilStage F φ hφ m
  let L := (unramifiedStage F (m + 1)).asPadicField (p := p)
  let τ := S.stageRep B hm
  have hτJ : Representation.IsIrreducible
      (τ.comp (weilSplit L (stageLift F φ hφ m) (stageLift_degree F φ hφ m)).inertia.subtype) := by
    rw [S.comp_inertia_eq_block τ, S.block_stageRep B hm]
    exact isIrreducible_comp_surjective _ _ S.ιJ_surjective B.2.2
  have hτ : τ.IsIrreducible := isIrreducible_of_comp τ _ hτJ
  let AL : WeilObj.{uF, uW} L := ⟨FiniteRepresentation.of τ, S.continuous_stageRep B hm, hτ⟩
  have : Nontrivial B.1 := nontrivial_of_isIrreducible _ B.2.2
  obtain ⟨r', hr'⟩ := Nat.exists_eq_succ_of_ne_zero (Module.finrank_pos (R := ℂ) (M := B.1)).ne'
  have hAL : AL.1.rank = r' + 1 := hr'
  have hl : HasWeilSwan L (weilClassOf L AL hAL) (weilSwanLabel L (weilClassOf L AL hAL)) :=
    (hasWeilSwan_iff_eq_label L _ _).mpr rfl
  have h1 := (hasWeilSwan_weilClassOf L AL hAL _).mp hl
  have h2 := lastBreak_stage F φ hφ m τ
  rw [S.block_stageRep B hm] at h2
  change lastBreak L AL.1 = _ at h2
  rw [h2] at h1
  have h3 := (hasWeilSwan_weilClassOf F A h s).mp hs
  have hk : k + 1 = (m + 1) * (r' + 1) := by rw [← h, hrank, hr']
  rw [hbreak, hk] at h3
  refine ⟨weilSwanLabel L (weilClassOf L AL hAL), ?_⟩
  have h4 : (s : ℝ) = ((m + 1) * weilSwanLabel L (weilClassOf L AL hAL) : ℕ) := by
    rw [h3]
    push_cast
    rw [h1]
    push_cast
    ring
  exact_mod_cast h4

end Langlands.Henniart.Numerical
