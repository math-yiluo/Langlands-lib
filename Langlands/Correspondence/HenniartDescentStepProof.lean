import Langlands.Correspondence.HenniartDescentWeil
import Langlands.Correspondence.HenniartRefinedStrataProof
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof
import Langlands.Representation.Conductor.SupercuspidalPadicGenericConductor
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationSupport
import Langlands.Representation.RankinSelberg.UnramifiedUnitaryPoleFreeProof

/-! # Descent of the refined numerical counts through a cyclic prime step -/

noncomputable section

namespace Langlands.Henniart

open Correspondence Numerical FiniteRepresentation CategoryTheory HarmonicAnalysis

universe uK uW uV

private theorem hasSupercuspidalSwan_exponent {p : ℕ} [Fact p.Prime]
    (K : PadicField.{uK} p) {k : ℕ}
    (π : SupercuspidalAutomorphicClass.{uK, uV} K k.succPNat) :
    HasSupercuspidalSwan K π (supercuspidalSwanExponent K π) := by
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  let := K.canonicalTopologicalData.localField
  change GeneralLinear.SupercuspidalClass.{uV, uK} (F := K.Carrier) (n := k + 1) at π
  obtain ⟨A, rfl⟩ := Quotient.exists_rep π
  obtain ⟨ψ₀⟩ := padicUnitaryAdditiveCharacterExists K K.canonicalTopologicalData
  obtain ⟨a, hψ⟩ := RankinSelberg.UnramifiedUnitary.exists_scale_hasIntegerConductor K ψ₀
  have hgen := RankinSelberg.SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal
    K (ψ₀.scale a) k A.obj A.property.1 A.property.2
  obtain ⟨m, -, hm, -⟩ := Conductor.genericConductor_isNewvectorConductor_of_supercuspidalPadic K
    Conductor.supercuspidalPadicConductorExponent (ψ₀.scale a) hψ A.obj.representation hgen
    A.property.2
  have hc : Numerical.conductor K (⟦A⟧ : SupercuspidalAutomorphicClass K k.succPNat) = (m : WithTop ℕ) := by
    change GeneralLinear.SupercuspidalClass.firstFixedLevel A.isoClass = _
    rw [GeneralLinear.SupercuspidalClass.firstFixedLevel_isoClass]
    have hex : Conductor.HasNewvectorLevel A.obj.representation := ⟨m, hm.1⟩
    rw [Conductor.firstFixedLevel_of_hasNewvectorLevel _ hex,
      (Conductor.newvectorConductor_eq_iff _ hex _).mpr hm]
  refine ⟨m, hc, ?_⟩
  change m - (k + 1) = WithTop.untopD 0 (Numerical.conductor K (k := k) ⟦A⟧) - (k + 1)
  rw [hc]
  rfl

section Step

variable {p : ℕ} [Fact p.Prime] (S : CyclicPrimeStep.{uK} p)

private theorem conjugate_one {k : ℕ}
    (P : SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) :
    S.galoisConjugate 1 k P = P := by
  let := S.top.canonicalTopologicalData.topology
  obtain ⟨A, rfl⟩ := Quotient.exists_rep P
  apply Quotient.sound
  refine ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A.obj) ?_))⟩
  intro g
  rfl

private theorem conjugate_mul {k : ℕ}
    (P : SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) (g h : S.Gal) :
    S.galoisConjugate h k (S.galoisConjugate g k P) = S.galoisConjugate (g * h) k P := by
  let := S.top.canonicalTopologicalData.topology
  obtain ⟨A, rfl⟩ := Quotient.exists_rep P
  apply Quotient.sound
  refine ⟨ObjectProperty.isoMk _ (SmoothRep.mkIso (Representation.Equiv.mk (LinearEquiv.refl ℂ A.obj) ?_))⟩
  intro x
  rfl

private theorem orbit_nodup {k : ℕ}
    (P : SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat)
    (hfree : ∀ g : S.Gal, g ≠ 1 → S.galoisConjugate g k P ≠ P) : (S.galoisOrbit P).Nodup := by
  classical
  unfold CyclicPrimeStep.galoisOrbit
  apply Multiset.Nodup.map ?_ (Finset.nodup _)
  intro g h heq
  have heq' := congrArg (S.galoisConjugate h⁻¹ k) (Sigma.mk.inj_iff.mp heq).2.eq
  rw [conjugate_mul, conjugate_mul, mul_inv_cancel, conjugate_one] at heq'
  exact (mul_inv_eq_one.mp (by by_contra! hne; exact hfree _ hne heq'))

private theorem orbit_card {k : ℕ}
    (P : SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) :
    (S.galoisOrbit P).card = S.degree := by
  have : Finite S.Gal := S.finite_gal
  let : Fintype S.Gal := Fintype.ofFinite _
  unfold CyclicPrimeStep.galoisOrbit
  rw [Multiset.card_map, Finset.card_val, Finset.card_univ, Fintype.card_eq_nat_card,
    S.degree_eq_card]

private theorem mem_orbit {k : ℕ}
    (P : SupercuspidalAutomorphicClass.{uK, uV} S.top k.succPNat) :
    (⟨k, P⟩ : Σ j : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top j.succPNat) ∈ S.galoisOrbit P := by
  have : Finite S.Gal := S.finite_gal
  let : Fintype S.Gal := Fintype.ofFinite _
  unfold CyclicPrimeStep.galoisOrbit
  exact Multiset.mem_map.mpr ⟨1, Finset.mem_univ _, by rw [conjugate_one]⟩

private theorem fixed_by_all_of_fixed_by_one {k : ℕ}
    (π : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat)
    {η₀ : QuasiCharacter S.base} (hη₀ : η₀ ∈ S.normCharacters) (hne : η₀ ≠ 1)
    (hfix : supercuspidalCharacterTwist S.base k η₀ π = π) :
    ∀ η ∈ S.normCharacters, supercuspidalCharacterTwist S.base k η π = π := by
  have hpow : ∀ j : ℕ, supercuspidalTwist S.base (η₀ ^ j) π = π := by
    intro j
    induction j with
    | zero => exact supercuspidalTwist_one S.base π
    | succ j ih => rw [pow_succ', ← supercuspidalTwist_twist, ih]; exact hfix
  intro η hη
  obtain ⟨j, rfl⟩ := S.exists_pow_eq_of_ne_one hη₀ hne hη
  exact hpow j

private theorem singletonDecomposition {k : ℕ}
    (σ : IrreducibleWeilClass.{uK, uW} S.base k.succPNat)
    (T : IrreducibleWeilClass.{uK, uW} S.top k.succPNat)
    (h : Weil.Local.extensionRestrictClass S.base S.top S.embedding (weilClassForget S.base σ) =
      weilClassForget S.top T) :
    IsRestrictionDecomposition S σ {⟨k, T⟩} := by
  refine ⟨[⟨k, T⟩], rfl, h.trans ?_⟩
  obtain ⟨T, hT⟩ := T
  obtain ⟨A, rfl⟩ := Quotient.exists_rep T
  change classOf A.val = directSumClass (fun _ : Fin 1 => classOf A.val)
  rw [directSumClass_classOf]
  apply (classOf_eq_iff _ _).2
  refine ⟨(Representation.Equiv.mk (DirectSum.linearEquivFunOnFintype ℂ (Fin 1) (fun _ => A.val) |>.trans
    (LinearEquiv.funUnique (Fin 1) ℂ A.val)) ?_).symm⟩
  intro g
  apply LinearMap.ext
  intro v
  change DirectSum.lmap (fun _ : Fin 1 => A.val.representation g) v 0 = A.val.representation g (v 0)
  exact DirectSum.lmap_apply _ _ _

private theorem singleton_fibre_surjective {k : ℕ}
    (Ch : CyclicBaseChangeMap.{uK, uV} S)
    (π : SupercuspidalAutomorphicClass.{uK, uV} S.base k.succPNat)
    (hTw : ∀ η ∈ S.normCharacters, Ch k (supercuspidalCharacterTwist S.base k η π) = Ch k π)
    (hFibre : ∀ π', Ch k π' = Ch k π →
      ∃ η ∈ S.normCharacters, π' = supercuspidalCharacterTwist S.base k η π)
    (f : Fin S.degree → {π' // Ch k π' = Ch k π}) (hf : Function.Injective f) :
    Function.Surjective f := by
  let tw : S.normCharacters → {π' // Ch k π' = Ch k π} :=
    fun η => ⟨supercuspidalCharacterTwist S.base k η.1 π, hTw η.1 η.2⟩
  have htw : Function.Surjective tw := by
    rintro ⟨π', hπ'⟩
    obtain ⟨η, hη, rfl⟩ := hFibre π' hπ'
    exact ⟨⟨η, hη⟩, rfl⟩
  have : Finite S.normCharacters := S.normCharacters_finite_ncard.1
  have : Finite {π' // Ch k π' = Ch k π} := Finite.of_surjective tw htw
  apply (hf.bijective_of_nat_card_le ?_).2
  rw [Nat.card_fin]
  exact (Nat.card_le_card_of_surjective tw htw).trans S.normCharacters_finite_ncard.2

end Step

/-- Refined numerical counts descend through a cyclic prime-degree step
(Henniart 1988, §6.8, and the numerical route note, Lemma `lem:step`). -/
theorem descentStep : DescentStepStatement.{uK, uW, uV} := by
  classical
  intro hSwan hArtin p _ S N φL φM Ch hφ hWeak hCompat hReflect x hCounts
  have hCountL := refinedStrata.{uK, uW, uV}.2 p S.base x N
  have hCountM := refinedStrata.{uK, uW, uV}.2 p S.top (S.herbrandPsi x) N
  refine hCountL.2 (fun k _ σ => hArtin p S.base k σ) (fun k hk => ?_)
  refine ⟨φL k hk, (hφ k hk).1, ?_⟩
  intro π s hs hx
  obtain ⟨-, hGal, hTw, hSingle, hOrbit, -⟩ := (hWeak k).1 π
  have hLift : ∀ j (P : SupercuspidalAutomorphicClass.{uK, uV} S.top j.succPNat),
      ⟨j, P⟩ ∈ Ch k π → ∀ hj : j + 1 ≤ N, P ∈ Set.range (φM j hj) := by
    intro j P hP hj
    exact hCountM.1 hCounts j hj _ (hφ j hj).2 P _ (hasSupercuspidalSwan_exponent S.top P)
      (baseChangeSlope hSwan p S Ch hWeak k π x s hs hx ⟨j, P⟩ hP)
  by_cases hFree : ∀ η ∈ S.normCharacters, η ≠ 1 →
      supercuspidalCharacterTwist S.base k η π ≠ π
  · obtain ⟨⟨P, hP⟩, hFibre⟩ := hSingle hFree
    obtain ⟨T, hT⟩ := hLift k P (by simp [hP]) hk
    have hPfix (g : S.Gal) : S.galoisConjugate g k (φM k hk T) = φM k hk T := by
      have hg := hGal g
      rw [hP, Multiset.map_singleton, Multiset.singleton_inj] at hg
      rw [hT]
      exact (Sigma.mk.inj_iff.mp hg).2.eq
    obtain ⟨f, hf, hfRes⟩ := DescentWeil.extensions S k T (hReflect k hk T hPfix)
    have hBC (i : Fin S.degree) : Ch k (φL k hk (f i)) = Ch k π := by
      have hBound : ∀ t ∈ ({⟨k, T⟩} : Multiset (Σ j : ℕ, IrreducibleWeilClass.{uK, uW} S.top j.succPNat)),
          t.1 + 1 ≤ N := by
        intro t ht
        rwa [Multiset.mem_singleton.mp ht]
      rw [hCompat k hk (f i) _ (singletonDecomposition S _ T (hfRes i)) hBound, hP]
      change ({⟨k, φM k hk T⟩} : Multiset (Σ a : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top a.succPNat)) = {⟨k, P⟩}
      rw [hT]
    let F : Fin S.degree → {π' // Ch k π' = Ch k π} := fun i => ⟨φL k hk (f i), hBC i⟩
    have hinj : Function.Injective F := fun _ _ hij =>
      hf ((hφ k hk).1.1 (congrArg Subtype.val hij))
    obtain ⟨i, hi⟩ := singleton_fibre_surjective S Ch π hTw
      (fun π' hπ' => (hFibre π').mp hπ') F hinj ⟨π, rfl⟩
    exact ⟨f i, congrArg Subtype.val hi⟩
  · simp only [not_forall, not_not, exists_prop] at hFree
    obtain ⟨η, hη, hne, hfix⟩ := hFree
    obtain ⟨hdvd, ⟨j, P, hj, hfree, hP⟩, hUnique⟩ :=
      hOrbit (fixed_by_all_of_fixed_by_one S π hη hne hfix)
    have hrank : k + 1 = (j + 1) * S.degree := by rw [hj, Nat.div_mul_cancel hdvd]
    have hjN : j + 1 ≤ N := (hj ▸ Nat.div_le_self _ _).trans hk
    obtain ⟨T, hT⟩ := hLift j P (hP ▸ mem_orbit S P) hjN
    have hnfix : ¬ ∀ w, weilConjugate S w T = T := by
      intro hfixT
      obtain ⟨f, -, hf⟩ := DescentWeil.extensions S j T hfixT
      let i : Fin S.degree := ⟨0, S.degree_prime.pos⟩
      have hb : ∀ t ∈ ({⟨j, T⟩} : Multiset (Σ a : ℕ, IrreducibleWeilClass.{uK, uW} S.top a.succPNat)),
          t.1 + 1 ≤ N := by
        intro t ht
        rwa [Multiset.mem_singleton.mp ht]
      have hc : Ch j (φL j hjN (f i)) = {⟨j, P⟩} := by
        rw [hCompat j hjN (f i) _ (singletonDecomposition S _ T (hf i)) hb]
        change ({⟨j, φM j hjN T⟩} : Multiset (Σ a : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top a.succPNat)) = {⟨j, P⟩}
        rw [hT]
      have : Finite S.Gal := S.finite_gal
      have : Nontrivial S.Gal := Finite.one_lt_card_iff_nontrivial.mp
        (S.degree_eq_card ▸ S.degree_prime.one_lt)
      obtain ⟨g, hg⟩ := exists_ne (1 : S.Gal)
      have h := ((hWeak j).1 (φL j hjN (f i))).2.1 g
      rw [hc, Multiset.map_singleton, Multiset.singleton_inj] at h
      exact hfree g hg (Sigma.mk.inj_iff.mp h).2.eq
    obtain ⟨σ, m, hRes, hmT, hmCard, hmRank⟩ := DescentWeil.induction S k j T hrank hnfix
    have hBound : ∀ t ∈ m, t.1 + 1 ≤ N := fun t ht => by rw [hmRank t ht]; exact hjN
    have hCh := hCompat k hk σ m hRes hBound
    have hMem : (⟨j, P⟩ : Σ a : ℕ, SupercuspidalAutomorphicClass.{uK, uV} S.top a.succPNat) ∈
        Ch k (φL k hk σ) := by
      rw [hCh]
      exact Multiset.mem_pmap.mpr ⟨⟨j, T⟩, hmT, congrArg (Sigma.mk j) hT⟩
    refine ⟨σ, hUnique _ ?_⟩
    rw [hP]
    apply Eq.symm
    apply Multiset.eq_of_le_of_card_le
    · apply (Multiset.le_iff_subset (orbit_nodup S P hfree)).mpr
      intro ρ hρ
      obtain ⟨g, -, rfl⟩ := Multiset.mem_map.mp hρ
      have h := Multiset.mem_map_of_mem (S.galoisConjugateSigma g) hMem
      rwa [((hWeak k).1 (φL k hk σ)).2.1 g] at h
    · rw [hCh, Multiset.card_pmap, hmCard, orbit_card]

end Langlands.Henniart
