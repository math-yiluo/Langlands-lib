import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Automorphic.Unramified.CyclicRegularOrbitLiftReductionStatement

/-! # The reduction of cyclic regular orbit lifting -/

noncomputable section

open scoped BigOperators

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.Unramified

open Langlands.Global Langlands.Automorphic.CuspidalOperatorRealization
open Langlands.ClassField.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

variable {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E] [IsGalois F E]
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

omit [CompactSpace (AdeleQuotient F)] in
private theorem regularOrbit_nodup (σ : E ≃ₐ[F] E)
    (hgen : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ)
    {m : ℕ} (c : IsoClass E m)
    (hregular : ∀ i : ℕ, 0 < i → i < Module.finrank F E → ¬ c.IsGaloisStable (σ ^ i)) :
    (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank c)).Nodup := by
  classical
  let d := PositiveRankCuspidalClass.ofFixedRank c
  have horder : orderOf σ = Module.finrank F E :=
    (orderOf_eq_card_of_forall_mem_zpowers hgen).trans (IsGalois.card_aut_eq_finrank F E)
  have hinj : Function.Injective (fun τ : E ≃ₐ[F] E => d.galoisConj τ) := by
    intro a b hab
    change d.galoisConj a = d.galoisConj b at hab
    have hfix : d.galoisConj (b⁻¹ * a) = d := by
      rw [PositiveRankCuspidalClass.galoisConj_mul, hab,
        ← PositiveRankCuspidalClass.galoisConj_mul, inv_mul_cancel,
        PositiveRankCuspidalClass.galoisConj_one]
    have hone : b⁻¹ * a = 1 := by
      obtain ⟨i, hi, he⟩ := Finset.mem_image.mp
        (mem_zpowers_iff_mem_range_orderOf.mp (hgen (b⁻¹ * a)))
      rw [← he] at hfix ⊢
      have hi' : i < Module.finrank F E := horder ▸ Finset.mem_range.mp hi
      have hzero : i = 0 := by
        by_contra hnonzero
        exact hregular i (Nat.pos_of_ne_zero hnonzero) hi'
          ((PositiveRankCuspidalClass.isGaloisStable_iff_galoisConj_ofFixedRank
            (σ ^ i) c).mpr hfix)
      simp only [hzero, pow_zero]
    exact (inv_mul_eq_one.mp hone).symm
  exact Multiset.Nodup.map hinj (Finset.univ : Finset (E ≃ₐ[F] E)).nodup

omit [IsGalois F E] [CompactSpace (AdeleQuotient F)] in
private theorem isUnitary_galoisOrbit {m : ℕ} (T : CuspidalOperatorRealization E m)
    (hT : HasUnitaryCentralCharacter T) :
    (IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass)).IsUnitary := by
  intro c hc
  obtain ⟨τ, _, rfl⟩ := Multiset.mem_map.mp hc
  let e := τ.toRingEquiv.symm
  change (T.arithmeticComap e).realization.IsUnitarizable
  obtain ⟨χ, hχ, hcentral⟩ := hT
  exact (T.arithmeticComap e).isUnitarizable_of_hasUnitaryCentralCharacter
    ⟨HeckeCharacter.comap e χ, (HeckeCharacter.isUnitary_comap_iff e χ).mpr hχ,
      (T.arithmeticComap_hasCentralCharacter_iff e χ).mpr hcentral⟩

/-- Actual regular induction, the weak base change comparison and the pair
multiplicity formula imply the regular orbit lift and its uniqueness. -/
theorem cyclicRegularOrbitLiftReduction : CyclicRegularOrbitLiftReductionStatement.{uF, uE, uV, uW} := by
  classical
  intro hexists hcomparison hpairs F E _ _ _ _ _ _ _ _ σ hgen η hη m T hT hregular
  let _ : IsCyclic (E ≃ₐ[F] E) := ⟨⟨σ, hgen⟩⟩
  obtain ⟨r, S, hrank, hS, hInd⟩ := hexists F E σ hgen m T hT hregular
  let c := PositiveRankCuspidalClass.ofFixedRank S.isoClass
  let lower := IsobaricData.ofCuspidal c
  let orbit := IsobaricData.galoisOrbit F (PositiveRankCuspidalClass.ofFixedRank T.isoClass)
  have hlower : lower.IsUnitary :=
    IsobaricData.isUnitary_ofCuspidal.mpr (S.isUnitarizable_of_hasUnitaryCentralCharacter hS)
  have horbit : orbit.IsUnitary := isUnitary_galoisOrbit T hT
  have hBC : IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} orbit lower :=
    hcomparison F E S.isoClass T.isoClass hInd
  have horbitCount : IsobaricData.equalConstituentPairCount orbit orbit = Module.finrank F E := by
    have hnodup : orbit.Nodup := regularOrbit_nodup σ hgen T.isoClass hregular
    have hmap : orbit.map (fun d => orbit.count d) = orbit.map (fun _ => (1 : ℕ)) :=
      Multiset.map_congr rfl fun _ hd => Multiset.count_eq_one_of_mem hnodup hd
    unfold IsobaricData.equalConstituentPairCount
    rw [hmap, Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]
    simp only [orbit, IsobaricData.galoisOrbit, Multiset.card_map, Finset.card_val,
      Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  let finiteOrder (i : ℕ) : (η ^ i).HasFiniteOrder :=
    HeckeCharacter.IsTrivialOnNorm.hasFiniteOrder E (by
      intro x
      rw [ContinuousMonoidHom.pow_apply, hη.isTrivialOnNorm x, one_pow])
  let twist (i : ℕ) := c.determinantTwist (η ^ i) (finiteOrder i)
  have hcount (D : IsobaricData F) (hD : D.IsUnitary)
      (hDBase : IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} orbit D) :
      (∑ i ∈ Finset.range (Module.finrank F E), D.count (twist i)) = Module.finrank F E := by
    have h := hpairs F E η hη lower D orbit orbit hlower hD horbit horbit hBC hDBase
    dsimp only at h
    rw [horbitCount] at h
    simpa only [lower, IsobaricData.ofCuspidal, IsobaricData.equalConstituentPairCount,
      Multiset.map_singleton, Multiset.sum_singleton] using h
  have hfixed (i : ℕ) (hi : i ∈ Finset.range (Module.finrank F E)) : twist i = c := by
    have hle (j : ℕ) (_ : j ∈ Finset.range (Module.finrank F E)) : lower.count (twist j) ≤ 1 :=
      (Multiset.count_le_card _ _).trans_eq (Multiset.card_singleton _)
    have hsum := (Finset.sum_eq_sum_iff_of_le (g := fun _ => (1 : ℕ)) hle).mp
      (by simpa using hcount lower hlower hBC)
    have hmem : twist i ∈ lower := Multiset.count_pos.mp (by simp only [hsum i hi, Nat.zero_lt_one])
    simpa only [lower, IsobaricData.ofCuspidal, Multiset.mem_singleton] using hmem
  have hfinite := hη.isTrivialOnNorm.hasFiniteOrder E
  have hself : S.isoClass.determinantTwist η hfinite = S.isoClass := by
    by_cases hdegree : 1 < Module.finrank F E
    · apply PositiveRankCuspidalClass.ofFixedRank_injective r
      simpa only [twist, c, pow_one, PositiveRankCuspidalClass.determinantTwist_ofFixedRank] using
        hfixed 1 (Finset.mem_range.mpr hdegree)
    · have hd : Module.finrank F E = 1 := by
        have := Module.finrank_pos (R := F) (M := E)
        omega
      have heta : η = 1 := by
        simpa only [hd, pow_one] using hη.isTrivialOnNorm.pow_finrank_eq_one E
      simpa only [heta] using IsoClass.determinantTwist_one S.isoClass
  refine ⟨r, S.isoClass, hrank, hlower,
    (IsoClass.isFiniteOrderDeterminantTwist_iff_eq _ _ η hfinite).mpr hself.symm, ?_⟩
  intro D hD
  change IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} orbit D ↔ D = lower
  refine ⟨fun hDBase => ?_, fun h => h ▸ hBC⟩
  have hsum : Module.finrank F E * D.count c = Module.finrank F E := by
    calc
      Module.finrank F E * D.count c = ∑ _i ∈ Finset.range (Module.finrank F E), D.count c := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
      _ = ∑ i ∈ Finset.range (Module.finrank F E), D.count (twist i) :=
        Finset.sum_congr rfl fun i hi => congrArg (Multiset.count · D) (hfixed i hi).symm
      _ = Module.finrank F E := hcount D hD hDBase
  have hone : D.count c = 1 :=
    Nat.eq_of_mul_eq_mul_left Module.finrank_pos (hsum.trans (mul_one _).symm)
  have hmem : c ∈ D := Multiset.count_pos.mp (by simp only [hone, Nat.zero_lt_one])
  have hrankD : D.rank = lower.rank := hDBase.rank_eq.symm.trans hBC.rank_eq
  have herase : IsobaricData.rank (D.erase c) = 0 := by
    have h := (congrArg IsobaricData.rank (Multiset.cons_erase hmem)).trans hrankD
    change IsobaricData.rank (c ::ₘ D.erase c) = (IsobaricData.ofCuspidal c).rank at h
    rw [IsobaricData.rank_cons, IsobaricData.rank_ofCuspidal] at h
    omega
  have hzero : D.erase c = 0 := by
    by_contra hnonempty
    have hpos := (IsobaricData.rank_pos_iff _).mpr hnonempty
    omega
  rw [← Multiset.cons_erase hmem, hzero]
  rfl

end Langlands.Automorphic.Unramified
