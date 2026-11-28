import Langlands.Representation.Archimedean.RealLinkedJacquetFunctional
import Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof
import Langlands.Representation.Archimedean.RealWhittakerMaximallyFaithfulProof
import Langlands.Representation.Archimedean.RealStandardHermitianDual
import Langlands.Representation.Archimedean.RealLanglandsRankOneReduction

/-! # Sorting irreducible generic unitary real standard modules -/

noncomputable section

open scoped ComplexConjugate TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean RealPrincipalSeriesInfChar
open RealStandardCentralGrowth RealLinkedQuotientGrowth
open Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem maximallyFaithful_realStandard {n : ℕ} {ds : List RealBlock}
    (hgen : IsRealGenericGKModule n (realStandardLie n ds)) :
    IsMaximallyFaithful (realStandardLie n ds) :=
  Kostant.realWhittakerMaximallyFaithful n _ _ (realStandardLie_hasInfinitesimalCharacter n ds) hgen

/-- The slow-growth Jacquet witness cannot occur on an irreducible generic standard module,
regardless of the order of its blocks. -/
private theorem no_linkedJacquetFunctional {n : ℕ} {ds : List RealBlock}
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (hgen : IsRealGenericGKModule n (realStandardLie n ds)) :
    ¬ RealLinkedJacquetFunctionalExists n ds := by
  rintro ⟨ℓ, a, e, p, k, hp, hℓ0, hℓ, ha, hY⟩
  obtain ⟨W, hWgk, hWtop, C, hC⟩ := RealLinkedJacquetFunctional.quotientGrowth_of_functional
    realLeftPolynomialGrowth realTaylorLeftPolynomial hℓ0 hℓ ha hY
  have hW : W = ⊥ := (hirr.2 W hWgk.1 hWgk.2).resolve_right hWtop
  let inst := hirr.1
  obtain ⟨c, hc, hcd⟩ := realStandardCentralGrowth n ds (exists_ne 0)
  have hN : 1 ≤ n * (n - 1) := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  refine not_forall_le hc hN (fun d => hcd d
    (LinearMap.llcomp ℂ _ _ _ W.mkQ ∘ₗ (envelopingAction (realStandardLie n ds)).toLinearMap)
    fun u _ hu => maximallyFaithful_realStandard hgen u (LinearMap.ext fun v => ?_))
    hC (fun _ => le_rfl)
  have hv := LinearMap.congr_fun hu v
  rw [LinearMap.comp_apply, LinearMap.llcomp_apply, LinearMap.zero_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hv
  change envelopingAction (realStandardLie n ds) u v ∈ W at hv
  simpa only [hW, Submodule.mem_bot, LinearMap.zero_apply] using hv

/-- An adjacent decreasing pair of nondegenerate blocks is unlinked in any irreducible
and generic real standard module, even when the full list is not ordered. -/
private theorem adjacent_unlinked {n : ℕ} (pre post : List RealBlock) (x y : RealBlock)
    (hrank : realRank (pre ++ x :: y :: post) = n)
    (hirr : IsIrreducibleGKModule (realStandardRep n (pre ++ x :: y :: post))
      (realStandardLie n (pre ++ x :: y :: post)))
    (hgen : IsRealGenericGKModule n (realStandardLie n (pre ++ x :: y :: post)))
    (hx : IsRealBlockNondegenerate x) (hy : IsRealBlockNondegenerate y)
    (hord : realBlockExponent y ≤ realBlockExponent x) : AreRealBlocksUnlinked x y := by
  by_contra hlink
  let c : ℝ := ((realRank post : ℝ) - (realRank pre : ℝ)) / 2
  have hpair := realPairLinkedJacquetFunctional (realBlockTwist c x) (realBlockTwist c y)
    ((isRealBlockNondegenerate_twist c x).2 hx) ((isRealBlockNondegenerate_twist c y).2 hy)
    (by rw [realBlockExponent_twist, realBlockExponent_twist]; linarith)
    (fun h => hlink ((areRealBlocksUnlinked_twist c x y).1 h))
  change RealLinkedJacquetFunctionalExists (realRank ([x, y].map (realBlockTwist c))) _ at hpair
  rw [realRank_map_realBlockTwist] at hpair
  have hstage := realLinkedJacquetFunctionalInStages n pre [x, y] post (by simpa using hrank) hpair
  exact no_linkedJacquetFunctional hirr hgen (by simpa using hstage)

private def hermitianDualDatum : MoeglinDatum → MoeglinDatum
  | .character e s => .character e (-conj s)
  | .discrete p s => .discrete p (-conj s)

private theorem moeglinData_hermitianDual (x : RealBlock) :
    realBlockMoeglinData (realHermitianDualBlock x) =
      (realBlockMoeglinData x).map hermitianDualDatum := by
  cases x with
  | character d =>
      simp [realHermitianDualBlock, realBlockConjExponent, RealLocalJacquet.dualBlock,
        RealCharacterData.inverse, realBlockMoeglinData, RealJacquetFrobenius.charData,
        hermitianDualDatum]
  | induced d =>
      by_cases hd : d.weight = 0 <;>
        simp [realHermitianDualBlock, realBlockConjExponent, RealLocalJacquet.dualBlock,
          ComplexCharacterData.inverse, realBlockMoeglinData, characterOfParams,
          hermitianDualDatum, hd, Int.natAbs_neg]

private theorem nondegenerate_hermitianDual {x : RealBlock} (hx : IsRealBlockNondegenerate x) :
    IsRealBlockNondegenerate (realHermitianDualBlock x) := by
  cases x with
  | character d => trivial
  | induced d =>
      simpa [realHermitianDualBlock, realBlockConjExponent, RealLocalJacquet.dualBlock,
        ComplexCharacterData.inverse, IsRealBlockNondegenerate, characterOfParams] using hx

private theorem reflected_sub_eq {s t r : ℂ} (hr : conj r = r) (h : s - t = r) :
    -conj t - (-conj s) = r := calc
  -conj t - (-conj s) = conj (s - t) := by rw [map_sub]; ring
  _ = r := by rw [h, hr]

private theorem reflected_sub_eq_halfNat_add {s t : ℂ} {p k : ℕ}
    (h : s - t = (p : ℂ) / 2 + k) : -conj t - (-conj s) = (p : ℂ) / 2 + k :=
  reflected_sub_eq (by simp [map_div₀, map_ofNat]) h

private theorem linked_hermitianDual_rev {a b : MoeglinDatum} (h : a.IsLinked b) :
    (hermitianDualDatum b).IsLinked (hermitianDualDatum a) := by
  cases a <;> cases b <;> simp only [MoeglinDatum.IsLinked, hermitianDualDatum] at h ⊢
  · obtain ⟨k, hk, hst, hp⟩ := h
    exact ⟨k, hk, reflected_sub_eq (by simp) hst, by simpa only [add_right_comm k] using hp⟩
  · obtain ⟨k, hk, h | h⟩ := h
    · exact ⟨k, hk, Or.inr (reflected_sub_eq_halfNat_add h)⟩
    · exact ⟨k, hk, Or.inl (reflected_sub_eq_halfNat_add h)⟩
  · obtain ⟨k, hk, h | h⟩ := h
    · exact ⟨k, hk, Or.inr (reflected_sub_eq_halfNat_add h)⟩
    · exact ⟨k, hk, Or.inl (reflected_sub_eq_halfNat_add h)⟩
  · rename_i p s q t
    have hab : ((q : ℤ) - p).natAbs = ((p : ℤ) - q).natAbs := by
      rw [← neg_sub (p : ℤ) q, Int.natAbs_neg]
    rw [hab]
    obtain ⟨k, hk, h | h⟩ := h
    · exact ⟨k, hk, Or.inl (reflected_sub_eq_halfNat_add h)⟩
    · exact ⟨k, hk, Or.inr (reflected_sub_eq_halfNat_add h)⟩

private theorem unlinked_of_hermitianDual_rev {x y : RealBlock}
    (h : AreRealBlocksUnlinked (realHermitianDualBlock y) (realHermitianDualBlock x)) :
    AreRealBlocksUnlinked x y := by
  intro a ha b hb hab
  apply h (hermitianDualDatum b) _ (hermitianDualDatum a) _ (linked_hermitianDual_rev hab)
  · rw [moeglinData_hermitianDual]
    exact List.mem_map_of_mem hb
  · rw [moeglinData_hermitianDual]
    exact List.mem_map_of_mem ha

private theorem adjacent_inversion_unlinked {n : ℕ} (pre post : List RealBlock) (x y : RealBlock)
    (hrank : realRank (pre ++ x :: y :: post) = n)
    (hirr : IsIrreducibleGKModule (realStandardRep n (pre ++ x :: y :: post))
      (realStandardLie n (pre ++ x :: y :: post)))
    (hgen : IsRealGenericGKModule n (realStandardLie n (pre ++ x :: y :: post)))
    (hunit : IsRealUnitarizableGKModule n (realStandardRep n (pre ++ x :: y :: post))
      (realStandardLie n (pre ++ x :: y :: post)))
    (hx : IsRealBlockNondegenerate x) (hy : IsRealBlockNondegenerate y)
    (hxy : realBlockExponent x < realBlockExponent y) : AreRealBlocksUnlinked y x := by
  have hpar := realStandard_hermitianDual_parameter hrank hirr hunit
  rw [List.map_append, List.map_cons, List.map_cons] at hpar
  obtain ⟨hdrank, hdirr, hdgen, _⟩ := realStandardParameter_model hirr hgen hunit hpar
  refine unlinked_of_hermitianDual_rev (adjacent_unlinked (pre.map _) (post.map _)
    (realHermitianDualBlock x) (realHermitianDualBlock y) hdrank hdirr hdgen
    (nondegenerate_hermitianDual hx) (nondegenerate_hermitianDual hy) ?_)
  rw [realBlockExponent_hermitianDual, realBlockExponent_hermitianDual]
  exact neg_le_neg hxy.le

/-- An irreducible generic standard module in Langlands order has unlinked Mœglin data. -/
theorem realStandard_unlinked_of_ordered {n : ℕ} {ds : List RealBlock}
    (hrank : realRank ds = n) (hord : IsRealLanglandsOrdered ds)
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (hgen : IsRealGenericGKModule n (realStandardLie n ds)) : IsRealMoeglinUnlinked ds := by
  by_contra hlink
  let inst := hirr.1
  have hbot : IsGKSubmodule (realStandardRep n ds) (realStandardLie n ds) ⊥ := by
    constructor <;> intro g f hf <;>
      simp only [Submodule.mem_bot] at hf ⊢ <;> rw [hf, map_zero]
  exact realLinkedLanglandsQuotientNotLarge n ds ⊥ hrank hord hlink hbot bot_ne_top
    (fun W hW hne => le_of_eq ((hirr.2 W hW.1 hW.2).resolve_right hne))
    ((isMaximallyFaithfulModulo_bot_iff _).2 (maximallyFaithful_realStandard hgen))

/-- A nondegenerate parameter list of an irreducible generic infinitesimally unitary real
standard module can be sorted using unlinked swaps. The ordered list is unlinked and is
again a standard parameter of that module. -/
theorem exists_realStandard_ordered_unlinked (n : ℕ) (ds : List RealBlock)
    (hrank : realRank ds = n) (hnd : ∀ x ∈ ds, IsRealBlockNondegenerate x)
    (hirr : IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds))
    (hgen : IsRealGenericGKModule n (realStandardLie n ds))
    (hunit : IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds)) :
    ∃ es : List RealBlock, es.Perm ds ∧ IsRealLanglandsOrdered es ∧ IsRealMoeglinUnlinked es ∧
      HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) es := by
  classical
  by_cases hord : IsRealLanglandsOrdered ds
  · exact ⟨ds, .refl _, hord, realStandard_unlinked_of_ordered hrank hord hirr hgen,
      hrank, LinearMap.id, Function.injective_id, isRealStandardIntertwiner_id n ds⟩
  obtain ⟨pre, x, y, post, hds, hxy⟩ := exists_adjacent_inversion_of_not_ordered hord
  subst ds
  have hunl := adjacent_inversion_unlinked pre post x y hrank hirr hgen hunit
    (hnd x (by simp)) (hnd y (by simp)) hxy
  have hperm := (List.Perm.swap x y post).append_left pre
  have hrank' := (realRank_perm hperm).trans hrank
  obtain ⟨B, hBi, hB⟩ := realUnlinkedSwap n pre post y x hrank' hxy.le hunl
  obtain ⟨_, hirr', hgen', hunit'⟩ := realStandardParameter_model hirr hgen hunit
    ⟨hrank', B, hBi, hB⟩
  obtain ⟨es, hes, heso, hesu, hrs, A, hAi, hA⟩ :=
    exists_realStandard_ordered_unlinked n (pre ++ y :: x :: post) hrank'
      (fun z hz => hnd z (hperm.mem_iff.mp hz)) hirr' hgen' hunit'
  exact ⟨es, hes.trans hperm, heso, hesu, hrs, B ∘ₗ A, hBi.comp hAi,
    IsRealStandardIntertwiner.comp_standard hA hB⟩
termination_by realInversionCount ds
decreasing_by
  rw [hds]
  exact realInversionCount_swap_lt pre post hxy

private theorem linked_symm {a b : MoeglinDatum} (h : a.IsLinked b) : b.IsLinked a := by
  cases a <;> cases b <;> simp only [MoeglinDatum.IsLinked] at h ⊢
  · obtain ⟨k, hk, hst, hp⟩ := h
    refine ⟨-k, neg_ne_zero.mpr hk, ?_, ?_⟩
    · rw [Int.cast_neg, ← neg_sub, hst]
    · obtain ⟨m, hm⟩ := hp
      exact ⟨m - k, by omega⟩
  · exact h
  · exact h
  · rename_i p s q t
    rw [← neg_sub (p : ℤ) q, Int.natAbs_neg]
    obtain ⟨k, hk, h⟩ := h
    exact ⟨k, hk, h.symm⟩

/-- Every parameter list of an irreducible generic infinitesimally unitary real standard
module has pairwise unlinked Mœglin data, even with degenerate blocks or out of order. -/
def RealStandardMoeglinUnlinkedNecessityStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
    IsRealGenericGKModule n (realStandardLie n ds) →
    IsRealUnitarizableGKModule n (realStandardRep n ds) (realStandardLie n ds) →
    IsRealMoeglinUnlinked ds

theorem realStandard_moeglinUnlinked_of_unitaryGeneric :
    RealStandardMoeglinUnlinkedNecessityStatement := by
  intro n ds hrank hirr hgen hunit
  let es := ds.flatMap realBlockExpand
  have hmod : realStandardModule n ds = realStandardModule n es := by
    simpa only [List.nil_append] using realStandardModule_append_flatMap_expand n ds []
  have hpar : HasRealStandardParameter n (realStandardRep n ds) (realStandardLie n ds) es :=
    ⟨(realRank_flatMap_expand ds).trans hrank,
      (RealInjectiveIntertwinerExists.refl n ds).of_eq hmod rfl⟩
  obtain ⟨hre, hirre, hgene, hunite⟩ := realStandardParameter_model hirr hgen hunit hpar
  have hnd : ∀ x ∈ es, IsRealBlockNondegenerate x := by
    intro x hx
    obtain ⟨y, _, hy⟩ := List.mem_flatMap.mp hx
    exact isRealBlockNondegenerate_of_mem_expand hy
  obtain ⟨fs, hperm, _, hunl, _⟩ :=
    exists_realStandard_ordered_unlinked n es hre hnd hirre hgene hunite
  have hp : (realMoeglinData fs).Perm (realMoeglinData ds) := by
    rw [← realMoeglinData_flatMap_expand ds]
    exact hperm.flatMap (fun _ _ => .refl _)
  exact (hp.pairwise_iff (fun h hba => h (linked_symm hba))).mp hunl

end Langlands.Archimedean
