import Langlands.Global.ArthurTruncationConstantTermExpansion
import Langlands.Global.ArthurTruncationWeylPositivity
import Langlands.Global.ArthurTruncationAlternation
import Langlands.GroupScheme.Rational.StandardLeviTwistedRootSupport

/-! # Cancellation in each Weyl cell of the constant term -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Group.RelativeWeylIndexing Langlands.Aubert.General.RationalPointFamily
  Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints ArthurParabolicSpaces

section FiniteSums

variable {B W : Type*} [Fintype B] [Fintype W] [Group W]
  {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Exchange the standard-parabolic and Weyl sums, keeping the admissible indices. -/
theorem sum_minimal_swap (Q : Finset B) (f : Finset B → W → ℂ) :
    (∑ S : Finset B, ∑ w ∈ Finset.univ.filter (IsMinimal cs Q S), f S w) =
      ∑ w ∈ Finset.univ.filter (IsMinimal cs Q ∅),
        ∑ S ∈ (positiveSimpleSet cs w).powerset, f S w := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : IsMinimal cs Q ∅ w
  · rw [ite_eq_left hw, ← Finset.sum_filter]
    congr 1
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset]
    exact (isMinimal_iff_leftMinimal_and_subset cs).trans (and_iff_right hw)
  · rw [ite_eq_right hw]
    refine Finset.sum_eq_zero fun S _ => ite_eq_right fun hmin => ?_
    exact hw (((isMinimal_iff_leftMinimal_and_subset cs).mp hmin).1)

end FiniteSums

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {i : T.toGrp ⟶ G}
  [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (Standard.parabolicHom i ν ∅) K)
  (hρ : Function.Bijective (restrictToTorus F i ν ∅))

local notation "A" => AdelicGroupPoints F G
local notation "B" => SimpleRoot i ν
local notation "W" => relativeWeylGroup i
local notation "roots" => rootSet i ν
local notation "p" => Standard.parabolicHom i ν
local notation "r" => Standard.unipotentHom i ν
local notation "H" => height hi hK hρ
local notation "λ₀" => fundamentalWeight hG hi hν D
local notation "N₀" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (r ∅))

variable [Fintype (SimpleRoot i ν)] [Fintype (relativeWeylGroup i)]
  {M : CoxeterMatrix (SimpleRoot i ν)} (cs : CoxeterSystem M (relativeWeylGroup i))
  (hcs : IsRelativeWeylCoxeterRealization i ν cs)

omit [NumberField F] [LocallyOfFiniteType G.X.hom] [Fintype (relativeWeylGroup i)] in
private theorem tauHat_eq_ite (S : Finset B) (z : V T) :
    (ArthurRelative.tauHat hG hi ν D (roots S) (simpleRelativeRoots i ν) z : ℂ) =
      if ∀ a ∈ (Finset.univ : Finset B) \ S,
        0 < ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a.val z then 1 else 0 := by
  classical
  rw [ArthurRelative.tauHat_eq hG hi D (ν := ν) _ Set.Subset.rfl]
  simp only [Int.cast_ite, Int.cast_one, Int.cast_zero]
  apply if_congr ?_ rfl rfl
  constructor
  · intro h a ha
    exact h a.val ⟨a.2, fun has => (Finset.mem_sdiff.mp ha).2 ((val_mem_rootSet i ν S a).mp has)⟩
  · intro h a ha
    exact h ⟨a, ha.1⟩ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun has => ha.2 ((val_mem_rootSet i ν S ⟨a, ha.1⟩).mpr has)⟩)

include hν hcs in
set_option maxHeartbeats 1400000 in
/-- For a left-minimal representative, the signed sum of its admissible terms vanishes
whenever a weight outside the testing parabolic is positive on every translated orbit. -/
theorem bruhatCutoffSum_eq_zero_of_leftMinimal
    (hunf : GeometricLemmaUnfoldingStatement.{u}) (Q : Finset B)
    (n : W → normalizerPoints i) (hn : ∀ w, (QuotientGroup.mk (n w) : W) = w)
    (w : W) (hw : IsMinimal cs Q ∅ w) (β : B) (hβ : β ∉ Q)
    (Tp : V T) (φ : A → ℂ) (hφ : IsLocallyBoundedInvariant (rationalSubgroup F G) φ) (x : A)
    (hpositive : ∀ (delta : rationalImage F (p (roots Q))) (v : N₀),
      0 < pair T (relativeWeylFullRealAction i w⁻¹ (λ₀ β))
        (H ((innerAdelicPoint F G (n w).val)⁻¹ * (v : A) * ((delta : A) * x)) - Tp)) :
    ∑ S ∈ (positiveSimpleSet cs w).powerset, (-1 : ℂ) ^ (Fintype.card B - S.card) *
      bruhatCutoffSum hG hi D hK hρ Q S (intersectionSubset cs Q S w) (intersectionSubset cs S Q w⁻¹)
        (innerAdelicPoint F G (n w).val) Tp φ x = 0 := by
  classical
  let allowed := positiveSimpleSet cs w
  let neutral := allowed ∩ simpleImage cs w⁻¹ Q
  let free := allowed \ neutral
  let wA := innerAdelicPoint F G (n w).val
  let ξ : Vstar T := relativeWeylFullRealAction i w⁻¹ (λ₀ β)
  let coeff (a : B) := pair T ξ (D.realCoroot (simpleToRelativeRoot i ν a))
  let sign (S : Finset B) : ℂ := (-1 : ℂ) ^ (Fintype.card B - S.card)
  let R (J : Finset B) := simpleImage cs w J ∩ Q
  let C (S J : Finset B) := bruhatCutoffSum hG hi D hK hρ Q S J (R J) wA Tp φ x
  have hAllowed : free ∪ neutral = allowed := Finset.sdiff_union_of_subset Finset.inter_subset_left
  have hDisjoint : Disjoint free neutral := Finset.disjoint_sdiff.symm
  have hmin (S : Finset B) (hS : S ∈ allowed.powerset) : IsMinimal cs Q S w :=
    (isMinimal_iff_leftMinimal_and_subset cs).mpr ⟨hw, Finset.mem_powerset.mp hS⟩
  have hJ (S : Finset B) (hS : S ∈ allowed.powerset) : intersectionSubset cs Q S w = S ∩ neutral :=
    intersectionSubset_eq_neutral_inter cs (hmin S hS)
  have hR (S : Finset B) (hS : S ∈ allowed.powerset) : intersectionSubset cs S Q w⁻¹ = R (S ∩ neutral) := by
    rw [intersectionSubset_inv_eq_of_image cs (hmin S hS), hJ S hS]
  obtain ⟨ζ, hζ⟩ := (standardCocharacter F G hG T i hi ν hν _ (rootSet_subset i ν Q)).1
  have hβ' : β.val ∉ roots Q := fun h => hβ ((val_mem_rootSet i ν Q β).mp h)
  have hroot (a : B) : a ∈ allowed ↔ schemeWeylCharacterAction i w a.val ∈ positiveRelativeRoots i ν :=
    (mem_positiveSimpleSet cs w a).trans ((hcs.2.2.1 w a))
  have hCoeff (a : B) := fundamentalWeight_weyl_coroot_sign hG hi hν D β a w⁻¹ hζ hβ'
  have hCoeff₁ : ∀ a ∈ free, 0 ≤ coeff a := by
    intro a ha
    rw [Finset.mem_sdiff] at ha
    exact (hCoeff a).1 (by rw [inv_inv]; exact (hroot a).mp ha.1)
  have hCoeff₂ : ∀ a ∈ neutral, coeff a = 0 := by
    intro a ha
    have hSa : ({a} : Finset B) ∈ allowed.powerset :=
      Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp ha).1)
    have hIa : a ∈ intersectionSubset cs Q {a} w := by rw [hJ _ hSa]; simp [ha]
    have hzero := ((hcs.mem_intersectionSubset_iff_pairing_eq_zero hν hζ w a).mp hIa).2
    exact (hCoeff a).2.2 (by rw [inv_inv]; exact (hroot a).mp (Finset.mem_inter.mp ha).1)
      (by rwa [inv_inv])
  have hCoeff₃ : ∀ a ∈ (Finset.univ : Finset B), a ∉ free ∪ neutral → coeff a ≤ 0 := by
    intro a _ ha
    exact (hCoeff a).2.1 (by rw [inv_inv]; exact fun hr => ha (hAllowed.symm ▸ (hroot a).mpr hr))
  change (∑ S ∈ allowed.powerset, sign S * bruhatCutoffSum hG hi D hK hρ Q S
    (intersectionSubset cs Q S w) (intersectionSubset cs S Q w⁻¹) wA Tp φ x) = 0
  calc
    _ = ∑ S ∈ allowed.powerset, sign S * C S (S ∩ neutral) := by
      apply Finset.sum_congr rfl
      intro S hS
      unfold C
      rw [hJ S hS, hR S hS]
    _ = ∑ J ∈ neutral.powerset, ∑ S ∈ allowed.powerset.filter (fun S => S ∩ neutral = J),
          sign S * C S (S ∩ neutral) :=
      (Finset.sum_fiberwise_of_maps_to (g := fun S => S ∩ neutral)
        (fun _ _ => Finset.mem_powerset.mpr Finset.inter_subset_right) _).symm
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro J _
      let fiber := allowed.powerset.filter (fun S => S ∩ neutral = J)
      let G₁ (c : BruhatOuterCosets Q (R J)) : A := ((c.out : rationalImage F (p (roots Q))) : A) * x
      let Y := BruhatRadicalQuotient J (R J) wA
      let m := bruhatRadicalMeasure J (R J) wA
      let k (S : Finset B) (c : BruhatOuterCosets Q (R J)) (v : Y) :=
        bruhatCutoffIntegrand hG hi D hK hρ S J (R J) wA Tp φ (G₁ c) v
      have hdata (S : Finset B) (hS : S ∈ fiber) :
          (∀ c, Integrable (k S c) m) ∧ Summable (fun c => ∫ v, k S c v ∂m) := by
        obtain ⟨hS, hSJ⟩ := Finset.mem_filter.mp hS
        let j : {w : W // IsMinimal cs Q S w} := ⟨w, hmin S hS⟩
        obtain ⟨hiS, hsumS, -⟩ := constantTerm_cutoffSeries_bruhat hG hi hν D hK hρ
          hunf cs hcs Q S n hn Tp φ hφ x
        have heJ : intersectionSubset cs Q S j.val = J := (hJ S hS).trans hSJ
        have heR : intersectionSubset cs S Q j.val⁻¹ = R J := (hR S hS).trans (congrArg R hSJ)
        let conditions (J R : Finset B) :=
          let L (c : BruhatOuterCosets Q R) :=
            bruhatCutoffIntegrand hG hi D hK hρ S J R wA Tp φ
              (((c.out : rationalImage F (p (roots Q))) : A) * x)
          let mu := bruhatRadicalMeasure J R wA
          (∀ c, Integrable (L c) mu) ∧ Summable (fun c => ∫ v, L c v ∂mu)
        have hc : conditions (intersectionSubset cs Q S j.val) (intersectionSubset cs S Q j.val⁻¹) :=
          ⟨hiS j, hsumS j⟩
        rw [heJ, heR] at hc
        exact hc
      calc
        _ = ∑ S ∈ fiber, sign S * C S J := by
          apply Finset.sum_congr rfl
          intro S hS
          rw [(Finset.mem_filter.mp hS).2]
        _ = ∑' c, ∑ S ∈ fiber, sign S * ∫ v, k S c v ∂m := by
          change (∑ S ∈ fiber, sign S * ∑' c, ∫ v, k S c v ∂m) = _
          simp_rw [← tsum_mul_left]
          exact (Summable.tsum_finsetSum (fun S hS => (hdata S hS).2.mul_left (sign S))).symm
        _ = 0 := by
          suffices h : ∀ c : BruhatOuterCosets Q (R J),
              (∑ S ∈ fiber, sign S * (∫ v, k S c v ∂m)) = 0 from
            (tsum_congr h).trans tsum_zero
          intro c
          simp_rw [← integral_const_mul]
          rw [← integral_finsetSum fiber (fun S hS => ((hdata S hS).1 c).const_mul (sign S))]
          have hp (v : Y) : 0 < pair T ξ (H (bruhatEvaluation (G₁ c) v) - Tp) := by
            have hn₀ : (v.out : AdelicSubgroupPoints.adelicPoints F G
                (SubgroupFunctor.range (r (roots (R J))))).val ∈ N₀ :=
              unipotentRange_le hG hi hν (Set.empty_subset _) (rootSet_subset i ν (R J)) _ v.out.2
            exact hpositive c.out ⟨_, hn₀⟩
          have hk : (fun v => ∑ S ∈ fiber, sign S * k S c v) = 0 := by
            funext v
            let z := bruhatEvaluation (J := J) (R := R J) (w := wA) (G₁ c) v
            let weight (a : B) := ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a.val (H z - Tp)
            let d := constantTerm F i ν (roots J) φ z
            let payload (S : Finset B) := if S ∩ neutral = J then d else 0
            have hp' : 0 < ∑ a : B, coeff a * weight a := by
              have hx := fullAction_mem_rootSpan w⁻¹ (isRealFundamentalWeight hG hi hν D β).1
              rw [← pair_rootSpan_eq_sum_fullWeights hG hi hν D hx]
              exact hp v
            have hAlt := Langlands.ArthurCombinatorics.alternatingCutoff_eq_zero (Finset.univ : Finset B)
              free neutral (Finset.subset_univ _) (Finset.subset_univ _) hDisjoint coeff weight payload
              hCoeff₁ hCoeff₂ hCoeff₃ (by
                intro S _
                simp only [payload, Finset.inter_assoc, Finset.inter_self]) hp'
            rw [hAllowed] at hAlt
            change (∑ S ∈ fiber, sign S * k S c v) = 0
            refine Eq.trans ?_ hAlt
            unfold fiber
            rw [Finset.sum_filter]
            apply Finset.sum_congr rfl
            intro S _
            by_cases hS : S ∩ neutral = J
            · simp only [hS, ↓reduceIte, k, bruhatCutoffIntegrand, payload, sign]
              rw [tauHat_eq_ite hG hi D]
              change _ * (d * (if ∀ a ∈ (Finset.univ : Finset B) \ S, 0 < weight a then 1 else 0)) = _
              split <;> simp_all
            · simp [hS, payload]
          rw [hk]
          simp

end Langlands.Global.ArthurTruncation.Idempotence
