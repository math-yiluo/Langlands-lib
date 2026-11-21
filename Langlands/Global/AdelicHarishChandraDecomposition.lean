import Langlands.Global.AdelicLocalFinitenessProductBridge
import Langlands.Global.AdelicLeviConstantTermPairing
import Langlands.Global.AdelicConstantTermComposition
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Harish-Chandra decomposition by constant terms

For a compatible standard parabolic family and a continuous left `G(F)`-invariant `f`, define
`f_P = Σ_{S ⊆ P} (−1)^{|P ∖ S|} C_S f` for finite sets `P` of simple roots. Then
`f = Σ_{P ⊆ Δ₀} f_P` (Möbius inversion, using `C_G = id`), and `f_P` is cuspidal along `P`
(pairing `S ↔ S ∪ {α}` for `α ∈ P ∖ Q`, using `C_Q C_S = C_{Q ∩ S}`). -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.HarishChandraDecomposition

section Combinatorics

variable {α : Type v} [DecidableEq α] {M : Type w} [AddCommGroup M] [Module ℂ M]

/-- The alternating sum `Σ_{S ⊆ P} (−1)^{|P ∖ S|} c(S)`. -/
def alternatingSum (c : Finset α → M) (P : Finset α) : M :=
  ∑ S ∈ P.powerset, ((-1 : ℂ) ^ (P \ S).card) • c S

theorem alternatingSum_insert {a : α} {P : Finset α} (ha : a ∉ P) (c : Finset α → M) :
    alternatingSum c (insert a P) =
      alternatingSum (fun S => c (insert a S)) P - alternatingSum c P := by
  unfold alternatingSum
  rw [Finset.sum_powerset_insert ha, sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  · refine Finset.sum_congr rfl fun S hS => ?_
    have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
    rw [Finset.insert_sdiff_insert, Finset.sdiff_insert_of_notMem ha]
  · refine Finset.sum_congr rfl fun S hS => ?_
    have haS : a ∉ S := fun h => ha (Finset.mem_powerset.mp hS h)
    rw [Finset.insert_sdiff_of_notMem _ haS, Finset.card_insert_of_notMem
      (fun h => ha (Finset.mem_sdiff.mp h).1), pow_succ, mul_neg_one, neg_smul]

/-- **Möbius inversion.** `Σ_{P ⊆ D} Σ_{S ⊆ P} (−1)^{|P ∖ S|} c(S) = c(D)`. -/
theorem sum_alternatingSum (D : Finset α) (c : Finset α → M) :
    ∑ P ∈ D.powerset, alternatingSum c P = c D := by
  induction D using Finset.induction_on generalizing c with
  | empty => simp [alternatingSum]
  | insert a D ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have h : ∀ P ∈ D.powerset, alternatingSum c (insert a P) =
        alternatingSum (fun S => c (insert a S)) P - alternatingSum c P := fun P hP =>
      alternatingSum_insert (fun h => ha (Finset.mem_powerset.mp hP h)) c
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, ih (fun S => c (insert a S))]
    abel

/-- **Cancellation.** If `a ∈ P` and `c(insert a S) = c(S)` for `S ⊆ P ∖ {a}`, the alternating sum
vanishes. -/
theorem alternatingSum_eq_zero {a : α} {P : Finset α} (haP : a ∈ P) (c : Finset α → M)
    (hc : ∀ S ⊆ P.erase a, c (insert a S) = c S) : alternatingSum c P = 0 := by
  rw [← Finset.insert_erase haP, alternatingSum_insert (Finset.notMem_erase a P)]
  rw [sub_eq_zero]
  unfold alternatingSum
  exact Finset.sum_congr rfl fun S hS => by
    simp only
    rw [hc S (Finset.mem_powerset.mp hS)]

end Combinatorics

end Langlands.Global.HarishChandraDecomposition

namespace Langlands.Global.StandardParabolicFamily

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Global.AdelicSubgroupPoints Langlands.Global.ConstantTermComposition
open Langlands.Global.HarishChandraDecomposition
open Classical

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "rad(" J ")" => SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J)

/-- `Δ₀` is finite. -/
theorem finite_simpleRoots : (simpleRelativeRoots 𝓕.i 𝓕.ν).Finite :=
  𝓕.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots 𝓕.i 𝓕.ν

/-- `Δ₀` as a finset. -/
def simpleRootFinset : Finset (characterLattice 𝓕.T) := 𝓕.finite_simpleRoots.toFinset

/-- The standard index of a finset of characters, intersected with `Δ₀`. -/
def finsetIndex (S : Finset (characterLattice 𝓕.T)) : Idx :=
  ⟨↑S ∩ simpleRelativeRoots 𝓕.i 𝓕.ν, Set.inter_subset_right⟩

theorem finsetIndex_simpleRootFinset : 𝓕.finsetIndex 𝓕.simpleRootFinset = 𝓕.top := by
  apply Subtype.ext
  change (↑𝓕.finite_simpleRoots.toFinset : Set (characterLattice 𝓕.T)) ∩
    simpleRelativeRoots 𝓕.i 𝓕.ν = simpleRelativeRoots 𝓕.i 𝓕.ν
  rw [Set.Finite.coe_toFinset, Set.inter_self]

/-- The Harish-Chandra component `φ_P = Σ_{S ⊆ P} (−1)^{|P ∖ S|} C_S φ` for a finset `P`. -/
def hcComponent (P : Finset (characterLattice 𝓕.T)) (φ : AdelicGroupPoints F G → ℂ) :
    AdelicGroupPoints F G → ℂ :=
  alternatingSum (fun S => 𝓕.constantTerm (𝓕.finsetIndex S) φ) P

/-- **Möbius inversion.** `φ = Σ_{P ⊆ Δ₀} φ_P`. -/
theorem sum_hcComponent (φ : AdelicGroupPoints F G → ℂ) :
    ∑ P ∈ 𝓕.simpleRootFinset.powerset, 𝓕.hcComponent P φ = φ := by
  unfold hcComponent
  rw [sum_alternatingSum, finsetIndex_simpleRootFinset, constantTerm_top]

/-- `C_Q f` is invariant under the rational points of every standard radical `U_R`. -/
theorem isRationalInvariant_constantTerm (R Q : Idx) (f : ContinuousRationalFunctions F G) :
    IsRationalInvariant F G rad(R) (𝓕.constantTerm Q (evaluate F G f)) := by
  let : IsClosed (adelicPoints F G rad(Q) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  have hφ : 𝓕.constantTerm Q (evaluate F G f) = normalizedConstantTerm F G rad(Q) f :=
    funext fun x => (normalizedConstantTerm_range_eq_subgroupConstantTerm F G
      (𝓕.iU Q ≫ 𝓕.p Q) f x).symm
  have hRI : rad(R) ≤ rad(𝓕.interIndex R Q) := 𝓕.radical_le_of_le (𝓕.interIndex_le_left R Q)
  have hQnI : rad(Q).IsNormalizedBy rad(𝓕.interIndex R Q) :=
    𝓕.radical_isNormalizedBy_of_le (𝓕.interIndex_le_right R Q)
  rintro _ ⟨q, rfl⟩ x
  rw [hφ]
  exact normalizedConstantTerm_rationalNormalizer_mul F G rad(Q) hQnI ⟨q.val, hRI _ q.2⟩ f x

/-- Integrability of the constant-term integrand of a continuous `U(F)`-invariant function. -/
theorem integrable_out_of_isRationalInvariant {U : SubgroupFunctor G}
    [IsClosed (adelicPoints F G U : Set (AdelicGroupPoints F G))]
    [CompactSpace (RationalQuotient F G U)] {φ : AdelicGroupPoints F G → ℂ}
    (hφ : Continuous φ) (hinv : IsRationalInvariant F G U φ) (g : AdelicGroupPoints F G) :
    letI := rationalQuotientBorelSpace F G U
    Integrable (fun x : RationalQuotient F G U =>
      φ (((Quotient.out x : adelicPoints F G U) : AdelicGroupPoints F G) * g))
      (normalizedRationalQuotientHaarMeasure F G U) := by
  let := rationalQuotientBorelSpace F G U
  let : IsProbabilityMeasure (normalizedRationalQuotientHaarMeasure F G U) :=
    normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  have heq : (fun x : RationalQuotient F G U =>
      φ (((Quotient.out x : adelicPoints F G U) : AdelicGroupPoints F G) * g)) =
      descendedIntegrand hinv g := funext fun x => (descendedIntegrand_out hinv g x).symm
  rw [heq]
  exact (continuous_descendedIntegrand hinv hφ g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The constant term along `Q` of a component is the alternating sum of the constant terms
along `Q ∩ S`. -/
theorem constantTerm_hcComponent (Q : Idx) (P : Finset (characterLattice 𝓕.T))
    (f : ContinuousRationalFunctions F G) :
    𝓕.constantTerm Q (𝓕.hcComponent P (evaluate F G f)) =
      alternatingSum (fun S => 𝓕.constantTerm (𝓕.interIndex Q (𝓕.finsetIndex S))
        (evaluate F G f)) P := by
  let : IsClosed (adelicPoints F G rad(Q) : Set (AdelicGroupPoints F G)) :=
    isClosed_adelicPoints_range F G (𝓕.iU Q ≫ 𝓕.p Q)
  let := 𝓕.compactSpace_radicalRationalQuotient Q
  let := rationalQuotientBorelSpace F G rad(Q)
  have hint : ∀ S g, Integrable (fun x : RationalQuotient F G rad(Q) =>
      𝓕.constantTerm (𝓕.finsetIndex S) (evaluate F G f)
        (((Quotient.out x : adelicPoints F G rad(Q)) : AdelicGroupPoints F G) * g))
      (normalizedRationalQuotientHaarMeasure F G rad(Q)) := fun S g =>
    integrable_out_of_isRationalInvariant (𝓕.continuous_constantTerm _ f)
      (𝓕.isRationalInvariant_constantTerm Q _ f) g
  unfold hcComponent alternatingSum
  simp_rw [← 𝓕.constantTerm_constantTerm Q _ f]
  funext g
  change (∫ x, (∑ S ∈ P.powerset, ((-1 : ℂ) ^ (P \ S).card) •
      𝓕.constantTerm (𝓕.finsetIndex S) (evaluate F G f))
        (((Quotient.out x : adelicPoints F G rad(Q)) : AdelicGroupPoints F G) * g)
      ∂normalizedRationalQuotientHaarMeasure F G rad(Q)) = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_finsetSum _ (fun S _ => (hint S g).const_mul _)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [integral_const_mul]
  rfl

/-- **Cuspidality of the components.** For every finset `P`, the component `f_P` of a continuous
`G(F)`-invariant `f` is cuspidal along `P`: its constant terms along all `Q ⊊ P` vanish. -/
theorem isCuspidalAlong_hcComponent (P : Finset (characterLattice 𝓕.T))
    (f : ContinuousRationalFunctions F G) :
    𝓕.IsCuspidalAlong (𝓕.finsetIndex P) (𝓕.hcComponent P (evaluate F G f)) := by
  intro Q hQ
  rw [𝓕.constantTerm_hcComponent]
  obtain ⟨a, haP, haQ⟩ := Set.exists_of_ssubset hQ
  refine alternatingSum_eq_zero (Finset.mem_coe.mp haP.1) _ fun S _ => ?_
  congr 1
  apply Subtype.ext
  ext x
  change x ∈ Q.1 ∩ (↑(insert a S) ∩ simpleRelativeRoots 𝓕.i 𝓕.ν) ↔
    x ∈ Q.1 ∩ (↑S ∩ simpleRelativeRoots 𝓕.i 𝓕.ν)
  simp only [Set.mem_inter_iff, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
  constructor
  · rintro ⟨hxQ, hxS | hxS, hxΔ⟩
    · exact absurd (hxS ▸ hxQ) haQ
    · exact ⟨hxQ, hxS, hxΔ⟩
  · rintro ⟨hxQ, hxS, hxΔ⟩
    exact ⟨hxQ, Or.inr hxS, hxΔ⟩

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

/-- **Statement form.** For a compatible standard parabolic family and a continuous left
`G(F)`-invariant `f`, the components `f_P = Σ_{S ⊆ P} (−1)^{|P ∖ S|} C_S f` (`P ⊆ Δ₀`) sum to `f`,
and each `f_P` is cuspidal along `P`. -/
def HarishChandraDecompositionStatement : Prop :=
  ∀ {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (𝓕 : StandardParabolicFamily F G) (f : ContinuousRationalFunctions F G),
    (∑ P ∈ 𝓕.simpleRootFinset.powerset, 𝓕.hcComponent P (evaluate F G f)) = evaluate F G f ∧
      ∀ P : Finset (characterLattice 𝓕.T),
        𝓕.IsCuspidalAlong (𝓕.finsetIndex P) (𝓕.hcComponent P (evaluate F G f))

/-- Proof of `HarishChandraDecompositionStatement`. -/
theorem harishChandraDecomposition : HarishChandraDecompositionStatement.{u} :=
  fun 𝓕 f => ⟨𝓕.sum_hcComponent _, fun P => 𝓕.isCuspidalAlong_hcComponent P f⟩

end Langlands.Global
