import Langlands.Representation.Aubert.GradedDerivative
import Langlands.Representation.Aubert.MultisegmentRankOrder
import Langlands.Representation.Aubert.SegmentPolynomialInjectivity
import Langlands.Representation.Aubert.SegmentProductClass
import Langlands.Representation.Aubert.SupportGrading
import Langlands.Representation.Aubert.ZelevinskyHighestDerivative
import Langlands.Representation.Aubert.ZelevinskyPolynomial
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof
import Langlands.Representation.Smooth.ConstituentSupport
import Langlands.Representation.Classification.SegmentProductCuspidalEmbedding
import Langlands.Representation.Classification.SegmentSocleProductComparison
import Langlands.Representation.Classification.SegmentZelevinskyConstituentExistenceProof
import Langlands.Representation.Classification.MultisegmentClassificationStatement
import Langlands.Representation.Classification.SegmentHeadSupportGeneric
import Langlands.Representation.Classification.SegmentSocleProductHomogeneityProof
import Langlands.Representation.Filtration.ExactFunctorIrreducibility

/-!
# Surjectivity of the segment-polynomial evaluation

Surjectivity of `segmentPolynomialEvaluation` and the comparison of Ze80 Corollary 7.5,
conditional on multisegment socle exhaustion (Ze80 Theorem 6.1 (c)). Triangularity
(Ze80 Theorem 7.1) is proved for the rank order `Multisegment.RankLE` and weak labels,
using the total derivative and the highest-derivative label step (a weak form of
Ze80 6.6, proved from Ze80 Theorem 6.2).
-/

noncomputable section

open CategoryTheory
open scoped BigOperators

namespace Langlands.Aubert

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

namespace SegmentPolynomialSurjectivity

open SmoothRep SmoothRep.IrreducibleGrothendieckProof VirtualRepresentation PadicField.TopologicalData

/-! ### Coefficients of graded classes -/

/-- Irreducible labels of the actual `GL_m(F)`, for the topology carried by `T`. -/
abbrev Label (m : ℕ) : Type _ :=
  letI := T.topology
  GeneralLinear.IrreducibleIsoClass.{uV, uF} m F.Carrier

/-- The class of the irreducible label `c` of `GL_m`, placed in rank `m`. -/
def basisClass (m : ℕ) (c : Label.{uF, uV} F T m) :
    GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  gradedInclusion F T m (GeneralLinear.realizeIrreducibles m F.Carrier (generator c))

theorem basisClass_irreducibleIsoClass (m : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) (hA : A.IsIrreducible),
      basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier A hA) =
        gradedInclusion F T m (GeneralLinear.finiteLengthClass m F.Carrier A
          (hasFiniteLength_of_isIrreducible hA)) := by
  let := T.topology
  intro A hA
  exact congrArg (gradedInclusion F T m)
    (GeneralLinear.realizeIrreducibles_generator_irreducibleIsoClass m F.Carrier A hA
      (hasFiniteLength_of_isIrreducible hA))

/-- The coefficient of the irreducible label `c` of `GL_m` in a graded class. -/
def coeff (m : ℕ) (c : Label.{uF, uV} F T m) :
    GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ :=
  letI := T.topology
  (Finsupp.lapply c).comp (factorMap.comp (DirectSum.component ℤ ℕ
    (fun k => GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} k F.Carrier) m))

theorem coeff_apply (m : ℕ) (c : Label.{uF, uV} F T m)
    (x : GradedGrothendieckGroup.{uF, uV} F T) :
    letI := T.topology
    coeff F T m c x = factorMap (x m) c := rfl

theorem gradedInclusion_apply_self (m : ℕ) :
    letI := T.topology
    ∀ y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} m F.Carrier,
      (gradedInclusion F T m y) m = y := by
  let := T.topology
  intro y
  exact DirectSum.of_eq_same _ _

theorem gradedInclusion_apply_of_ne {m n : ℕ} (h : n ≠ m) :
    letI := T.topology
    ∀ y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} m F.Carrier,
      (gradedInclusion F T m y) n = 0 := by
  let := T.topology
  intro y
  exact DirectSum.of_eq_of_ne _ _ _ h

open Classical in
/-- Every integer-valued linear functional is the sum of its values on the irreducible
basis classes, weighted by the coefficients. -/
theorem apply_eq_sum (χ : GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ)
    (x : GradedGrothendieckGroup.{uF, uV} F T) :
    letI := T.topology
    χ x = ∑ m ∈ x.support, (factorMap (x m)).sum fun c z => z * χ (basisClass F T m c) := by
  classical
  let := T.topology
  conv_lhs => rw [← DirectSum.sum_support_of x]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  let L : GeneralLinear.IrreducibleLattice.{uV, uF} m F.Carrier →ₗ[ℤ] ℤ :=
    χ.comp ((gradedInclusion F T m).comp (GeneralLinear.realizeIrreducibles m F.Carrier))
  have hL : L = Finsupp.linearCombination ℤ fun c => L (generator c) := by
    refine Finsupp.lhom_ext fun c z => ?_
    rw [Finsupp.linearCombination_single]
    have hz : Finsupp.single c z = z • generator c := by simp [generator]
    rw [hz, map_zsmul]
  have hx : x m = GeneralLinear.realizeIrreducibles m F.Carrier (factorMap (x m)) :=
    (LinearMap.congr_fun realize_comp_factorMap (x m)).symm
  have h1 : χ (DirectSum.of _ m (x m)) = L (factorMap (x m)) := by
    change χ (gradedInclusion F T m (x m)) = _
    conv_lhs => rw [hx]
    rfl
  rw [h1, hL, Finsupp.linearCombination_apply]
  rfl

/-- A graded class is effective when all its coefficients are nonnegative. -/
def IsEffective (x : GradedGrothendieckGroup.{uF, uV} F T) : Prop :=
  ∀ m c, 0 ≤ coeff F T m c x

theorem isEffective_zero : IsEffective F T 0 := fun m c => by simp

theorem IsEffective.add {x y : GradedGrothendieckGroup.{uF, uV} F T} (hx : IsEffective F T x)
    (hy : IsEffective F T y) : IsEffective F T (x + y) := fun m c => by
  rw [map_add]
  exact add_nonneg (hx m c) (hy m c)

theorem isEffective_sum {ι : Type*} (s : Finset ι) (f : ι → GradedGrothendieckGroup.{uF, uV} F T)
    (hf : ∀ i ∈ s, IsEffective F T (f i)) : IsEffective F T (∑ i ∈ s, f i) := fun m c => by
  rw [map_sum]
  exact Finset.sum_nonneg fun i hi => hf i hi m c

theorem coeff_gradedInclusion_of_ne {m n : ℕ} (h : n ≠ m)
    (c : Label.{uF, uV} F T n) :
    letI := T.topology
    ∀ y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} m F.Carrier,
      coeff F T n c (gradedInclusion F T m y) = 0 := by
  let := T.topology
  intro y
  rw [coeff_apply, gradedInclusion_apply_of_ne F T h, map_zero, Finsupp.zero_apply]

theorem coeff_gradedInclusion_ofRepresentation (m : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) (hA : A.HasFiniteLength)
      (τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) (hτ : τ.IsIrreducible),
      coeff F T m (GeneralLinear.irreducibleIsoClass m F.Carrier τ hτ)
          (gradedInclusion F T m (GeneralLinear.finiteLengthClass m F.Carrier A hA)) =
        (compositionMultiplicity ⟨A, hA⟩ τ : ℤ) := by
  let := T.topology
  intro A hA τ hτ
  rw [coeff_apply, gradedInclusion_apply_self, GeneralLinear.finiteLengthClass,
    factorMap_ofRepresentation]
  exact compositionFactors_apply _ τ hτ

theorem isEffective_gradedInclusion_ofRepresentation (m : ℕ) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) (hA : A.HasFiniteLength),
      IsEffective F T (gradedInclusion F T m (GeneralLinear.finiteLengthClass m F.Carrier A hA)) := by
  let := T.topology
  intro A hA n c
  by_cases h : n = m
  · subst h
    obtain ⟨τ, hτ, rfl⟩ := IrreducibleIsoClass.exists_eq c
    rw [coeff_gradedInclusion_ofRepresentation F T n A hA τ hτ]
    exact Int.natCast_nonneg _
  · rw [coeff_gradedInclusion_of_ne F T h]

/-- Comparison of two functionals on effective classes from their basis values. -/
theorem le_of_isEffective {φ χ : GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ}
    (h : ∀ m c, φ (basisClass F T m c) ≤ χ (basisClass F T m c))
    {x : GradedGrothendieckGroup.{uF, uV} F T} (hx : IsEffective F T x) : φ x ≤ χ x := by
  rw [apply_eq_sum F T φ, apply_eq_sum F T χ]
  refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun c _ => ?_
  exact mul_le_mul_of_nonneg_left (h m c) (hx m c)

theorem nonneg_of_isEffective {χ : GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ}
    (h : ∀ m c, 0 ≤ χ (basisClass F T m c))
    {x : GradedGrothendieckGroup.{uF, uV} F T} (hx : IsEffective F T x) : 0 ≤ χ x :=
  le_of_isEffective F T (φ := 0) (fun m c => h m c) hx

/-- A functional nonnegative on basis classes dominates each single weighted coefficient
of an effective class. -/
theorem coeff_mul_le_of_isEffective {χ : GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ}
    (h : ∀ m c, 0 ≤ χ (basisClass F T m c))
    {x : GradedGrothendieckGroup.{uF, uV} F T} (hx : IsEffective F T x) (n : ℕ)
    (c : Label.{uF, uV} F T n) :
    coeff F T n c x * χ (basisClass F T n c) ≤ χ x := by
  classical
  let := T.topology
  have hterm : ∀ m c, 0 ≤ coeff F T m c x * χ (basisClass F T m c) :=
    fun m c => mul_nonneg (hx m c) (h m c)
  rw [apply_eq_sum F T χ x]
  by_cases hn : n ∈ x.support
  · refine le_trans ?_ (Finset.single_le_sum (f := fun m =>
      (factorMap (x m)).sum fun c z => z * χ (basisClass F T m c))
      (fun m _ => Finset.sum_nonneg fun c _ => hterm m c) hn)
    by_cases hc : c ∈ (factorMap (x n)).support
    · exact Finset.single_le_sum (f := fun c => factorMap (x n) c * χ (basisClass F T n c))
        (fun c _ => hterm n c) hc
    · rw [coeff_apply, Finsupp.notMem_support_iff.mp hc, zero_mul]
      exact Finset.sum_nonneg fun c _ => hterm n c
  · rw [coeff_apply, DFinsupp.notMem_support_iff.mp hn, map_zero, Finsupp.zero_apply, zero_mul]
    exact Finset.sum_nonneg fun m _ => Finset.sum_nonneg fun c _ => hterm m c

/-! ### Weighted counts -/

/-- The weighted count `∑ w(c) · coeff_c` of a family of weights on irreducible labels. -/
def weightedCount (w : ∀ m, Label.{uF, uV} F T m → ℤ) :
    GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ :=
  letI := T.topology
  DirectSum.toModule ℤ ℕ ℤ fun m => (Finsupp.linearCombination ℤ (w m)).comp factorMap

theorem weightedCount_gradedInclusion
    (w : ∀ m, Label.{uF, uV} F T m → ℤ) (m : ℕ) :
    letI := T.topology
    ∀ y : GeneralLinear.FiniteLengthGrothendieckGroup.{uV, uF} m F.Carrier,
      weightedCount F T w (gradedInclusion F T m y) = (factorMap y).sum fun c z => z * w m c := by
  let := T.topology
  intro y
  rw [weightedCount, gradedInclusion, DirectSum.toModule_lof, LinearMap.comp_apply,
    Finsupp.linearCombination_apply]
  rfl

theorem weightedCount_basisClass
    (w : ∀ m, Label.{uF, uV} F T m → ℤ) (m : ℕ)
    (c : Label.{uF, uV} F T m) :
    weightedCount F T w (basisClass F T m c) = w m c := by
  let := T.topology
  rw [basisClass, weightedCount_gradedInclusion]
  have : factorMap (GeneralLinear.realizeIrreducibles m F.Carrier (generator c)) = generator c :=
    LinearMap.congr_fun factorMap_comp_realize (generator c)
  rw [this, generator, Finsupp.sum_single_index (by simp), one_mul]

theorem weightedCount_nonneg
    {w : ∀ m, Label.{uF, uV} F T m → ℤ}
    (hw : ∀ m c, 0 ≤ w m c) {x : GradedGrothendieckGroup.{uF, uV} F T}
    (hx : IsEffective F T x) : 0 ≤ weightedCount F T w x :=
  nonneg_of_isEffective F T (fun m c => by rw [weightedCount_basisClass]; exact hw m c) hx

/-- On an effective class, a nonnegative weighted count dominates each weighted coefficient. -/
theorem coeff_mul_le_weightedCount
    {w : ∀ m, Label.{uF, uV} F T m → ℤ}
    (hw : ∀ m c, 0 ≤ w m c) {x : GradedGrothendieckGroup.{uF, uV} F T}
    (hx : IsEffective F T x) (n : ℕ) (c : Label.{uF, uV} F T n) :
    coeff F T n c x * w n c ≤ weightedCount F T w x := by
  have := coeff_mul_le_of_isEffective F T (χ := weightedCount F T w)
    (fun m c => by rw [weightedCount_basisClass]; exact hw m c) hx n c
  rwa [weightedCount_basisClass] at this

/-! ### Basis classes and positivity -/

theorem coeff_basisClass_self (m : ℕ) (c : Label.{uF, uV} F T m) :
    coeff F T m c (basisClass F T m c) = 1 := by
  let := T.topology
  have h : factorMap (GeneralLinear.realizeIrreducibles m F.Carrier (generator c)) = generator c :=
    LinearMap.congr_fun factorMap_comp_realize (generator c)
  rw [coeff_apply, basisClass, gradedInclusion_apply_self, h, generator, Finsupp.single_eq_same]

theorem coeff_basisClass_of_ne (m : ℕ) {c c' : Label.{uF, uV} F T m} (hc : c ≠ c') :
    coeff F T m c' (basisClass F T m c) = 0 := by
  let := T.topology
  have h : factorMap (GeneralLinear.realizeIrreducibles m F.Carrier (generator c)) = generator c :=
    LinearMap.congr_fun factorMap_comp_realize (generator c)
  rw [coeff_apply, basisClass, gradedInclusion_apply_self, h, generator]
  simp [hc]

theorem isEffective_basisClass (m : ℕ) (c : Label.{uF, uV} F T m) :
    IsEffective F T (basisClass F T m c) := by
  let := T.topology
  obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
  rw [basisClass_irreducibleIsoClass]
  exact isEffective_gradedInclusion_ofRepresentation F T m A _

/-- Removing one basis class from an effective class containing it keeps it effective. -/
theorem isEffective_sub_basisClass {x : GradedGrothendieckGroup.{uF, uV} F T}
    (hx : IsEffective F T x) {m : ℕ} {c : Label.{uF, uV} F T m} (hc : 1 ≤ coeff F T m c x) :
    IsEffective F T (x - basisClass F T m c) := by
  intro m' c'
  rw [map_sub, sub_nonneg]
  by_cases hm : m' = m
  · subst hm
    by_cases h : c = c'
    · subst h
      rw [coeff_basisClass_self]
      exact hc
    · rw [coeff_basisClass_of_ne F T m' h]
      exact hx _ _
  · rw [basisClass, coeff_gradedInclusion_of_ne F T hm]
    exact hx _ _

open Classical in
/-- Every graded class is the finite sum of its coefficients times the basis classes. -/
theorem eq_sum_basisClass (x : GradedGrothendieckGroup.{uF, uV} F T) :
    letI := T.topology
    x = ∑ m ∈ x.support, (factorMap (x m)).sum fun c z => z • basisClass F T m c := by
  classical
  let := T.topology
  conv_lhs => rw [← DirectSum.sum_support_of x]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hx : x m = GeneralLinear.realizeIrreducibles m F.Carrier (factorMap (x m)) :=
    (LinearMap.congr_fun realize_comp_factorMap (x m)).symm
  change gradedInclusion F T m (x m) = _
  conv_lhs => rw [hx, ← Finsupp.sum_single (factorMap (x m))]
  rw [map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr fun c _ => ?_
  have hz : Finsupp.single c (factorMap (x m) c) = factorMap (x m) c • generator c := by
    simp [generator]
  rw [hz, map_zsmul, map_zsmul]
  rfl

/-- An additive subgroup containing every basis class with a nonzero coefficient in `x`
contains `x`. -/
theorem mem_of_coeff {S : AddSubgroup (GradedGrothendieckGroup.{uF, uV} F T)}
    {x : GradedGrothendieckGroup.{uF, uV} F T}
    (h : ∀ m c, coeff F T m c x ≠ 0 → basisClass F T m c ∈ S) : x ∈ S := by
  classical
  let := T.topology
  rw [eq_sum_basisClass F T x]
  exact S.sum_mem fun m _ => S.sum_mem fun c hc =>
    S.zsmul_mem (h m c (Finsupp.mem_support_iff.mp hc)) _

open Classical in
/-- A functional positive on an effective class is positive on one of its constituents. -/
theorem exists_coeff_pos_of_pos {χ : GradedGrothendieckGroup.{uF, uV} F T →ₗ[ℤ] ℤ}
    {x : GradedGrothendieckGroup.{uF, uV} F T} (hx : IsEffective F T x) (h : 0 < χ x) :
    ∃ m c, 0 < coeff F T m c x ∧ 0 < χ (basisClass F T m c) := by
  by_contra hcon
  push Not at hcon
  refine absurd h (not_lt.mpr ?_)
  rw [apply_eq_sum F T χ x]
  refine Finset.sum_nonpos fun m _ => Finset.sum_nonpos fun c _ => ?_
  rcases (hx m c).lt_or_eq with hc | hc
  · exact mul_nonpos_of_nonneg_of_nonpos hc.le (hcon m c hc)
  · rw [coeff_apply] at hc
    dsimp only
    rw [← hc, zero_mul]

theorem weightedCount_eq_zero_of {w : ∀ m, Label.{uF, uV} F T m → ℤ}
    {x : GradedGrothendieckGroup.{uF, uV} F T} (h : ∀ m c, coeff F T m c x ≠ 0 → w m c = 0) :
    weightedCount F T w x = 0 := by
  classical
  rw [apply_eq_sum F T _ x]
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun c hc => ?_
  dsimp only
  rw [weightedCount_basisClass, h m c (Finsupp.mem_support_iff.mp hc), mul_zero]

theorem exists_mem_pos_of_sum_pos {ι : Type*} {s : Multiset ι} {f : ι → ℤ}
    (h : 0 < (s.map f).sum) : ∃ i ∈ s, 0 < f i := by
  by_contra hcon
  push Not at hcon
  refine absurd h (not_lt.mpr ?_)
  have := Multiset.sum_map_le_sum_map f (fun _ => (0 : ℤ)) hcon
  simpa using this

/-- A sum over the antidiagonal of `s` whose terms vanish unless the second part is empty
reduces to the term `(s, 0)`. -/
theorem sum_antidiagonal_eq_of_snd {α M : Type*} [AddCommMonoid M]
    (s : Multiset α) (f : Multiset α × Multiset α → M) (hf : ∀ q : Multiset α × Multiset α, q.2 ≠ 0 → f q = 0) :
    ((Multiset.antidiagonal s).map f).sum = f (s, 0) := by
  induction s using Multiset.induction_on generalizing f with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.antidiagonal_cons, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
      Multiset.map_map]
    have h1 : ((Multiset.antidiagonal s).map (f ∘ Prod.map id (Multiset.cons x))).sum = 0 :=
      Multiset.sum_eq_zero fun z hz => by
        obtain ⟨q, -, rfl⟩ := Multiset.mem_map.mp hz
        exact hf _ (Multiset.cons_ne_zero)
    rw [h1, zero_add, ih (f ∘ Prod.map (Multiset.cons x) id) fun q hq => hf _ hq]
    rfl

/-- The variant of `sum_antidiagonal_eq_of_snd` where the vanishing is only assumed on the
antidiagonal. -/
theorem sum_antidiagonal_eq_of_mem_snd {α M : Type*} [AddCommMonoid M]
    (s : Multiset α) (f : Multiset α × Multiset α → M)
    (hf : ∀ q ∈ Multiset.antidiagonal s, q.2 ≠ 0 → f q = 0) :
    ((Multiset.antidiagonal s).map f).sum = f (s, 0) := by
  classical
  have hs : (s, (0 : Multiset α)) ∈ Multiset.antidiagonal s :=
    Multiset.mem_antidiagonal.mpr (add_zero s)
  have h : (Multiset.antidiagonal s).map f =
      (Multiset.antidiagonal s).map fun q => if q ∈ Multiset.antidiagonal s then f q else 0 :=
    Multiset.map_congr rfl fun q hq => (ite_eq_left hq).symm
  rw [h, sum_antidiagonal_eq_of_snd s _ fun q hq => ?_, ite_eq_left hs]
  split_ifs with hmem
  · exact hf q hmem hq
  · rfl

/-! ### The total derivative on basis classes -/

section Derivative

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem isEffective_gradedDerivative_basisClass (m : ℕ) (c : Label.{uF, uV} F T m) :
    IsEffective F T (gradedDerivative F T ψ (basisClass F T m c)) := by
  let := T.topology
  obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
  rw [basisClass_irreducibleIsoClass, GeneralLinear.finiteLengthClass,
    gradedDerivative_ofRepresentation]
  exact isEffective_sum F T _ _ fun k _ => isEffective_gradedInclusion_ofRepresentation F T _ _ _

theorem isEffective_gradedDerivative {x : GradedGrothendieckGroup.{uF, uV} F T}
    (hx : IsEffective F T x) : IsEffective F T (gradedDerivative F T ψ x) := fun m c =>
  nonneg_of_isEffective F T (χ := (coeff F T m c).comp (gradedDerivative F T ψ))
    (fun m' c' => isEffective_gradedDerivative_basisClass F T ψ m' c' m c) hx

/-- On rank zero the total derivative is the identity. -/
theorem gradedDerivative_gradedInclusion_zero :
    letI := T.topology
    ∀ y, gradedDerivative F T ψ (gradedInclusion F T 0 y) = gradedInclusion F T 0 y := by
  let := T.topology
  intro y
  rw [gradedDerivative_homogeneous, Finset.sum_range_one, derivativeComponent_of_le F T ψ le_rfl,
    derivativeK0_zero]
  rfl

/-- An irreducible subquotient of the order-`k` derivative of an irreducible `A` occurs in the
total derivative of the class of `A`. -/
theorem coeff_gradedDerivative_pos (m k : ℕ) (hk : k ≤ m) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) (hA : A.IsIrreducible)
      (B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (m - k) F.Carrier)) (hB : B.IsIrreducible),
      SmoothRep.IsSubquotient B
          ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ m k hk).obj A) →
        0 < coeff F T (m - k) (GeneralLinear.irreducibleIsoClass (m - k) F.Carrier B hB)
          (gradedDerivative F T ψ
            (basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier A hA))) := by
  let := T.topology
  intro A hA B hB hsub
  have hAL := hasFiniteLength_of_isIrreducible hA
  have hfl := generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ m k hk A hAL
  have hpos : 0 < (compositionMultiplicity ⟨_, hfl⟩ B : ℤ) := by
    exact_mod_cast (compositionMultiplicity_pos_iff_isSubquotient ⟨_, hfl⟩ B hB).mpr hsub
  rw [← coeff_gradedInclusion_ofRepresentation F T (m - k) _ hfl B hB] at hpos
  have hsum : gradedDerivative F T ψ
      (basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier A hA)) =
      ∑ j : Fin (m + 1), gradedInclusion F T (m - j)
        (GeneralLinear.finiteLengthClass (m - j) F.Carrier
          ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ m j
            (Nat.lt_succ_iff.mp j.isLt)).obj A)
          (generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ m j
            (Nat.lt_succ_iff.mp j.isLt) A hAL)) := by
    rw [basisClass_irreducibleIsoClass, GeneralLinear.finiteLengthClass,
      gradedDerivative_ofRepresentation F T ψ m A hAL]
    rfl
  have hle : ∀ j : Fin (m + 1),
      coeff F T (m - k) (GeneralLinear.irreducibleIsoClass (m - k) F.Carrier B hB)
        (gradedInclusion F T (m - j)
          (GeneralLinear.finiteLengthClass (m - j) F.Carrier
            ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ m j
              (Nat.lt_succ_iff.mp j.isLt)).obj A)
            (generalLinearDerivative_preservesFiniteLength.{uF, uV} F T ψ m j
              (Nat.lt_succ_iff.mp j.isLt) A hAL))) ≤
      coeff F T (m - k) (GeneralLinear.irreducibleIsoClass (m - k) F.Carrier B hB)
        (gradedDerivative F T ψ
          (basisClass F T m (GeneralLinear.irreducibleIsoClass m F.Carrier A hA))) := by
    intro j
    rw [hsum, map_sum]
    exact Finset.single_le_sum (fun i _ => isEffective_gradedInclusion_ofRepresentation F T _ _ _ _ _)
      (Finset.mem_univ j)
  exact lt_of_lt_of_le hpos (hle ⟨k, Nat.lt_succ_of_le hk⟩)

end Derivative

/-! ### Products of segment socles -/

section Zeta

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)

/-- Zelevinsky's class `ζ(a) = ∏_{Δ ∈ a} ζ(Δ)` of a multisegment `a`: the value of the
segment-polynomial evaluation at the monomial of `a`. -/
def zeta (a : T.Multisegment.{max uF uV, uF}) : GradedGrothendieckGroup.{uF, uV} F T :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  segmentPolynomialEvaluation F T hx hl (a.map MvPolynomial.X).prod

theorem zeta_zero : zeta F T hx hl 0 = gradedUnit F T := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  rw [zeta, Multiset.map_zero, Multiset.prod_zero, map_one]
  rfl

theorem zeta_add (a b : T.Multisegment.{max uF uV, uF}) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    zeta F T hx hl (a + b) = zeta F T hx hl a * zeta F T hx hl b := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  rw [zeta, zeta, zeta, Multiset.map_add, Multiset.prod_add, map_mul]

theorem zeta_singleton (Δ : T.Segment.{max uF uV, uF}) :
    zeta F T hx hl {Δ} = gradedSegmentSocle F T Δ := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  rw [zeta, Multiset.map_singleton, Multiset.prod_singleton]
  exact MvPolynomial.eval₂Hom_X' _ _ _

theorem prod_map_zeta_singleton (a : T.Multisegment.{max uF uV, uF}) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    (a.map fun Δ => zeta F T hx hl {Δ}).prod = zeta F T hx hl a := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  rw [zeta, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun Δ _ => ?_
  rw [zeta_singleton]
  exact (MvPolynomial.eval₂Hom_X' _ _ _).symm

theorem zeta_dropLast_eq_prod (a : T.Multisegment.{max uF uV, uF}) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    zeta F T hx hl (Multisegment.dropLast a) =
      (a.map fun Δ => zeta F T hx hl (Multisegment.dropLast {Δ})).prod := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  induction a using Multiset.induction_on with
  | empty =>
    rw [Multisegment.dropLast_zero, Multiset.map_zero, Multiset.prod_zero, zeta,
      Multiset.map_zero, Multiset.prod_zero, map_one]
  | cons Δ a ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ← ih, ← zeta_add, ← Multisegment.dropLast_add,
      Multiset.singleton_add]

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- `D ζ(Δ) = ζ({Δ}⁻) + ζ(Δ)`, where `{Δ}⁻` is empty for a segment of length one. -/
theorem gradedDerivative_zeta_singleton (Δ : T.Segment.{max uF uV, uF}) :
    gradedDerivative F T ψ (zeta F T hx hl {Δ}) =
      zeta F T hx hl (Multisegment.dropLast {Δ}) + zeta F T hx hl {Δ} := by
  let := T.topology
  rw [zeta_singleton, ← Multiset.cons_zero]
  by_cases h : 1 < Δ.length
  · rw [Multisegment.dropLast_cons_of_one_lt Δ h, Multisegment.dropLast_zero, Multiset.cons_zero,
      zeta_singleton, gradedDerivative_segmentSocle_of_two_le F T ψ Δ h]
    exact add_comm _ _
  · have h1 : Δ.length = 1 := by have := Δ.length_pos; omega
    rw [Multisegment.dropLast_cons_of_length_eq_one Δ h1, Multisegment.dropLast_zero, zeta_zero,
      gradedDerivative_segmentSocle_of_length_eq_one F T ψ Δ h1]
    exact add_comm _ _

/-- **The derivative of a product of segment socles** (the K0 form of Zelevinsky's
Leibniz formula): `D ζ(a) = ∑_{a = a₁ + a₂} ζ(a₁⁻ + a₂)`. -/
theorem gradedDerivative_zeta (a : T.Multisegment.{max uF uV, uF}) :
    gradedDerivative F T ψ (zeta F T hx hl a) =
      ((Multiset.antidiagonal a).map fun q =>
        zeta F T hx hl (Multisegment.dropLast q.1 + q.2)).sum := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  calc gradedDerivative F T ψ (zeta F T hx hl a)
      = gradedDerivativeRingHom F T ψ hx hl (a.map fun Δ => zeta F T hx hl {Δ}).prod := by
        rw [prod_map_zeta_singleton, gradedDerivativeRingHom_apply]
    _ = (a.map fun Δ => zeta F T hx hl (Multisegment.dropLast {Δ}) + zeta F T hx hl {Δ}).prod := by
        rw [map_multiset_prod, Multiset.map_map]
        congr 1
        exact Multiset.map_congr rfl fun Δ _ => gradedDerivative_zeta_singleton F T hx hl ψ Δ
    _ = _ := by
        rw [Multiset.prod_map_add]
        congr 1
        refine Multiset.map_congr rfl fun q _ => ?_
        rw [← zeta_dropLast_eq_prod, prod_map_zeta_singleton, zeta_add]

/-- Every multisegment is the multisegment of a datum of supplied segment socles. -/
theorem exists_datum (a : T.Multisegment.{max uF uV, uF}) {n : ℕ} (hn : a.degree = n) :
    ∃ d : T.SegmentProductDatum.{max uF uV, uF} n, d.multisegment = a ∧ d.HasSegmentSocles := by
  obtain ⟨d, hd, hs⟩ := SegmentProductDatum.exists_of_list
    (Classification.segmentZelevinskyConstituentExistence.{uF, max uF uV} F T) a.toList
    (n := n) (by
      rw [← hn, Multisegment.degree, ← Multiset.sum_coe, ← Multiset.map_coe, Multiset.coe_toList])
  exact ⟨d, by rw [SegmentProductDatum.multisegment, hd, Multiset.coe_toList], hs⟩

/-- `ζ` of the multisegment of a datum of segment socles is the class of its product. -/
theorem zeta_multisegment {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hd : d.HasSegmentSocles) :
    letI := T.topology
    zeta F T hx hl d.multisegment = gradedInclusion F T n (GeneralLinear.finiteLengthClass n
      F.Carrier d.induced (SegmentProductClass.hasFiniteLength_induced F T d hd)) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  rw [gradedInclusion_induced_eq_segmentPolynomialEvaluation F T hx hl d hd, zeta]
  congr 1
  simp only [SegmentProductDatum.multisegment, Multiset.map_coe, Multiset.prod_coe, List.map_ofFn,
    List.prod_ofFn, Function.comp_apply]

theorem isEffective_zeta (a : T.Multisegment.{max uF uV, uF}) :
    IsEffective F T (zeta F T hx hl a) := by
  obtain ⟨d, hda, hd⟩ := exists_datum F T a rfl
  rw [← hda, zeta_multisegment F T hx hl d hd]
  exact isEffective_gradedInclusion_ofRepresentation F T _ _ _

theorem coeff_zeta_eq_zero_of_ne {a : T.Multisegment.{max uF uV, uF}} {m : ℕ} (h : m ≠ a.degree)
    (c : Label.{uF, uV} F T m) : coeff F T m c (zeta F T hx hl a) = 0 := by
  obtain ⟨d, hda, hd⟩ := exists_datum F T a rfl
  rw [← hda, zeta_multisegment F T hx hl d hd]
  exact coeff_gradedInclusion_of_ne F T h c _

theorem isSubquotient_of_coeff_zeta_pos {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hd : d.HasSegmentSocles) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.IsIrreducible),
      0 < coeff F T n (GeneralLinear.irreducibleIsoClass n F.Carrier A hA)
          (zeta F T hx hl d.multisegment) →
        SmoothRep.IsSubquotient A d.induced := by
  let := T.topology
  intro A hA h
  rw [zeta_multisegment F T hx hl d hd, coeff_gradedInclusion_ofRepresentation F T n _ _ A hA] at h
  exact (compositionMultiplicity_pos_iff_isSubquotient _ A hA).mp (by exact_mod_cast h)

end Zeta

/-! ### Supports of constituents -/

/-- Every irreducible subquotient of a product of segment socles has the cuspidal content
of the multisegment as supercuspidal support. -/
theorem classSupport_of_isSubquotient {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (hd : d.HasSegmentSocles) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)) (hA : A.IsIrreducible),
      SmoothRep.IsSubquotient A d.induced →
        SupportGrading.classSupport F T n (GeneralLinear.irreducibleIsoClass n F.Carrier A hA) =
          d.multisegment.cuspidalContent := by
  let := T.topology
  intro A hA hsub
  obtain ⟨k, ρ, h, B, hB, hρ, f, hf⟩ :=
    Classification.SegmentProductCuspidalEmbedding.embedsCuspidal_induced d hd
  rw [SupportGrading.classSupport_irreducibleIsoClass]
  exact SupportGrading.supercuspidalSupport_eq hA ⟨k, ρ, hρ, h, B, hB, hA,
    Classification.SegmentHeadSupport.isSubquotient_trans hsub
      (SmoothRep.IsSubrepresentation.isSubquotient ⟨f, hf⟩)⟩

theorem isSubquotient_of_isZelevinskySubrepresentation {n : ℕ}
    {d : T.SegmentProductDatum.{max uF uV, uF} n}
    {A : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (h : d.IsZelevinskySubrepresentation A) :
    letI := T.topology
    SmoothRep.IsSubquotient A d.induced := by
  let := T.topology
  obtain ⟨-, -, -, j, hj⟩ := h
  exact SmoothRep.IsSubrepresentation.isSubquotient ⟨SmoothRep.ofHom j, hj⟩

theorem classSupport_of_coeff_zeta_pos (hx : BinaryProductExactnessStatement.{uF, uV} F T)
    (hl : GradedInductionRingLawsStatement F T hx) {e : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (h : 0 < coeff F T m c (zeta F T hx hl e)) :
    SupportGrading.classSupport F T m c = e.cuspidalContent := by
  let := T.topology
  have hm : e.degree = m := by
    by_contra hne
    rw [coeff_zeta_eq_zero_of_ne F T hx hl (Ne.symm hne)] at h
    exact lt_irrefl 0 h
  obtain ⟨d, rfl, hd⟩ := exists_datum F T e hm
  obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
  exact classSupport_of_isSubquotient F T d hd A hA
    (isSubquotient_of_coeff_zeta_pos F T hx hl d hd A hA h)

/-! ### Multisegment bookkeeping -/

theorem degree_multisegment {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n) :
    d.multisegment.degree = n := by
  rw [Multisegment.degree, SegmentProductDatum.multisegment, Multiset.map_coe, Multiset.sum_coe]
  exact SegmentProductDatum.sum_map_degree_ofFn d

theorem eq_zero_of_degree_eq_zero {a : T.Multisegment.{max uF uV, uF}} (h : a.degree = 0) :
    a = 0 := by
  have h' : (a.map Segment.degree).sum = 0 := h
  refine Multiset.eq_zero_of_forall_notMem fun Δ hΔ => ?_
  have := (Multiset.sum_eq_zero_iff.mp h') Δ.degree (Multiset.mem_map_of_mem _ hΔ)
  exact Δ.degree_pos.ne' this

theorem sum_rank_pos {n : ℕ} (d : T.SegmentProductDatum.{max uF uV, uF} n) (hn : 0 < n) :
    0 < ∑ i, (d.segments i).rank := by
  have h := d.degree_sum
  rcases Nat.eq_zero_or_pos d.length with h0 | h0
  · exfalso
    have : IsEmpty (Fin d.length) := by rw [h0]; infer_instance
    rw [Finset.univ_eq_empty, Finset.sum_empty] at h
    omega
  · have : Nonempty (Fin d.length) := ⟨⟨0, h0⟩⟩
    exact Finset.sum_pos (fun i _ => (d.segments i).rank_pos) Finset.univ_nonempty

theorem degree_dropLast_lt {a : T.Multisegment.{max uF uV, uF}} (ha : a ≠ 0) :
    (Multisegment.dropLast a).degree < a.degree := by
  have key : ∀ a : T.Multisegment.{max uF uV, uF},
      (Multisegment.dropLast a).degree + (a.map Segment.rank).sum = a.degree := by
    intro a
    induction a using Multiset.induction_on with
    | empty => simp [Multisegment.degree]
    | cons Δ a ih =>
      have hΔ := Δ.dropLast_degree_add_rank
      by_cases h : 1 < Δ.length
      · rw [Multisegment.dropLast_cons_of_one_lt Δ h]
        rw [Δ.dropLast_of_one_lt h] at hΔ
        simp only [Multisegment.degree, Multiset.map_cons, Multiset.sum_cons, Option.map_some,
          Option.getD_some] at hΔ ih ⊢
        omega
      · have h1 : Δ.length = 1 := by have := Δ.length_pos; omega
        rw [Multisegment.dropLast_cons_of_length_eq_one Δ h1]
        rw [Δ.dropLast_of_length_eq_one h1] at hΔ
        simp only [Multisegment.degree, Multiset.map_cons, Multiset.sum_cons, Option.map_none,
          Option.getD_none] at hΔ ih ⊢
        omega
  obtain ⟨Δ, hΔ⟩ := Multiset.exists_mem_of_ne_zero ha
  have hr : Δ.rank ≤ (a.map Segment.rank).sum :=
    Multiset.le_sum_of_mem (Multiset.mem_map_of_mem _ hΔ)
  have := key a
  have := Δ.rank_pos
  omega

theorem card_cuspidalContent_dropLast (b : T.Multisegment.{max uF uV, uF}) :
    Multiset.card (Multisegment.dropLast b).cuspidalContent + Multiset.card b =
      Multiset.card b.cuspidalContent := by
  induction b using Multiset.induction_on with
  | empty => simp
  | cons Δ b ih =>
    by_cases h : 1 < Δ.length
    · rw [Multisegment.dropLast_cons_of_one_lt Δ h, Multisegment.cuspidalContent_cons,
        Multisegment.cuspidalContent_cons, Multiset.card_add, Multiset.card_add, Multiset.card_cons,
        Segment.card_cuspidalContent, Segment.card_cuspidalContent, Segment.dropLastNonempty_length]
      omega
    · have h1 : Δ.length = 1 := by have := Δ.length_pos; omega
      rw [Multisegment.dropLast_cons_of_length_eq_one Δ h1, Multisegment.cuspidalContent_cons,
        Multiset.card_add, Multiset.card_cons, Segment.card_cuspidalContent]
      omega

/-! ### Labels -/

section Labels

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The weak form of Zelevinsky's Proposition 6.6 used here: every irreducible
subrepresentation `π` of a precedence-ordered product of segment socles with multisegment
`a` of positive degree has, in its derivative of order `λ(a) = ∑ rank`, an irreducible
subquotient which is an irreducible subrepresentation of a precedence-ordered product of
segment socles with multisegment `a⁻`. -/
def HighestDerivativeLabelStep : Prop :=
  letI := T.topology
  ∀ (n : ℕ), 0 < n → ∀ (d : T.SegmentProductDatum.{max uF uV, uF} n)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)),
    d.IsZelevinskySubrepresentation π →
      ∃ (hk : ∑ i, (d.segments i).rank ≤ n)
        (d' : T.SegmentProductDatum.{max uF uV, uF} (n - ∑ i, (d.segments i).rank))
        (π' : SmoothRep.{0, uF, max uF uV} ℂ
          (GeneralLinear (n - ∑ i, (d.segments i).rank) F.Carrier)),
        d'.multisegment = Multisegment.dropLast d.multisegment ∧
          d'.IsZelevinskySubrepresentation π' ∧
          SmoothRep.IsSubquotient π'
            ((Derivative.generalLinearDerivative.{uF, max uF uV} T ψ n
              (∑ i, (d.segments i).rank) hk).obj π)

/-- `c` is a label of the multisegment `b`: some representative of `c` is an irreducible
subrepresentation of a precedence-ordered product of segment socles with multisegment `b`. -/
def IsLabel (b : T.Multisegment.{max uF uV, uF}) (m : ℕ) (c : Label.{uF, uV} F T m) : Prop :=
  letI := T.topology
  ∃ (A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear m F.Carrier)) (hA : A.IsIrreducible),
    GeneralLinear.irreducibleIsoClass m F.Carrier A hA = c ∧
      ∃ d : T.SegmentProductDatum.{max uF uV, uF} m,
        d.multisegment = b ∧ d.IsZelevinskySubrepresentation A

open Classical in
/-- The indicator weight of the labels of `b`. -/
def labelWeight (b : T.Multisegment.{max uF uV, uF}) (m : ℕ) (c : Label.{uF, uV} F T m) : ℤ :=
  if IsLabel F T b m c then 1 else 0

theorem labelWeight_of_isLabel {b : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (h : IsLabel F T b m c) : labelWeight F T b m c = 1 :=
  ite_eq_left h

theorem labelWeight_of_not_isLabel {b : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (h : ¬IsLabel F T b m c) : labelWeight F T b m c = 0 :=
  ite_eq_right h

theorem labelWeight_nonneg (b : T.Multisegment.{max uF uV, uF}) (m : ℕ)
    (c : Label.{uF, uV} F T m) : 0 ≤ labelWeight F T b m c := by
  unfold labelWeight
  split_ifs <;> norm_num

theorem labelWeight_le_one (b : T.Multisegment.{max uF uV, uF}) (m : ℕ)
    (c : Label.{uF, uV} F T m) : labelWeight F T b m c ≤ 1 := by
  unfold labelWeight
  split_ifs <;> norm_num

theorem IsLabel.degree {b : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (h : IsLabel F T b m c) : b.degree = m := by
  obtain ⟨-, -, -, d, rfl, -⟩ := h
  exact degree_multisegment F T d

theorem IsLabel.classSupport {b : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (h : IsLabel F T b m c) :
    SupportGrading.classSupport F T m c = b.cuspidalContent := by
  let := T.topology
  obtain ⟨A, hA, rfl, d, rfl, hd⟩ := h
  exact classSupport_of_isSubquotient F T d hd.2.1 A hA
    (isSubquotient_of_isZelevinskySubrepresentation F T hd)

/-- Exhaustion: every irreducible label is the label of some multisegment. -/
theorem exists_isLabel (hex : Classification.MultisegmentSocleExhaustion.{uF, uV} F T)
    (m : ℕ) (c : Label.{uF, uV} F T m) : ∃ b, IsLabel F T b m c := by
  let := T.topology
  obtain ⟨A, hA, rfl⟩ := IrreducibleIsoClass.exists_eq c
  obtain ⟨b, -, d, hdb, hd⟩ := hex m A hA
  exact ⟨b, A, hA, rfl, d, hdb, hd.isZelevinskySubrepresentation⟩

/-- The rank-zero unit class is a basis class. -/
theorem gradedUnit_eq_basisClass :
    ∃ c : Label.{uF, uV} F T 0, gradedUnit.{uF, uV} F T = basisClass F T 0 c := by
  let := T.topology
  have hirr : (T.binaryProductUnit.{uF, max uF uV}).IsIrreducible :=
    ExactFunctorIrreducibility.isIrreducible_of_finrank_eq_one _
      T.finrank_binaryProductUnit.{uF, max uF uV}
  exact ⟨GeneralLinear.irreducibleIsoClass 0 F.Carrier _ hirr, by
    rw [basisClass_irreducibleIsoClass]
    rfl⟩

/-- The highest-derivative step on labels: a label of `b` of positive degree yields a label
of `b⁻` occurring in the total derivative of its basis class. -/
theorem exists_derivative_isLabel (hstep : HighestDerivativeLabelStep.{uF, uV} F T ψ)
    {b : T.Multisegment.{max uF uV, uF}} {m : ℕ} {c : Label.{uF, uV} F T m}
    (h : IsLabel F T b m c) (hm : 0 < m) :
    ∃ k, 0 < k ∧ k ≤ m ∧ ∃ c'' : Label.{uF, uV} F T (m - k),
      IsLabel F T (Multisegment.dropLast b) (m - k) c'' ∧
        0 < coeff F T (m - k) c'' (gradedDerivative F T ψ (basisClass F T m c)) := by
  let := T.topology
  obtain ⟨A, hA, rfl, d, rfl, hd⟩ := h
  obtain ⟨hk, d', π', hd'm, hd', hsub⟩ := hstep m hm d A hd
  have hπ' : π'.IsIrreducible := hd'.2.2.1
  exact ⟨_, sum_rank_pos F T d hm, hk, GeneralLinear.irreducibleIsoClass _ F.Carrier π' hπ',
    ⟨π', hπ', rfl, d', hd'm, hd'⟩, coeff_gradedDerivative_pos F T ψ m _ hk A hA π' hπ' hsub⟩

/-- The highest-derivative step holds: it is Worker 237's
`ZelevinskyHighestDerivative.exists_label_subquotient` applied to the homogeneity of
precedence-ordered products of segment socles (Ze80 Theorem 6.2). -/
theorem highestDerivativeLabelStep : HighestDerivativeLabelStep.{uF, uV} F T ψ :=
  ZelevinskyHighestDerivative.exists_label_subquotient F T
    (Classification.segmentSocleProductHomogeneity.{uF, max uF uV} F T) ψ

end Labels

section Triangularity

variable (hx : BinaryProductExactnessStatement.{uF, uV} F T)
  (hl : GradedInductionRingLawsStatement F T hx)
  (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- A label of `b` occurs in `ζ(b)`. -/
theorem one_le_coeff_zeta_of_isLabel {b : T.Multisegment.{max uF uV, uF}} {m : ℕ}
    {c : Label.{uF, uV} F T m} (h : IsLabel F T b m c) :
    1 ≤ coeff F T m c (zeta F T hx hl b) := by
  let := T.topology
  obtain ⟨A, hA, rfl, d, rfl, hd⟩ := h
  have hsoc : d.HasSegmentSocles := hd.2.1
  have hfl := SegmentProductClass.hasFiniteLength_induced F T d hsoc
  have hsub : SmoothRep.IsSubquotient A d.induced :=
    isSubquotient_of_isZelevinskySubrepresentation F T hd
  have hpos : 0 < compositionMultiplicity ⟨_, hfl⟩ A :=
    (compositionMultiplicity_pos_iff_isSubquotient ⟨_, hfl⟩ A hA).mpr hsub
  have hc := coeff_gradedInclusion_ofRepresentation F T m _ hfl A hA
  rw [← zeta_multisegment F T hx hl d hsoc] at hc
  rw [hc]
  exact_mod_cast hpos

/-- **Zelevinsky's Theorem 7.1, triangularity (rank-order form of 7.4).** If a label of `b`
occurs in `ζ(a)`, then `b ≼ a` in the rank order. -/
theorem rankLE_of_coeff_zeta_pos (hstep : HighestDerivativeLabelStep.{uF, uV} F T ψ) :
    ∀ (m : ℕ) (c : Label.{uF, uV} F T m) (b a : T.Multisegment.{max uF uV, uF}),
      IsLabel F T b m c → 0 < coeff F T m c (zeta F T hx hl a) → Multisegment.RankLE b a := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro c b a hb ha
  have hcont : b.cuspidalContent = a.cuspidalContent :=
    (IsLabel.classSupport F T hb).symm.trans (classSupport_of_coeff_zeta_pos F T hx hl ha)
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · have hb0 : b = 0 := eq_zero_of_degree_eq_zero F T (IsLabel.degree F T hb)
    have ha0 : a = 0 := by
      refine eq_zero_of_degree_eq_zero F T ?_
      by_contra hne
      rw [coeff_zeta_eq_zero_of_ne F T hx hl (Ne.symm hne)] at ha
      exact lt_irrefl 0 ha
    rw [hb0, ha0]
    exact Multisegment.RankLE.refl 0
  · obtain ⟨k, hk0, hk, c'', hlab, hpos⟩ := exists_derivative_isLabel F T ψ hstep hb hm
    have hχ : 0 < coeff F T (m - k) c'' (gradedDerivative F T ψ (zeta F T hx hl a)) := by
      have h1 := coeff_mul_le_of_isEffective F T
        (χ := (coeff F T (m - k) c'').comp (gradedDerivative F T ψ))
        (fun m' c' => isEffective_gradedDerivative_basisClass F T ψ m' c' _ _)
        (isEffective_zeta F T hx hl a) m c
      exact lt_of_lt_of_le (mul_pos ha hpos) h1
    rw [gradedDerivative_zeta F T hx hl ψ, map_multiset_sum, Multiset.map_map] at hχ
    obtain ⟨q, hq, hqpos⟩ := exists_mem_pos_of_sum_pos hχ
    have hqa : q.1 + q.2 = a := Multiset.mem_antidiagonal.mp hq
    have hrank : Multisegment.RankLE (Multisegment.dropLast b)
        (Multisegment.dropLast q.1 + q.2) := ih (m - k) (by omega) c'' _ _ hlab hqpos
    have e : Multisegment.dropLast q.1 + q.2 = q.2 + Multisegment.dropLast q.1 := add_comm _ _
    rw [e] at hrank
    exact Multisegment.RankLE.of_dropLast (c := q.2) (S := q.1) (hqa.symm.trans (add_comm _ _))
      hcont hrank

/-- Labels of `a⁻` do not occur in `ζ(a₁⁻ + a₂)` when `a = a₁ + a₂` with `a₂ ≠ 0`: the
cuspidal contents differ. -/
theorem labelCount_zeta_eq_zero {a : T.Multisegment.{max uF uV, uF}}
    {q : T.Multisegment.{max uF uV, uF} × T.Multisegment.{max uF uV, uF}}
    (hq : q.1 + q.2 = a) (h2 : q.2 ≠ 0) :
    weightedCount F T (labelWeight F T (Multisegment.dropLast a))
      (zeta F T hx hl (Multisegment.dropLast q.1 + q.2)) = 0 := by
  refine weightedCount_eq_zero_of F T fun m c hc => labelWeight_of_not_isLabel F T fun hlab => h2 ?_
  have hpos : 0 < coeff F T m c (zeta F T hx hl (Multisegment.dropLast q.1 + q.2)) :=
    lt_of_le_of_ne (isEffective_zeta F T hx hl _ m c) (Ne.symm hc)
  have h1 := classSupport_of_coeff_zeta_pos F T hx hl hpos
  rw [IsLabel.classSupport F T hlab, ← hq, Multisegment.dropLast_add,
    Multisegment.cuspidalContent_add, Multisegment.cuspidalContent_add] at h1
  have h3 := add_left_cancel h1
  have h4 := card_cuspidalContent_dropLast F T q.2
  rw [h3] at h4
  exact Multiset.card_eq_zero.mp (by omega)

/-- **Zelevinsky's Theorem 7.1, multiplicity one (weak-label form of 7.2).** The labels of
`a` occur in `ζ(a)` with total multiplicity at most one. -/
theorem labelCount_zeta_le_one (hstep : HighestDerivativeLabelStep.{uF, uV} F T ψ) :
    ∀ a : T.Multisegment.{max uF uV, uF},
      weightedCount F T (labelWeight F T a) (zeta F T hx hl a) ≤ 1 := by
  suffices h : ∀ n (a : T.Multisegment.{max uF uV, uF}), a.degree = n →
      weightedCount F T (labelWeight F T a) (zeta F T hx hl a) ≤ 1 from
    fun a => h _ a rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro a hn
  by_cases ha : a = 0
  · subst ha
    obtain ⟨c0, hc0⟩ := gradedUnit_eq_basisClass F T
    rw [zeta_zero, hc0, weightedCount_basisClass]
    exact labelWeight_le_one F T _ _ _
  · have hbound : ∀ m c, labelWeight F T a m c ≤
        weightedCount F T (labelWeight F T (Multisegment.dropLast a))
          (gradedDerivative F T ψ (basisClass F T m c)) := by
      intro m c
      by_cases hc : IsLabel F T a m c
      · rw [labelWeight_of_isLabel F T hc]
        have hm : 0 < m := by
          rw [← IsLabel.degree F T hc]
          exact Nat.pos_of_ne_zero fun h0 => ha (eq_zero_of_degree_eq_zero F T h0)
        obtain ⟨k, -, -, c'', hlab, hpos⟩ := exists_derivative_isLabel F T ψ hstep hc hm
        have h1 := coeff_mul_le_weightedCount F T
          (w := labelWeight F T (Multisegment.dropLast a)) (labelWeight_nonneg F T _)
          (isEffective_gradedDerivative_basisClass F T ψ m c) (m - k) c''
        rw [labelWeight_of_isLabel F T hlab, mul_one] at h1
        omega
      · rw [labelWeight_of_not_isLabel F T hc]
        exact weightedCount_nonneg F T (labelWeight_nonneg F T _)
          (isEffective_gradedDerivative_basisClass F T ψ m c)
    have hle := le_of_isEffective F T (φ := weightedCount F T (labelWeight F T a))
      (χ := (weightedCount F T (labelWeight F T (Multisegment.dropLast a))).comp
        (gradedDerivative F T ψ))
      (fun m c => by rw [weightedCount_basisClass]; exact hbound m c)
      (isEffective_zeta F T hx hl a)
    rw [LinearMap.comp_apply, gradedDerivative_zeta F T hx hl ψ, map_multiset_sum,
      Multiset.map_map, sum_antidiagonal_eq_of_mem_snd a
        ((weightedCount F T (labelWeight F T (Multisegment.dropLast a))) ∘
          fun q => zeta F T hx hl (Multisegment.dropLast q.1 + q.2)) fun q hq h2 =>
        labelCount_zeta_eq_zero F T hx hl (Multiset.mem_antidiagonal.mp hq) h2] at hle
    refine hle.trans ?_
    have hlt : (Multisegment.dropLast a).degree < n := hn ▸ degree_dropLast_lt F T ha
    have := ih _ hlt (Multisegment.dropLast a) rfl
    simpa only [Function.comp_apply, add_zero] using this

/-! ### Surjectivity -/

/-- The range of the segment-polynomial evaluation, as an additive subgroup. -/
def evaluationRange : AddSubgroup (GradedGrothendieckGroup.{uF, uV} F T) :=
  letI := T.topology
  letI := gradedInductionRing F T hx hl
  (segmentPolynomialEvaluation F T hx hl).toAddMonoidHom.range

theorem zeta_mem_evaluationRange (a : T.Multisegment.{max uF uV, uF}) :
    zeta F T hx hl a ∈ evaluationRange F T hx hl :=
  AddMonoidHom.mem_range.mpr ⟨_, rfl⟩

/-- Every basis class is in the range of the evaluation, by well-founded induction on the
rank order of a multisegment labelling it. -/
theorem basisClass_mem_evaluationRange
    (hex : Classification.MultisegmentSocleExhaustion.{uF, uV} F T)
    (hstep : HighestDerivativeLabelStep.{uF, uV} F T ψ) (m : ℕ) (c : Label.{uF, uV} F T m) :
    basisClass F T m c ∈ evaluationRange F T hx hl := by
  have key : ∀ b : T.Multisegment.{max uF uV, uF}, ∀ (m : ℕ) (c : Label.{uF, uV} F T m),
      IsLabel F T b m c → basisClass F T m c ∈ evaluationRange F T hx hl := by
    intro b
    refine (Multisegment.wellFounded_rankLT (T := T)).induction
      (C := fun b => ∀ (m : ℕ) (c : Label.{uF, uV} F T m),
        IsLabel F T b m c → basisClass F T m c ∈ evaluationRange F T hx hl) b ?_
    intro b ih m c hb
    have h1 := one_le_coeff_zeta_of_isLabel F T hx hl hb
    have hy : IsEffective F T (zeta F T hx hl b - basisClass F T m c) :=
      isEffective_sub_basisClass F T (isEffective_zeta F T hx hl b) h1
    have hcount : weightedCount F T (labelWeight F T b)
        (zeta F T hx hl b - basisClass F T m c) ≤ 0 := by
      rw [map_sub, weightedCount_basisClass, labelWeight_of_isLabel F T hb]
      have := labelCount_zeta_le_one F T hx hl ψ hstep b
      omega
    have hymem : zeta F T hx hl b - basisClass F T m c ∈ evaluationRange F T hx hl := by
      refine mem_of_coeff F T fun m' c' hc' => ?_
      have hpos : 0 < coeff F T m' c' (zeta F T hx hl b - basisClass F T m c) :=
        lt_of_le_of_ne (hy m' c') (Ne.symm hc')
      obtain ⟨b', hb'⟩ := exists_isLabel F T hex m' c'
      have hz : 0 < coeff F T m' c' (zeta F T hx hl b) := by
        have e := map_sub (coeff F T m' c') (zeta F T hx hl b) (basisClass F T m c)
        have := isEffective_basisClass F T m c m' c'
        omega
      have hrank := rankLE_of_coeff_zeta_pos F T hx hl ψ hstep m' c' b' b hb' hz
      have hne : b' ≠ b := by
        rintro rfl
        have := coeff_mul_le_weightedCount F T (labelWeight_nonneg F T b') hy m' c'
        rw [labelWeight_of_isLabel F T hb', mul_one] at this
        omega
      exact ih b' ⟨hrank, hne⟩ m' c' hb'
    have e : basisClass F T m c = zeta F T hx hl b - (zeta F T hx hl b - basisClass F T m c) :=
      (sub_sub_cancel _ _).symm
    rw [e]
    exact (evaluationRange F T hx hl).sub_mem (zeta_mem_evaluationRange F T hx hl b) hymem
  obtain ⟨b, hb⟩ := exists_isLabel F T hex m c
  exact key b m c hb

/-- **Surjectivity of the segment-polynomial evaluation**, from exhaustion and the
highest-derivative step. -/
theorem segmentPolynomialEvaluation_surjective
    (hex : Classification.MultisegmentSocleExhaustion.{uF, uV} F T)
    (hstep : HighestDerivativeLabelStep.{uF, uV} F T ψ) :
    letI := T.topology
    letI := gradedInductionRing F T hx hl
    Function.Surjective (segmentPolynomialEvaluation F T hx hl) := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  intro x
  have hmem : x ∈ evaluationRange F T hx hl :=
    mem_of_coeff F T fun m c _ => basisClass_mem_evaluationRange F T hx hl ψ hex hstep m c
  obtain ⟨y, hy⟩ := AddMonoidHom.mem_range.mp hmem
  exact ⟨y, hy⟩

/-- **Ze80 Corollary 7.5**, conditional on exhaustion and the highest-derivative step:
the segment-polynomial evaluation is bijective. Injectivity is
`segmentPolynomialEvaluation_injective_of_derivation` applied to the total derivative. -/
theorem segmentPolynomialComparison_of_exhaustion
    (hex : Classification.MultisegmentSocleExhaustion.{uF, uV} F T)
    (hstep : HighestDerivativeLabelStep.{uF, uV} F T ψ) :
    SegmentPolynomialComparisonStatement F T hx hl := by
  let := T.topology
  let := gradedInductionRing F T hx hl
  exact ⟨segmentPolynomialEvaluation_injective_of_derivation F T hx hl
      (gradedDerivativeRingHom F T ψ hx hl)
      (fun Δ h => gradedDerivative_segmentSocle_of_length_eq_one F T ψ Δ h)
      (fun Δ h => gradedDerivative_segmentSocle_of_two_le F T ψ Δ h),
    segmentPolynomialEvaluation_surjective F T hx hl ψ hex hstep⟩

/-- **Ze80 Corollary 7.5**, conditional only on multisegment socle exhaustion: the
segment-polynomial evaluation is bijective. -/
theorem segmentPolynomialComparison_of_socleExhaustion
    (hex : Classification.MultisegmentSocleExhaustion.{uF, uV} F T) :
    SegmentPolynomialComparisonStatement F T hx hl := by
  let := T.topology
  obtain ⟨ψ⟩ := HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T
  exact segmentPolynomialComparison_of_exhaustion F T hx hl ψ hex
    (highestDerivativeLabelStep F T ψ)

end Triangularity

end SegmentPolynomialSurjectivity

end Langlands.Aubert
