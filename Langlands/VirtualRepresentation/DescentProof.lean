import Langlands.VirtualRepresentation.DescentStatement
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-!
# Integral relation descent and positive basis extraction

Proof development for the concrete finitely supported integer lattices.
-/

noncomputable section

namespace Langlands.VirtualRepresentation

universe u v w z

open scoped BigOperators

variable {ι : Type u} {κ : Type v} {J : Type w}

@[simp] theorem extend_generator {M : Type z} [AddCommGroup M] [hM : Module ℤ M]
    (f : ι → M) (i : ι) : extend f (generator i) = f i := by
  simp only [extend, generator, Finsupp.linearCombination_single]
  exact hM.toDistribMulAction.toMulAction.one_smul (f i)

@[simp] theorem generator_apply_self (i : ι) : (generator i) i = 1 := by
  simp [generator]

theorem integral_hom_ext {M : Type z} [AddCommGroup M] [Module ℤ M]
    {f g : IntegralLattice ι →ₗ[ℤ] M}
    (h : ∀ i, f (generator i) = g (generator i)) : f = g := by
  apply (integralBasis (ι := ι)).ext
  exact h

@[simp] theorem degree_generator (weight : ι → ℕ) (i : ι) :
    degree weight (generator i) = (weight i : ℤ) := by
  simp [degree]

@[simp] theorem pairing_generator_left (i : ι) (x : IntegralLattice ι) :
    pairing (generator i) x = x i := by
  simp [pairing, coefficient]

@[simp] theorem pairing_generator_right (x : IntegralLattice ι) (i : ι) :
    pairing x (generator i) = x i := by
  have h : (LinearMap.applyₗ (R := ℤ) (generator i)).comp pairing = coefficient i := by
    apply integral_hom_ext
    intro j
    change pairing (generator j) (generator i) = (generator j) i
    rw [pairing_generator_left]
    classical
    simp only [generator, Finsupp.single_apply, eq_comm]
  exact DFunLike.congr_fun h x

@[simp] theorem pairing_generator_self (i : ι) :
    pairing (generator i) (generator i) = 1 := by
  rw [pairing_generator_left, generator_apply_self]

theorem pairing_apply (x y : IntegralLattice ι) :
    pairing x y = ∑ i ∈ x.support, x i * y i := by
  simp [pairing, extend, Finsupp.linearCombination_apply, Finsupp.sum,
    coefficient, LinearMap.sum_apply]

theorem coefficient_square_le_pairing (x : IntegralLattice ι) (i : ι) :
    x i * x i ≤ pairing x x := by
  classical
  rw [pairing_apply]
  by_cases hi : i ∈ x.support
  · exact Finset.single_le_sum (fun j _ => mul_self_nonneg (x j)) hi
  · rw [Finsupp.notMem_support_iff.mp hi, zero_mul]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)

theorem integralPairingDefiniteness (ι : Type u) :
    IntegralPairingDefinitenessStatement ι := by
  intro x
  constructor
  · rw [pairing_apply]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)
  · constructor
    · intro hx
      ext i
      have hi := coefficient_square_le_pairing x i
      rw [hx] at hi
      change x i = 0
      nlinarith [sq_nonneg (x i)]
    · rintro rfl
      simp

theorem signed_generator_index_unique {x : IntegralLattice ι} {i j : ι}
    (hi : x = generator i ∨ x = -generator i)
    (hj : x = generator j ∨ x = -generator j) : i = j := by
  classical
  by_contra hij
  rcases hi with hi | hi <;> rcases hj with hj | hj
  all_goals
    have h := congrArg (fun y : IntegralLattice ι => y i) (hi.symm.trans hj)
    simp [generator, hij] at h

theorem integralNormOneSignedBasis (ι : Type u) :
    IntegralNormOneSignedBasisStatement ι := by
  classical
  intro x hx
  have hne : x ≠ 0 := by
    intro h
    simp [h] at hx
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (Finsupp.ext h)
  have hi_le := coefficient_square_le_pairing x i
  rw [hx] at hi_le
  have hi_cases : x i ≤ -1 ∨ 1 ≤ x i := by omega
  have hi_sq : x i * x i = 1 := by
    rcases hi_cases with hi_cases | hi_cases <;> nlinarith
  have hi_sign : x i = 1 ∨ x i = -1 := mul_self_eq_one_iff.mp hi_sq
  have heq : x = generator i ∨ x = -generator i := by
    rcases hi_sign with hi_sign | hi_sign
    · left
      apply sub_eq_zero.mp
      apply (integralPairingDefiniteness ι (x - generator i)).2.mp
      simp [map_sub, LinearMap.sub_apply, hx, hi_sign]
    · right
      have hz : x + generator i = 0 := by
        apply (integralPairingDefiniteness ι (x + generator i)).2.mp
        simp [map_add, LinearMap.add_apply, hx, hi_sign]
      exact eq_neg_of_add_eq_zero_left hz
  exact ⟨i, heq, fun j hj => signed_generator_index_unique hj heq⟩

theorem integralPositiveDegreeBasis (ι : Type u) :
    IntegralPositiveDegreeBasisStatement ι := by
  intro weight x hx hd
  obtain ⟨i, hi, hu⟩ := integralNormOneSignedBasis ι x hx
  have hpos : x = generator i := by
    rcases hi with hi | hi
    · exact hi
    · have hw : (0 : ℤ) ≤ weight i := Int.natCast_nonneg _
      simp only [hi, map_neg, degree_generator] at hd
      omega
  exact ⟨i, hpos, fun j hj => hu j (Or.inl hj)⟩

theorem integralIsometryInjectivity (ι : Type u) (κ : Type v) :
    IntegralIsometryInjectivityStatement ι κ := by
  intro T hT x y hxy
  apply sub_eq_zero.mp
  apply (integralPairingDefiniteness ι (x - y)).2.mp
  rw [← hT]
  simp [map_sub, hxy]

theorem integralIsometrySignedBasis (ι : Type u) (κ : Type v) :
    IntegralIsometrySignedBasisStatement ι κ := by
  classical
  intro T hT
  have hnorm (i : ι) : pairing (T (generator i)) (T (generator i)) = 1 := by
    rw [hT, pairing_generator_self]
  have hex (i : ι) : ∃ j : κ, T (generator i) = generator j ∨
      T (generator i) = -generator j :=
    (integralNormOneSignedBasis κ _ (hnorm i)).exists
  choose f hf using hex
  let sign : ι → ℤ := fun i => if T (generator i) = generator (f i) then 1 else -1
  refine ⟨f, sign, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have h := hT (generator i) (generator j)
    rcases hf i with hi | hi <;> rcases hf j with hj | hj
    all_goals
      rw [hi, hj] at h
      simp only [map_neg, LinearMap.neg_apply, pairing_generator_left] at h
      simp [generator, hij, hne] at h
  · intro i
    simp only [sign]
    split_ifs <;> simp
  · intro i
    dsimp [sign]
    split_ifs with hi
    · simpa using hi
    · simpa using (hf i).resolve_left hi

theorem integralIsometryPositiveBasis (ι : Type u) (κ : Type v) :
    IntegralIsometryPositiveBasisStatement ι κ := by
  classical
  intro sourceWeight targetWeight hpositive T hT hdegree
  have hex (i : ι) : ∃ j : κ, T (generator i) = generator j := by
    apply (integralPositiveDegreeBasis κ targetWeight (T (generator i)) ?_ ?_).exists
    · rw [hT, pairing_generator_self]
    · rw [hdegree, degree_generator]
      exact_mod_cast hpositive i
  choose f hf using hex
  refine ⟨f, ?_, hf, ?_⟩
  · intro i j hij
    have heq : generator i = generator j :=
      integralIsometryInjectivity ι κ T hT (by rw [hf, hf, hij])
    exact signed_generator_index_unique (Or.inl rfl) (Or.inl heq)
  · intro i
    have h := hdegree (generator i)
    rw [hf, degree_generator, degree_generator] at h
    exact_mod_cast h

theorem pairing_extend_eq (left : J → IntegralLattice ι)
    (right : J → IntegralLattice κ)
    (h : ∀ j k, pairing (left j) (left k) = pairing (right j) (right k))
    (x y : IntegralLattice J) :
    pairing (extend left x) (extend left y) =
      pairing (extend right x) (extend right y) := by
  let pl : IntegralLattice J →ₗ[ℤ] IntegralLattice J →ₗ[ℤ] ℤ :=
    (pairing.comp (extend left)).compl₂ (extend left)
  let pr : IntegralLattice J →ₗ[ℤ] IntegralLattice J →ₗ[ℤ] ℤ :=
    (pairing.comp (extend right)).compl₂ (extend right)
  have heq : pl = pr := by
    apply integral_hom_ext
    intro j
    apply integral_hom_ext
    intro k
    simpa [pl, pr] using h j k
  exact DFunLike.congr_fun (DFunLike.congr_fun heq x) y

theorem integralRelationDescent (ι : Type u) (κ : Type v) (J : Type w) :
    IntegralRelationDescentStatement ι κ J := by
  intro left right h
  ext x
  change extend left x = 0 ↔ extend right x = 0
  rw [← (integralPairingDefiniteness ι (extend left x)).2,
    ← (integralPairingDefiniteness κ (extend right x)).2]
  rw [pairing_extend_eq left right h]

@[simp] theorem evaluateGenerators_generator (family : J → IntegralLattice ι) (j : J) :
    evaluateGenerators family (generator j) =
      ⟨family j, Submodule.subset_span (Set.mem_range_self j)⟩ := by
  simp [evaluateGenerators]

@[simp] theorem coe_evaluateGenerators (family : J → IntegralLattice ι)
    (x : IntegralLattice J) :
    (evaluateGenerators family x : IntegralLattice ι) = extend family x := by
  have heq : (generated family).subtype.comp (evaluateGenerators family) =
      extend family := by
    apply integral_hom_ext
    intro j
    simp
  exact DFunLike.congr_fun heq x

theorem evaluateGenerators_surjective (family : J → IntegralLattice ι) :
    Function.Surjective (evaluateGenerators family) := by
  have hrange : LinearMap.range (extend family) = generated family := by
    exact Finsupp.range_linearCombination (R := ℤ) (v := family)
  intro x
  have hx : x.val ∈ LinearMap.range (extend family) := hrange.symm ▸ x.property
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, Subtype.ext ?_⟩
  simpa using hy

theorem ker_evaluateGenerators (family : J → IntegralLattice ι) :
    LinearMap.ker (evaluateGenerators family) = relations family := by
  ext x
  change evaluateGenerators family x = 0 ↔ extend family x = 0
  constructor
  · intro h
    have hv := congrArg (fun z : generated family => (z : IntegralLattice ι)) h
    simpa using hv
  · intro h
    apply Subtype.ext
    simpa using h

theorem generated_hom_ext {M : Type z} [AddCommGroup M] [Module ℤ M]
    (family : J → IntegralLattice ι) {f g : generated family →ₗ[ℤ] M}
    (h : ∀ j, f (evaluateGenerators family (generator j)) =
      g (evaluateGenerators family (generator j))) : f = g := by
  have heq : f.comp (evaluateGenerators family) = g.comp (evaluateGenerators family) := by
    apply integral_hom_ext
    exact h
  ext x
  obtain ⟨y, rfl⟩ := evaluateGenerators_surjective family x
  exact DFunLike.congr_fun heq y

theorem integralGeneratedEquivalence (ι : Type u) (κ : Type v) (J : Type w) :
    IntegralGeneratedEquivalenceStatement ι κ J := by
  intro left right hrelations
  have hker : LinearMap.ker (evaluateGenerators left) =
      LinearMap.ker (evaluateGenerators right) := by
    rw [ker_evaluateGenerators, ker_evaluateGenerators, hrelations]
  let el := (evaluateGenerators left).quotKerEquivOfSurjective
    (evaluateGenerators_surjective left)
  let er := (evaluateGenerators right).quotKerEquivOfSurjective
    (evaluateGenerators_surjective right)
  let T : generated left ≃ₗ[ℤ] generated right :=
    el.symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans er)
  have hT (x : IntegralLattice J) :
      T (evaluateGenerators left x) = evaluateGenerators right x := by
    simp [T, el, er]
  refine ⟨T, fun j => hT (generator j), ?_⟩
  intro S hS
  apply LinearEquiv.toLinearMap_injective
  apply generated_hom_ext left
  intro j
  exact (hS j).trans (hT (generator j)).symm

theorem generated_map_evaluate (left : J → IntegralLattice ι)
    (right : J → IntegralLattice κ) (T : generated left →ₗ[ℤ] generated right)
    (hT : ∀ j, T (evaluateGenerators left (generator j)) =
      evaluateGenerators right (generator j)) (x : IntegralLattice J) :
    T (evaluateGenerators left x) = evaluateGenerators right x := by
  have heq : T.comp (evaluateGenerators left) = evaluateGenerators right := by
    apply integral_hom_ext
    exact hT
  exact DFunLike.congr_fun heq x

theorem integralGeneratedIsometry (ι : Type u) (κ : Type v) (J : Type w) :
    IntegralGeneratedIsometryStatement ι κ J := by
  intro left right hpair T hT x y
  obtain ⟨a, rfl⟩ := evaluateGenerators_surjective left x
  obtain ⟨b, rfl⟩ := evaluateGenerators_surjective left y
  rw [generated_map_evaluate left right T hT,
    generated_map_evaluate left right T hT]
  simp only [coe_evaluateGenerators]
  exact (pairing_extend_eq left right hpair a b).symm

theorem integralGeneratedDegree (ι : Type u) (κ : Type v) (J : Type w) :
    IntegralGeneratedDegreeStatement ι κ J := by
  intro left right sourceWeight targetWeight hdegree T hT x
  have heq : (degree targetWeight).comp (extend right) =
      (degree sourceWeight).comp (extend left) := by
    apply integral_hom_ext
    intro j
    simpa using hdegree j
  obtain ⟨a, rfl⟩ := evaluateGenerators_surjective left x
  rw [generated_map_evaluate left right T hT]
  simp only [coe_evaluateGenerators]
  exact DFunLike.congr_fun heq a

theorem integralDescentAndPositivity (ι : Type u) (κ : Type v) (J : Type w) :
    IntegralDescentAndPositivityStatement ι κ J :=
  ⟨integralPairingDefiniteness ι, integralPairingDefiniteness κ,
    integralRelationDescent ι κ J, integralGeneratedEquivalence ι κ J,
    integralGeneratedIsometry ι κ J, integralGeneratedDegree ι κ J,
    integralNormOneSignedBasis ι, integralNormOneSignedBasis κ,
    integralPositiveDegreeBasis ι, integralPositiveDegreeBasis κ,
    integralIsometryInjectivity ι κ, integralIsometrySignedBasis ι κ,
    integralIsometryPositiveBasis ι κ⟩


end Langlands.VirtualRepresentation
