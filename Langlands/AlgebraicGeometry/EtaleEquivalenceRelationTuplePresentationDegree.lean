import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentationFiltration
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleDegreeScheme
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleOffDiagonal

/-! # Degree and off-diagonal maps in total tuple presentations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

/-- The exact degree locus of a chart, included in the total object scheme. -/
def tupleChartDegreeι {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleSymmetricDegreeScheme (length i) ⟶ (E.tupleChartPresentation length).U :=
  E.tupleSymmetricDegreeι (length i) ≫ E.tupleChartObjectι length i

instance tupleChartDegreeι_isClosedImmersion {I : Type} [Finite I]
    (length : I → ℕ) (i : I) : IsClosedImmersion (E.tupleChartDegreeι length i) := by
  have : IsClosedImmersion (E.tupleChartObjectι length i) := by
    change IsClosedImmersion (Sigma.ι (fun i => E.tupleSymmetricScheme (length i)) i)
    exact isClosedImmersion_sigma_ι _ _
  exact IsClosedImmersion.comp _ _

/-- The units over an exact degree locus, included in the total relation. -/
def tupleChartDegreeUnit {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleSymmetricDegreeScheme (length i) ⟶ (E.tupleChartPresentation length).R :=
  E.tupleSymmetricDegreeι (length i) ≫ E.tupleSymmetricCrossUnit (length i) ≫
    E.tupleChartRelationι length i i

@[reassoc (attr := simp)]
theorem tupleChartDegreeUnit_t {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleChartDegreeUnit length i ≫ (E.tupleChartPresentation length).t =
      E.tupleChartDegreeι length i := by
  simp [tupleChartDegreeUnit, tupleChartDegreeι]

@[reassoc (attr := simp)]
theorem tupleChartDegreeUnit_s {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleChartDegreeUnit length i ≫ (E.tupleChartPresentation length).s =
      E.tupleChartDegreeι length i := by
  simp [tupleChartDegreeUnit, tupleChartDegreeι]

theorem tupleChartDegreeι_not_mem_threshold {I : Type} [Finite I]
    (length : I → ℕ) (i : I) (x : E.tupleSymmetricDegreeScheme (length i)) :
    E.tupleChartDegreeι length i x ∉ E.tupleChartThresholdOpen length (length i + 1) := by
  simpa only [tupleChartDegreeι, Scheme.Hom.comp_apply,
    E.tupleChartObjectι_mem_threshold_iff] using
      E.tupleSymmetricDegreeι_not_mem_threshold (length i) x

/-- If one chart is strictly shorter than all the others, any point outside
the next threshold belongs to that chart. -/
theorem tupleChartObjectι_index_eq_of_not_threshold {I : Type} [Finite I]
    (length : I → ℕ) (i : I) (hi : ∀ j, j ≠ i → length i < length j)
    (j : I) (x : E.tupleSymmetricScheme (length j))
    (hx : E.tupleChartObjectι length j x ∉
      E.tupleChartThresholdOpen length (length i + 1)) : j = i := by
  classical
  by_contra hji
  have h := E.tupleSymmetricThresholdOpen_antitone (length j)
    (Nat.succ_le_of_lt (hi j hji))
  rw [E.tupleSymmetricThresholdOpen_self] at h
  exact hx ((E.tupleChartObjectι_mem_threshold_iff length _ j x).mpr
    (h (Set.mem_univ x)))

/-- Every arrow whose source is in the exact lowest-degree locus is its unit.
The factorization through open components works on arbitrary test schemes. -/
theorem tupleChartDegree_factors_unit {I : Type} [Finite I]
    (length : I → ℕ) (i : I) (hi : ∀ j, j ≠ i → length i < length j)
    {T : Scheme.{u}} (a : T ⟶ (E.tupleChartPresentation length).R)
    (b : T ⟶ E.tupleSymmetricDegreeScheme (length i))
    (hs : a ≫ (E.tupleChartPresentation length).s = b ≫ E.tupleChartDegreeι length i) :
    a = b ≫ E.tupleChartDegreeUnit length i := by
  have havs (x : T) :
      (E.tupleChartPresentation length).s (a x) ∉
        E.tupleChartThresholdOpen length (length i + 1) := by
    change (a ≫ (E.tupleChartPresentation length).s) x ∉ _
    rw [hs]
    exact E.tupleChartDegreeι_not_mem_threshold length i (b x)
  have havt (x : T) :
      (E.tupleChartPresentation length).t (a x) ∉
        E.tupleChartThresholdOpen length (length i + 1) := by
    intro hx
    have h := congrArg (fun V => a x ∈ V)
      (E.tupleChartThresholdOpen_preimage_eq length (length i + 1))
    exact havs x ((eq_iff_iff.mp h).mp hx)
  have hrange : Set.range a ⊆ Set.range (E.tupleChartRelationι length i i) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨⟨⟨j, k⟩⟩, z, hz⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
      (Discrete.functor (fun p : I × I =>
        E.tupleSymmetricCrossScheme (length p.1) (length p.2))) (a x)
    change E.tupleChartRelationι length j k z = a x at hz
    have hzt : (E.tupleChartRelationι length j k ≫
        (E.tupleChartPresentation length).t) z ∉
          E.tupleChartThresholdOpen length (length i + 1) := by
      change (E.tupleChartPresentation length).t
        (E.tupleChartRelationι length j k z) ∉ _
      rw [hz]
      exact havt x
    have hzs : (E.tupleChartRelationι length j k ≫
        (E.tupleChartPresentation length).s) z ∉
          E.tupleChartThresholdOpen length (length i + 1) := by
      change (E.tupleChartPresentation length).s
        (E.tupleChartRelationι length j k z) ∉ _
      rw [hz]
      exact havs x
    rw [E.tupleChartRelationι_t] at hzt
    rw [E.tupleChartRelationι_s] at hzs
    have hj := E.tupleChartObjectι_index_eq_of_not_threshold length i hi j
      (E.tupleSymmetricCrossLeft (length j) (length k) z) hzt
    have hk := E.tupleChartObjectι_index_eq_of_not_threshold length i hi k
      (E.tupleSymmetricCrossRight (length j) (length k) z) hzs
    subst j
    subst k
    exact ⟨z, hz⟩
  let l := IsOpenImmersion.lift (E.tupleChartRelationι length i i) a hrange
  have hl : l ≫ E.tupleChartRelationι length i i = a :=
    IsOpenImmersion.lift_fac _ _ _
  have hls : l ≫ E.tupleSymmetricCrossRight (length i) (length i) =
      b ≫ E.tupleSymmetricDegreeι (length i) := by
    apply (cancel_mono (E.tupleChartObjectι length i)).mp
    calc
      (l ≫ E.tupleSymmetricCrossRight (length i) (length i)) ≫
          E.tupleChartObjectι length i =
            l ≫ E.tupleChartRelationι length i i ≫
              (E.tupleChartPresentation length).s := by simp
      _ = a ≫ (E.tupleChartPresentation length).s := by rw [← Category.assoc, hl]
      _ = (b ≫ E.tupleSymmetricDegreeι (length i)) ≫
          E.tupleChartObjectι length i := by simpa [tupleChartDegreeι] using hs
  have hlnot (x : T) :
      (l ≫ E.tupleSymmetricCrossLeft (length i) (length i)) x ∉
        E.tupleSymmetricThresholdOpen (length i) (length i + 1) := by
    intro hx
    have h := (E.tupleSymmetricCross_threshold_iff (length i) (length i)
      (length i + 1) (l x)).mp hx
    change (l ≫ E.tupleSymmetricCrossRight (length i) (length i)) x ∈ _ at h
    rw [hls] at h
    exact E.tupleSymmetricDegreeι_not_mem_threshold (length i) (b x) h
  have hleq := E.tupleSymmetricCross_endpoints_eq_of_not_threshold (length i) l hlnot
  have hunit := E.tupleSymmetricCross_factors_unit_of_not_threshold (length i) l hlnot
  calc
    a = l ≫ E.tupleChartRelationι length i i := hl.symm
    _ = (l ≫ E.tupleSymmetricCrossLeft (length i) (length i) ≫
        E.tupleSymmetricCrossUnit (length i)) ≫ E.tupleChartRelationι length i i := by
      rw [← hunit]
    _ = b ≫ E.tupleChartDegreeUnit length i := by
      rw [← Category.assoc l _ _, hleq, hls]
      simp only [tupleChartDegreeUnit, Category.assoc]

/-- The restriction of the total relation to the exact lowest degree is the
identity relation, as a scheme-theoretic source pullback. -/
theorem tupleChartDegree_unit_isPullback {I : Type} [Finite I]
    (length : I → ℕ) (i : I) (hi : ∀ j, j ≠ i → length i < length j) :
    IsPullback (E.tupleChartDegreeUnit length i)
      (𝟙 (E.tupleSymmetricDegreeScheme (length i)))
      (E.tupleChartPresentation length).s (E.tupleChartDegreeι length i) := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro V a b _ h
    simpa using h
  · intro V a b hab
    exact ⟨b, by simpa using (E.tupleChartDegree_factors_unit length i hi a b hab).symm,
      by simp⟩

/-- The lowest chart index in a nonempty finite tail. -/
abbrev tupleTailLowestIndex (N p : ℕ) (hp : p < N + 1) :
    {i : Fin (N + 1) // p ≤ i.val} :=
  ⟨⟨p, hp⟩, le_rfl⟩

theorem tupleTailLowestIndex_strict (N p : ℕ) (hp : p < N + 1)
    (j : {i : Fin (N + 1) // p ≤ i.val}) (hj : j ≠ tupleTailLowestIndex N p hp) :
    p < j.val.val := by
  apply lt_of_le_of_ne j.property
  intro heq
  apply hj
  apply Subtype.ext
  exact Fin.ext heq.symm

theorem tupleTailDegree_unit_isPullback (N p : ℕ) (hp : p < N + 1) :
    IsPullback
      (E.tupleChartDegreeUnit (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val)
        (tupleTailLowestIndex N p hp))
      (𝟙 (E.tupleSymmetricDegreeScheme p))
      (E.tupleTailPresentation N p).s
      (E.tupleChartDegreeι (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val)
        (tupleTailLowestIndex N p hp)) :=
  E.tupleChartDegree_unit_isPullback _ _ (tupleTailLowestIndex_strict N p hp)

/-- The left endpoint of a nonidentity chart arrow, in the next total open. -/
def tupleChartOffDiagonalLeft {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleSymmetricOffDiagonalScheme (length i) ⟶
      (E.tupleChartThresholdOpen length (length i + 1)).toScheme :=
  IsOpenImmersion.lift (E.tupleChartThresholdOpen length (length i + 1)).ι
    (E.tupleSymmetricOffDiagonalι (length i) ≫
      E.tupleSymmetricCrossLeft (length i) (length i) ≫ E.tupleChartObjectι length i)
    (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      apply (E.tupleChartObjectι_mem_threshold_iff length _ i _).mpr
      exact E.tupleSymmetricOffDiagonalOpen_left_mem_threshold (length i) x.1 x.2)

/-- The right endpoint of a nonidentity chart arrow, in the next total open. -/
def tupleChartOffDiagonalRight {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleSymmetricOffDiagonalScheme (length i) ⟶
      (E.tupleChartThresholdOpen length (length i + 1)).toScheme :=
  IsOpenImmersion.lift (E.tupleChartThresholdOpen length (length i + 1)).ι
    (E.tupleSymmetricOffDiagonalι (length i) ≫
      E.tupleSymmetricCrossRight (length i) (length i) ≫ E.tupleChartObjectι length i)
    (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      apply (E.tupleChartObjectι_mem_threshold_iff length _ i _).mpr
      exact E.tupleSymmetricOffDiagonalOpen_right_mem_threshold (length i) x.1 x.2)

@[reassoc (attr := simp)]
theorem tupleChartOffDiagonalLeft_ι {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleChartOffDiagonalLeft length i ≫
        (E.tupleChartThresholdOpen length (length i + 1)).ι =
      E.tupleSymmetricOffDiagonalι (length i) ≫
        E.tupleSymmetricCrossLeft (length i) (length i) ≫ E.tupleChartObjectι length i :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem tupleChartOffDiagonalRight_ι {I : Type} [Finite I] (length : I → ℕ) (i : I) :
    E.tupleChartOffDiagonalRight length i ≫
        (E.tupleChartThresholdOpen length (length i + 1)).ι =
      E.tupleSymmetricOffDiagonalι (length i) ≫
        E.tupleSymmetricCrossRight (length i) (length i) ≫ E.tupleChartObjectι length i :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
theorem tupleSymmetricOffDiagonalSwap_chartLeft {I : Type} [Finite I]
    (length : I → ℕ) (i : I) :
    E.tupleSymmetricOffDiagonalSwap (length i) ≫ E.tupleChartOffDiagonalLeft length i =
      E.tupleChartOffDiagonalRight length i := by
  apply (cancel_mono (E.tupleChartThresholdOpen length (length i + 1)).ι).mp
  simp

@[reassoc (attr := simp)]
theorem tupleSymmetricOffDiagonalSwap_chartRight {I : Type} [Finite I]
    (length : I → ℕ) (i : I) :
    E.tupleSymmetricOffDiagonalSwap (length i) ≫ E.tupleChartOffDiagonalRight length i =
      E.tupleChartOffDiagonalLeft length i := by
  apply (cancel_mono (E.tupleChartThresholdOpen length (length i + 1)).ι).mp
  simp

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
