import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentationZero
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentationDegree
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationGeometry

/-! # Triviality over the complement of the next tuple threshold -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]

/-- The original object inclusion pulls the total threshold back to the
original invariant threshold. -/
theorem tupleFiniteZeroObjectMap_threshold_preimage (N k : ℕ) :
    E.tupleFiniteZeroObjectMap N ⁻¹ᵁ
        E.tupleChartThresholdOpen (fun i : Fin (N + 1) => i.val) k =
      E.tupleThresholdOpen k := by
  apply Opens.ext
  apply Set.ext
  intro x
  change E.tupleChartObjectι (fun i : Fin (N + 1) => i.val) 0
      (E.tupleSymmetricZeroIso.inv x) ∈
        E.tupleChartThresholdOpen (fun i : Fin (N + 1) => i.val) k ↔
      x ∈ E.tupleThresholdOpen k
  rw [E.tupleChartObjectι_mem_threshold_iff]
  have h := congrArg (fun V => E.tupleSymmetricZeroIso.inv x ∈ V)
    (E.tupleSymmetricZeroIso_threshold_preimage k)
  have hx : E.tupleSymmetricZeroIso.hom (E.tupleSymmetricZeroIso.inv x) = x :=
    (Scheme.homeoOfIso E.tupleSymmetricZeroIso).apply_symm_apply x
  change (E.tupleSymmetricZeroIso.hom (E.tupleSymmetricZeroIso.inv x) ∈
      E.tupleThresholdOpen k) =
    (E.tupleSymmetricZeroIso.inv x ∈ E.tupleSymmetricThresholdOpen 0 k) at h
  rw [hx] at h
  exact (eq_iff_iff.mp h).symm

/-- If a finite family has a unique shortest chart, every arrow from any
test scheme whose source avoids the next threshold is the source unit. -/
theorem tupleChart_factors_unit_of_not_threshold {I : Type} [Finite I]
    (length : I → ℕ) (i : I) (hi : ∀ j, j ≠ i → length i < length j)
    {T : Scheme.{u}} (a : T ⟶ (E.tupleChartPresentation length).R)
    (ha : ∀ x : T, (a ≫ (E.tupleChartPresentation length).s) x ∉
      E.tupleChartThresholdOpen length (length i + 1)) :
    a = a ≫ (E.tupleChartPresentation length).s ≫
      (E.tupleChartPresentation length).unit := by
  have havs (x : T) :
      (E.tupleChartPresentation length).s (a x) ∉
        E.tupleChartThresholdOpen length (length i + 1) := ha x
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
  have hlnot (x : T) :
      (l ≫ E.tupleSymmetricCrossLeft (length i) (length i)) x ∉
        E.tupleSymmetricThresholdOpen (length i) (length i + 1) := by
    intro hx
    have h := (E.tupleChartObjectι_mem_threshold_iff length (length i + 1) i
      ((l ≫ E.tupleSymmetricCrossLeft (length i) (length i)) x)).mpr hx
    change ((l ≫ E.tupleSymmetricCrossLeft (length i) (length i)) ≫
      E.tupleChartObjectι length i) x ∈ _ at h
    rw [Category.assoc, ← E.tupleChartRelationι_t, ← Category.assoc, hl] at h
    exact havt x h
  have hleq := E.tupleSymmetricCross_endpoints_eq_of_not_threshold (length i) l hlnot
  have hends : a ≫ (E.tupleChartPresentation length).t =
      a ≫ (E.tupleChartPresentation length).s := by
    calc
      _ = (l ≫ E.tupleSymmetricCrossLeft (length i) (length i)) ≫
          E.tupleChartObjectι length i := by rw [← hl]; simp
      _ = (l ≫ E.tupleSymmetricCrossRight (length i) (length i)) ≫
          E.tupleChartObjectι length i := by rw [hleq]
      _ = _ := by rw [← hl]; simp
  apply (E.tupleChartPresentation length).hom_ext
  · simpa using hends
  · simp

/-- The source pullback over any scheme mapping outside the next threshold
is the identity relation, with its full scheme structure. -/
theorem tupleChart_unit_isPullback_of_not_threshold {I : Type} [Finite I]
    (length : I → ℕ) (i : I) (hi : ∀ j, j ≠ i → length i < length j)
    {T : Scheme.{u}} (d : T ⟶ (E.tupleChartPresentation length).U)
    (hd : ∀ x : T, d x ∉ E.tupleChartThresholdOpen length (length i + 1)) :
    IsPullback (d ≫ (E.tupleChartPresentation length).unit) (𝟙 T)
      (E.tupleChartPresentation length).s d := by
  refine IsPullback.mk' (by simp) ?_ ?_
  · intro V a b _ h
    simpa using h
  · intro V a b hab
    have ha := E.tupleChart_factors_unit_of_not_threshold length i hi a (by
      intro x
      rw [hab]
      exact hd (b x))
    refine ⟨b, ?_, by simp⟩
    calc
      b ≫ (d ≫ (E.tupleChartPresentation length).unit) =
          (b ≫ d) ≫ (E.tupleChartPresentation length).unit :=
        (Category.assoc _ _ _).symm
      _ = (a ≫ (E.tupleChartPresentation length).s) ≫
          (E.tupleChartPresentation length).unit := by rw [hab]
      _ = a := by simpa only [Category.assoc] using ha.symm

/-- The closed complement of the next threshold in a finite tuple tail. -/
def tupleTailNextComplementClosed (N p : ℕ) :
    Closeds (E.tupleTailPresentation N p).U :=
  ⟨(E.tupleChartThresholdOpen
      (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) (p + 1) :
        Set (E.tupleTailPresentation N p).U)ᶜ,
    (E.tupleChartThresholdOpen
      (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) (p + 1)).isOpen.isClosed_compl⟩

/-- The canonical closed scheme structure on the next-threshold complement. -/
def tupleTailNextComplementScheme (N p : ℕ) : Scheme.{u} :=
  (Scheme.IdealSheafData.vanishingIdeal (E.tupleTailNextComplementClosed N p)).subscheme

/-- The closed immersion of the next-threshold complement into the tail. -/
def tupleTailNextComplementι (N p : ℕ) :
    E.tupleTailNextComplementScheme N p ⟶ (E.tupleTailPresentation N p).U :=
  (Scheme.IdealSheafData.vanishingIdeal (E.tupleTailNextComplementClosed N p)).subschemeι

instance tupleTailNextComplementι_isClosedImmersion (N p : ℕ) :
    IsClosedImmersion (E.tupleTailNextComplementι N p) :=
  inferInstanceAs (IsClosedImmersion
    (Scheme.IdealSheafData.vanishingIdeal (E.tupleTailNextComplementClosed N p)).subschemeι)

instance tupleTailNextComplementScheme_isAffine (N p : ℕ) :
    IsAffine (E.tupleTailNextComplementScheme N p) :=
  isAffine_of_isAffineHom (E.tupleTailNextComplementι N p)

theorem tupleTailNextComplementι_range (N p : ℕ) :
    Set.range (E.tupleTailNextComplementι N p) =
      (E.tupleTailNextComplementClosed N p : Set (E.tupleTailPresentation N p).U) := by
  change Set.range
    (Scheme.IdealSheafData.vanishingIdeal (E.tupleTailNextComplementClosed N p)).subschemeι = _
  rw [Scheme.IdealSheafData.range_subschemeι,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]

theorem tupleTailNextComplementι_not_mem_threshold (N p : ℕ)
    (x : E.tupleTailNextComplementScheme N p) :
    E.tupleTailNextComplementι N p x ∉ E.tupleChartThresholdOpen
      (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) (p + 1) := by
  change E.tupleTailNextComplementι N p x ∈
    (E.tupleTailNextComplementClosed N p : Set (E.tupleTailPresentation N p).U)
  rw [← E.tupleTailNextComplementι_range N p]
  exact ⟨x, rfl⟩

/-- Over the canonical complement, the finite-tail source relation is the
identity relation on that complement. -/
theorem tupleTailNextComplement_unit_isPullback (N p : ℕ) (hp : p < N + 1) :
    IsPullback (E.tupleTailNextComplementι N p ≫ (E.tupleTailPresentation N p).unit)
      (𝟙 (E.tupleTailNextComplementScheme N p))
      (E.tupleTailPresentation N p).s (E.tupleTailNextComplementι N p) :=
  E.tupleChart_unit_isPullback_of_not_threshold _
    (tupleTailLowestIndex N p hp) (tupleTailLowestIndex_strict N p hp)
    (E.tupleTailNextComplementι N p) (E.tupleTailNextComplementι_not_mem_threshold N p)

/-- The canonical complement is the source base change of the tail relation. -/
def tupleTailNextComplementCrossIso (N p : ℕ) (hp : p < N + 1) :
    E.tupleTailNextComplementScheme N p ≅
      pullback (E.tupleTailPresentation N p).s (E.tupleTailNextComplementι N p) :=
  (E.tupleTailNextComplement_unit_isPullback N p hp).isoPullback

@[reassoc (attr := simp)]
theorem tupleTailNextComplementCrossIso_hom_fst (N p : ℕ) (hp : p < N + 1) :
    (E.tupleTailNextComplementCrossIso N p hp).hom ≫ pullback.fst _ _ =
      E.tupleTailNextComplementι N p ≫ (E.tupleTailPresentation N p).unit :=
  (E.tupleTailNextComplement_unit_isPullback N p hp).isoPullback_hom_fst

@[reassoc (attr := simp)]
theorem tupleTailNextComplementCrossIso_hom_snd (N p : ℕ) (hp : p < N + 1) :
    (E.tupleTailNextComplementCrossIso N p hp).hom ≫ pullback.snd _ _ = 𝟙 _ :=
  (E.tupleTailNextComplement_unit_isPullback N p hp).isoPullback_hom_snd

theorem tupleTailNextComplementCrossIso_inv_eq_snd (N p : ℕ) (hp : p < N + 1) :
    (E.tupleTailNextComplementCrossIso N p hp).inv = pullback.snd _ _ := by
  simpa only [tupleTailNextComplementCrossIso, Category.comp_id] using
    (E.tupleTailNextComplement_unit_isPullback N p hp).isoPullback_inv_snd

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
