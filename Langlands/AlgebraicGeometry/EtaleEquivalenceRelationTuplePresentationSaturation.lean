import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentationReindex

/-! # Images and saturations of symmetric tuple charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]

/-- Ordered tuples whose zeroth coordinates are related have a point of the
ordered cross-correspondence lying over both tuples. -/
theorem exists_tupleCross_point (m n : ℕ)
    (x : E.tupleDistinctScheme m) (y : E.tupleDistinctScheme n)
    (h : E.PointRel (E.tupleDistinctProjection n 0 y)
      (E.tupleDistinctProjection m 0 x)) :
    ∃ z : E.tupleCrossScheme m n,
      E.tupleCrossLeft m n z = x ∧ E.tupleCrossRight m n z = y := by
  obtain ⟨r, hrs, hrt⟩ := h
  obtain ⟨a, ha, har⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := E.tupleDistinctProjection m 0) (g := E.t) x r hrt.symm
  have has : (pullback.snd (E.tupleDistinctProjection m 0) E.t ≫ E.s) a =
      E.tupleDistinctProjection n 0 y := by
    change E.s (pullback.snd (E.tupleDistinctProjection m 0) E.t a) = _
    rw [har, hrs]
  obtain ⟨z, hza, hzy⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := pullback.snd (E.tupleDistinctProjection m 0) E.t ≫ E.s)
    (g := E.tupleDistinctProjection n 0) a y has
  refine ⟨z, ?_, hzy⟩
  change pullback.fst (E.tupleDistinctProjection m 0) E.t
    (pullback.fst
      (pullback.snd (E.tupleDistinctProjection m 0) E.t ≫ E.s)
      (E.tupleDistinctProjection n 0) z) = x
  rw [hza, ha]

variable [IsAffine E.U] [IsAffine E.R]

/-- The image of the first symmetric cross endpoint is exactly the threshold
for tuples of the second length. -/
theorem tupleSymmetricCrossLeft_range (m n : ℕ) :
    Set.range (E.tupleSymmetricCrossLeft m n) =
      (E.tupleSymmetricThresholdOpen m n : Set (E.tupleSymmetricScheme m)) := by
  apply Set.ext
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    apply (E.tupleSymmetricCross_threshold_iff m n n z).mpr
    rw [E.tupleSymmetricThresholdOpen_self]
    trivial
  · intro hx
    obtain ⟨a, rfl⟩ := (E.tupleSymmetricMap m).surjective x
    have ha := (E.tupleSymmetricMap_mem_threshold_iff m n a).mp hx
    obtain ⟨y, hy, hya⟩ :=
      (E.mem_pointSaturationOpen (E.tupleImageOpen n) _).mp ha
    obtain ⟨b, hb⟩ := hy
    have hba : E.PointRel (E.tupleDistinctProjection n 0 b)
        (E.tupleDistinctProjection m 0 a) := by
      rw [hb]
      exact hya
    obtain ⟨z, hza, _⟩ := E.exists_tupleCross_point m n a b hba
    refine ⟨E.tupleSymmetricCrossMap m n z, ?_⟩
    change (E.tupleSymmetricCrossMap m n ≫ E.tupleSymmetricCrossLeft m n) z =
      E.tupleSymmetricMap m a
    rw [E.tupleSymmetricCrossMap_left]
    change E.tupleSymmetricMap m (E.tupleCrossLeft m n z) = _
    rw [hza]

variable [IsClosedImmersion (prod.lift E.t E.s)]

/-- In a finite tuple presentation, the saturation of one component is the
total threshold at that component's length. -/
theorem tupleChartObjectι_saturation {I : Type} [Finite I]
    (length : I → ℕ) (i : I) :
    (E.tupleChartPresentation length).pointSaturationOpen
        (E.tupleChartObjectι length i ''ᵁ ⊤) =
      E.tupleChartThresholdOpen length (length i) := by
  apply Opens.ext
  apply Set.ext
  intro x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ :=
      ((E.tupleChartPresentation length).mem_pointSaturationOpen _ x).mp hx
    apply E.tupleChartThresholdOpen_invariant length (length i) hyx
    obtain ⟨z, _, rfl⟩ := hy
    apply (E.tupleChartObjectι_mem_threshold_iff length (length i) i z).mpr
    rw [E.tupleSymmetricThresholdOpen_self]
    trivial
  · intro hx
    obtain ⟨⟨j⟩, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
      (Discrete.functor (fun j => E.tupleSymmetricScheme (length j))) x
    have hx' := (E.tupleChartObjectι_mem_threshold_iff length (length i) j x).mp hx
    change x ∈ (E.tupleSymmetricThresholdOpen (length j) (length i) :
      Set (E.tupleSymmetricScheme (length j))) at hx'
    rw [← E.tupleSymmetricCrossLeft_range (length j) (length i)] at hx'
    obtain ⟨z, hzx⟩ := hx'
    apply ((E.tupleChartPresentation length).mem_pointSaturationOpen _ _).mpr
    refine ⟨E.tupleChartObjectι length i
      (E.tupleSymmetricCrossRight (length j) (length i) z), ⟨_, trivial, rfl⟩,
      E.tupleChartRelationι length j i z, ?_, ?_⟩
    · change (E.tupleChartRelationι length j i ≫
        (E.tupleChartPresentation length).s) z = _
      rw [E.tupleChartRelationι_s]
      rfl
    · change (E.tupleChartRelationι length j i ≫
        (E.tupleChartPresentation length).t) z = _
      rw [E.tupleChartRelationι_t]
      change E.tupleChartObjectι length j
        (E.tupleSymmetricCrossLeft (length j) (length i) z) = _
      rw [hzx]
      rfl

/-- A subfamily beginning at length `d` and containing a chart of length `d`
has saturation equal to the `d`th threshold of the full presentation. -/
theorem tupleChartReindexObjectMap_saturation {I J : Type} [Finite I] [Finite J]
    (length : I → ℕ) (k : J → I)
    [IsOpenImmersion (E.tupleChartReindexObjectMap length k)]
    (d : ℕ) (hle : ∀ j, d ≤ length (k j)) (heq : ∃ j, length (k j) = d) :
    (E.tupleChartPresentation length).pointSaturationOpen
        (E.tupleChartReindexObjectMap length k ''ᵁ ⊤) =
      E.tupleChartThresholdOpen length d := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, hy, hyx⟩ :=
      ((E.tupleChartPresentation length).mem_pointSaturationOpen _ x).mp hx
    apply E.tupleChartThresholdOpen_invariant length d hyx
    obtain ⟨z, _, rfl⟩ := hy
    change z ∈ E.tupleChartReindexObjectMap length k ⁻¹ᵁ
      E.tupleChartThresholdOpen length d
    rw [E.tupleChartReindexObjectMap_threshold_preimage,
      E.tupleChartThresholdOpen_eq_top _ d hle]
    trivial
  · obtain ⟨j, hj⟩ := heq
    have hcomp : E.tupleChartObjectι length (k j) ''ᵁ ⊤ ≤
        E.tupleChartReindexObjectMap length k ''ᵁ ⊤ := by
      rintro _ ⟨z, _, rfl⟩
      refine ⟨E.tupleChartObjectι (fun j => length (k j)) j z, trivial, ?_⟩
      exact congrArg (fun f => f z) (E.tupleChartObjectι_reindexObjectMap length k j)
    have h := (E.tupleChartPresentation length).pointSaturationOpen_mono hcomp
    rw [E.tupleChartObjectι_saturation, hj] at h
    exact h

/-- The higher-tail chart covers exactly its threshold under the relation on
a lower tail, whenever the higher tail contains its lowest index. -/
theorem tupleTailToTailObjectMap_saturation (N p q : ℕ)
    (hpq : p ≤ q) (hq : q < N + 1) :
    (E.tupleTailPresentation N p).pointSaturationOpen
        (E.tupleTailToTailObjectMap N p q hpq ''ᵁ ⊤) =
      E.tupleChartThresholdOpen
        (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q := by
  apply E.tupleChartReindexObjectMap_saturation
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val)
    (tupleTailIndexMap N p q hpq) q
  · exact fun i => i.property
  · exact ⟨⟨⟨q, hq⟩, le_rfl⟩, rfl⟩

/-- In the full finite tuple presentation, the tail covers exactly the
threshold at its lowest index. -/
theorem tupleTailObjectMap_saturation (N p : ℕ) (hp : p < N + 1) :
    (E.tupleFinitePresentation N).pointSaturationOpen
        (E.tupleTailObjectMap N p ''ᵁ ⊤) =
      E.tupleChartThresholdOpen (fun i : Fin (N + 1) => i.val) p := by
  apply E.tupleChartReindexObjectMap_saturation
    (fun i : Fin (N + 1) => i.val)
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val) p
  · exact fun i => i.property
  · exact ⟨⟨⟨p, hp⟩, le_rfl⟩, rfl⟩


/-- Arrows in the lower tail whose source has a chosen lift to the higher tail. -/
abbrev tupleTailCrossCoverScheme (N p q : ℕ) (hpq : p ≤ q) : Scheme.{u} :=
  pullback (E.tupleTailPresentation N p).s (E.tupleTailToTailObjectMap N p q hpq)

/-- The chosen source lift of a cross-cover arrow. -/
abbrev tupleTailCrossCoverSource (N p q : ℕ) (hpq : p ≤ q) :
    E.tupleTailCrossCoverScheme N p q hpq ⟶ (E.tupleTailPresentation N q).U :=
  pullback.snd _ _

/-- The original lower-tail arrow underlying a cross-cover point. -/
abbrev tupleTailCrossCoverArrow (N p q : ℕ) (hpq : p ≤ q) :
    E.tupleTailCrossCoverScheme N p q hpq ⟶ (E.tupleTailPresentation N p).R :=
  pullback.fst _ _

/-- The lower-tail target of a cross-cover arrow. -/
def tupleTailCrossCoverTarget (N p q : ℕ) (hpq : p ≤ q) :
    E.tupleTailCrossCoverScheme N p q hpq ⟶ (E.tupleTailPresentation N p).U :=
  E.tupleTailCrossCoverArrow N p q hpq ≫ (E.tupleTailPresentation N p).t

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverArrow_s (N p q : ℕ) (hpq : p ≤ q) :
    E.tupleTailCrossCoverArrow N p q hpq ≫ (E.tupleTailPresentation N p).s =
      E.tupleTailCrossCoverSource N p q hpq ≫
        E.tupleTailToTailObjectMap N p q hpq :=
  pullback.condition

@[reassoc (attr := simp)]
theorem tupleTailCrossCoverArrow_t (N p q : ℕ) (hpq : p ≤ q) :
    E.tupleTailCrossCoverArrow N p q hpq ≫ (E.tupleTailPresentation N p).t =
      E.tupleTailCrossCoverTarget N p q hpq := rfl

instance tupleTailCrossCoverScheme_isAffine (N p q : ℕ) (hpq : p ≤ q) :
    IsAffine (E.tupleTailCrossCoverScheme N p q hpq) := by
  dsimp only [tupleTailCrossCoverScheme]
  infer_instance

instance tupleTailCrossCoverSource_etale (N p q : ℕ) (hpq : p ≤ q) :
    Etale (E.tupleTailCrossCoverSource N p q hpq) := by
  let := (E.tupleTailPresentation N p).etale_s
  dsimp only [tupleTailCrossCoverSource]
  infer_instance

instance tupleTailCrossCoverArrow_isOpenImmersion (N p q : ℕ) (hpq : p ≤ q) :
    IsOpenImmersion (E.tupleTailCrossCoverArrow N p q hpq) := by
  dsimp only [tupleTailCrossCoverArrow]
  infer_instance

instance tupleTailCrossCoverTarget_etale (N p q : ℕ) (hpq : p ≤ q) :
    Etale (E.tupleTailCrossCoverTarget N p q hpq) := by
  let := (E.tupleTailPresentation N p).etale_t
  dsimp only [tupleTailCrossCoverTarget]
  infer_instance

/-- The cross cover has the whole threshold as its target image. -/
theorem tupleTailCrossCoverTarget_range (N p q : ℕ)
    (hpq : p ≤ q) (hq : q < N + 1) :
    Set.range (E.tupleTailCrossCoverTarget N p q hpq) =
      (E.tupleChartThresholdOpen
        (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q :
          Set (E.tupleTailPresentation N p).U) := by
  rw [← E.tupleTailToTailObjectMap_saturation N p q hpq hq]
  apply Set.ext
  intro x
  constructor
  · rintro ⟨z, rfl⟩
    apply ((E.tupleTailPresentation N p).mem_pointSaturationOpen _ _).mpr
    refine ⟨E.tupleTailToTailObjectMap N p q hpq
      (E.tupleTailCrossCoverSource N p q hpq z), ⟨_, trivial, rfl⟩,
      E.tupleTailCrossCoverArrow N p q hpq z, ?_, rfl⟩
    exact congrArg (fun f => f z) (E.tupleTailCrossCoverArrow_s N p q hpq)
  · intro hx
    obtain ⟨y, ⟨v, _, hv⟩, r, hrs, hrt⟩ :=
      ((E.tupleTailPresentation N p).mem_pointSaturationOpen _ x).mp hx
    obtain ⟨z, hzr, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := (E.tupleTailPresentation N p).s)
      (g := E.tupleTailToTailObjectMap N p q hpq) r v (hrs.trans hv.symm)
    refine ⟨z, ?_⟩
    change (E.tupleTailPresentation N p).t
      (pullback.fst (E.tupleTailPresentation N p).s
        (E.tupleTailToTailObjectMap N p q hpq) z) = x
    rw [hzr, hrt]

/-- The affine cross scheme as a cover of the invariant threshold open. -/
def tupleTailThresholdCover (N p q : ℕ) (hpq : p ≤ q) (hq : q < N + 1) :
    E.tupleTailCrossCoverScheme N p q hpq ⟶
      (E.tupleChartThresholdOpen
        (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q).toScheme :=
  IsOpenImmersion.lift
    (E.tupleChartThresholdOpen
      (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q).ι
    (E.tupleTailCrossCoverTarget N p q hpq) (by
      rw [Scheme.Opens.range_ι, E.tupleTailCrossCoverTarget_range N p q hpq hq])

@[reassoc (attr := simp)]
theorem tupleTailThresholdCover_ι (N p q : ℕ) (hpq : p ≤ q) (hq : q < N + 1) :
    E.tupleTailThresholdCover N p q hpq hq ≫
      (E.tupleChartThresholdOpen
        (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q).ι =
      E.tupleTailCrossCoverTarget N p q hpq :=
  IsOpenImmersion.lift_fac _ _ _

instance tupleTailThresholdCover_etale (N p q : ℕ) (hpq : p ≤ q) (hq : q < N + 1) :
    Etale (E.tupleTailThresholdCover N p q hpq hq) := by
  have : Etale (E.tupleTailThresholdCover N p q hpq hq ≫
      (E.tupleChartThresholdOpen
        (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q).ι) := by
    rw [E.tupleTailThresholdCover_ι]
    infer_instance
  exact Etale.of_comp _
    (E.tupleChartThresholdOpen
      (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q).ι

instance tupleTailThresholdCover_surjective (N p q : ℕ)
    (hpq : p ≤ q) (hq : q < N + 1) :
    Surjective (E.tupleTailThresholdCover N p q hpq hq) := by
  constructor
  intro x
  have hx : x.val ∈
      (E.tupleChartThresholdOpen
        (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q :
          Set (E.tupleTailPresentation N p).U) := x.property
  rw [← E.tupleTailCrossCoverTarget_range N p q hpq hq] at hx
  obtain ⟨z, hz⟩ := hx
  refine ⟨z, ?_⟩
  apply (E.tupleChartThresholdOpen
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q).ι.isEmbedding.injective
  change (E.tupleTailThresholdCover N p q hpq hq ≫
    (E.tupleChartThresholdOpen
      (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) q).ι) z = _
  rw [E.tupleTailThresholdCover_ι]
  exact hz

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
