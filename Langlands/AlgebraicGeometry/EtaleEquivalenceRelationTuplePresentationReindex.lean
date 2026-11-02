import Langlands.AlgebraicGeometry.FiniteSchemeRelationReindex
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTuplePresentationFiltration

/-! # Actual chart comparisons for finite symmetric tuple subfamilies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable (E : EtaleEquivalenceRelation.{u}) [IsSeparated E.s]
  [IsAffine E.U] [IsAffine E.R] [IsClosedImmersion (prod.lift E.t E.s)]
  {I J : Type} [Finite I] [Finite J]

/-- The object map for a selected family of symmetric tuple charts. -/
abbrev tupleChartReindexObjectMap (length : I → ℕ) (k : J → I) :
    (E.tupleChartPresentation (fun j => length (k j))).U ⟶
      (E.tupleChartPresentation length).U :=
  (E.tupleChartRelation length).reindexObjectMap k

/-- The corresponding map on all cross-correspondences. -/
abbrev tupleChartReindexRelationMap (length : I → ℕ) (k : J → I) :
    (E.tupleChartPresentation (fun j => length (k j))).R ⟶
      (E.tupleChartPresentation length).R :=
  (E.tupleChartRelation length).reindexRelationMap k

@[reassoc (attr := simp)]
theorem tupleChartObjectι_reindexObjectMap (length : I → ℕ) (k : J → I) (j : J) :
    E.tupleChartObjectι (fun j => length (k j)) j ≫
      E.tupleChartReindexObjectMap length k = E.tupleChartObjectι length (k j) := by
  exact schemeSigmaReindexMap_ι _ k j

@[reassoc (attr := simp)]
theorem tupleChartRelationι_reindexRelationMap
    (length : I → ℕ) (k : J → I) (j l : J) :
    E.tupleChartRelationι (fun j => length (k j)) j l ≫
      E.tupleChartReindexRelationMap length k =
        E.tupleChartRelationι length (k j) (k l) := by
  exact schemeSigmaReindexMap_ι _ (fun p : J × J => (k p.1, k p.2)) (j, l)

@[reassoc (attr := simp)]
theorem tupleChartReindexRelationMap_t (length : I → ℕ) (k : J → I) :
    E.tupleChartReindexRelationMap length k ≫ (E.tupleChartPresentation length).t =
      (E.tupleChartPresentation (fun j => length (k j))).t ≫
        E.tupleChartReindexObjectMap length k := by
  exact (E.tupleChartRelation length).reindexRelationMap_first k

@[reassoc (attr := simp)]
theorem tupleChartReindexRelationMap_s (length : I → ℕ) (k : J → I) :
    E.tupleChartReindexRelationMap length k ≫ (E.tupleChartPresentation length).s =
      (E.tupleChartPresentation (fun j => length (k j))).s ≫
        E.tupleChartReindexObjectMap length k := by
  exact (E.tupleChartRelation length).reindexRelationMap_second k

theorem tupleChartReindexObjectMap_isOpenImmersion
    (length : I → ℕ) (k : J → I) (hk : Function.Injective k) :
    IsOpenImmersion (E.tupleChartReindexObjectMap length k) :=
  (E.tupleChartRelation length).reindexObjectMap_isOpenImmersion k hk

theorem tupleChartReindexObjectMap_isClosedImmersion
    (length : I → ℕ) (k : J → I) (hk : Function.Injective k) :
    IsClosedImmersion (E.tupleChartReindexObjectMap length k) :=
  (E.tupleChartRelation length).reindexObjectMap_isClosedImmersion k hk

theorem tupleChartReindexRelationMap_isOpenImmersion
    (length : I → ℕ) (k : J → I) (hk : Function.Injective k) :
    IsOpenImmersion (E.tupleChartReindexRelationMap length k) :=
  (E.tupleChartRelation length).reindexRelationMap_isOpenImmersion k hk

theorem tupleChartReindexRelationMap_isClosedImmersion
    (length : I → ℕ) (k : J → I) (hk : Function.Injective k) :
    IsClosedImmersion (E.tupleChartReindexRelationMap length k) :=
  (E.tupleChartRelation length).reindexRelationMap_isClosedImmersion k hk

/-- The induced relation map, with its actual chart-relation codomain. -/
abbrev tupleChartReindexChartMap (length : I → ℕ) (k : J → I) :
    (E.tupleChartPresentation (fun j => length (k j))).R ⟶
      Chart.arrows (E.tupleChartPresentation length) (E.tupleChartReindexObjectMap length k) :=
  (E.tupleChartRelation length).reindexChartMap k

@[reassoc (attr := simp)]
theorem tupleChartReindexChartMap_t (length : I → ℕ) (k : J → I) :
    E.tupleChartReindexChartMap length k ≫
      Chart.t (E.tupleChartPresentation length) (E.tupleChartReindexObjectMap length k) =
        (E.tupleChartPresentation (fun j => length (k j))).t := by
  exact (E.tupleChartRelation length).reindexChartMap_t k

@[reassoc (attr := simp)]
theorem tupleChartReindexChartMap_s (length : I → ℕ) (k : J → I) :
    E.tupleChartReindexChartMap length k ≫
      Chart.s (E.tupleChartPresentation length) (E.tupleChartReindexObjectMap length k) =
        (E.tupleChartPresentation (fun j => length (k j))).s := by
  exact (E.tupleChartRelation length).reindexChartMap_s k

@[reassoc (attr := simp)]
theorem tupleChartReindexChartMap_map (length : I → ℕ) (k : J → I) :
    E.tupleChartReindexChartMap length k ≫
      Chart.map (E.tupleChartPresentation length) (E.tupleChartReindexObjectMap length k) =
        E.tupleChartReindexRelationMap length k := by
  exact (E.tupleChartRelation length).reindexChartMap_map k

/-- The selected presentation is the actual chart of the full presentation. -/
abbrev tupleChartReindexChartIso
    (length : I → ℕ) (k : J → I) (hk : Function.Injective k) :
    (E.tupleChartPresentation (fun j => length (k j))).R ≅
      Chart.arrows (E.tupleChartPresentation length) (E.tupleChartReindexObjectMap length k) :=
  (E.tupleChartRelation length).reindexChartIso k hk

@[simp]
theorem tupleChartReindexChartIso_hom
    (length : I → ℕ) (k : J → I) (hk : Function.Injective k) :
    (E.tupleChartReindexChartIso length k hk).hom = E.tupleChartReindexChartMap length k :=
  (E.tupleChartRelation length).reindexChartIso_hom k hk

/-- Total tuple thresholds restrict to the same thresholds on a subfamily. -/
theorem tupleChartReindexObjectMap_threshold_preimage
    (length : I → ℕ) (k : J → I) (d : ℕ) :
    E.tupleChartReindexObjectMap length k ⁻¹ᵁ E.tupleChartThresholdOpen length d =
      E.tupleChartThresholdOpen (fun j => length (k j)) d := by
  apply Opens.ext
  apply Set.ext
  intro x
  obtain ⟨⟨j⟩, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (Discrete.functor (fun j => E.tupleSymmetricScheme (length (k j)))) x
  change (E.tupleChartObjectι (fun j => length (k j)) j ≫
      E.tupleChartReindexObjectMap length k) x ∈ E.tupleChartThresholdOpen length d ↔
    E.tupleChartObjectι (fun j => length (k j)) j x ∈
      E.tupleChartThresholdOpen (fun j => length (k j)) d
  rw [E.tupleChartObjectι_reindexObjectMap]
  simp only [E.tupleChartObjectι_mem_threshold_iff]

/-- Include the tuple tail in the finite family of all lengths through `N`. -/
abbrev tupleTailObjectMap (N p : ℕ) :
    (E.tupleTailPresentation N p).U ⟶ (E.tupleFinitePresentation N).U :=
  E.tupleChartReindexObjectMap (fun i : Fin (N + 1) => i.val)
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val)

/-- Include all cross-correspondences between charts in the tuple tail. -/
abbrev tupleTailRelationMap (N p : ℕ) :
    (E.tupleTailPresentation N p).R ⟶ (E.tupleFinitePresentation N).R :=
  E.tupleChartReindexRelationMap (fun i : Fin (N + 1) => i.val)
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val)

instance tupleTailObjectMap_isOpenImmersion (N p : ℕ) :
    IsOpenImmersion (E.tupleTailObjectMap N p) :=
  E.tupleChartReindexObjectMap_isOpenImmersion _ _ Subtype.val_injective

instance tupleTailObjectMap_isClosedImmersion (N p : ℕ) :
    IsClosedImmersion (E.tupleTailObjectMap N p) :=
  E.tupleChartReindexObjectMap_isClosedImmersion _ _ Subtype.val_injective

@[reassoc (attr := simp)]
theorem tupleTailRelationMap_t (N p : ℕ) :
    E.tupleTailRelationMap N p ≫ (E.tupleFinitePresentation N).t =
      (E.tupleTailPresentation N p).t ≫ E.tupleTailObjectMap N p :=
  E.tupleChartReindexRelationMap_t _ _

@[reassoc (attr := simp)]
theorem tupleTailRelationMap_s (N p : ℕ) :
    E.tupleTailRelationMap N p ≫ (E.tupleFinitePresentation N).s =
      (E.tupleTailPresentation N p).s ≫ E.tupleTailObjectMap N p :=
  E.tupleChartReindexRelationMap_s _ _

/-- The actual chart relation map for the full tuple tail. -/
abbrev tupleTailChartMap (N p : ℕ) :
    (E.tupleTailPresentation N p).R ⟶
      Chart.arrows (E.tupleFinitePresentation N) (E.tupleTailObjectMap N p) :=
  E.tupleChartReindexChartMap (fun i : Fin (N + 1) => i.val)
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val)

/-- The tail relation is isomorphic to the actual induced chart relation. -/
abbrev tupleTailChartIso (N p : ℕ) :
    (E.tupleTailPresentation N p).R ≅
      Chart.arrows (E.tupleFinitePresentation N) (E.tupleTailObjectMap N p) :=
  E.tupleChartReindexChartIso (fun i : Fin (N + 1) => i.val)
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val) Subtype.val_injective

@[simp]
theorem tupleTailChartIso_hom (N p : ℕ) :
    (E.tupleTailChartIso N p).hom = E.tupleTailChartMap N p :=
  E.tupleChartReindexChartIso_hom _ _ _

@[reassoc (attr := simp)]
theorem tupleTailChartMap_t (N p : ℕ) :
    E.tupleTailChartMap N p ≫
      Chart.t (E.tupleFinitePresentation N) (E.tupleTailObjectMap N p) =
        (E.tupleTailPresentation N p).t :=
  E.tupleChartReindexChartMap_t _ _

@[reassoc (attr := simp)]
theorem tupleTailChartMap_s (N p : ℕ) :
    E.tupleTailChartMap N p ≫
      Chart.s (E.tupleFinitePresentation N) (E.tupleTailObjectMap N p) =
        (E.tupleTailPresentation N p).s :=
  E.tupleChartReindexChartMap_s _ _

/-- The index inclusion of a higher tail into a lower tail. -/
abbrev tupleTailIndexMap (N p q : ℕ) (hpq : p ≤ q)
    (i : {i : Fin (N + 1) // q ≤ i.val}) : {i : Fin (N + 1) // p ≤ i.val} :=
  ⟨i.val, hpq.trans i.property⟩

theorem tupleTailIndexMap_injective (N p q : ℕ) (hpq : p ≤ q) :
    Function.Injective (tupleTailIndexMap N p q hpq) := by
  intro i j h
  apply Subtype.ext
  exact congrArg (fun a : {i : Fin (N + 1) // p ≤ i.val} => a.val) h

/-- The object chart map from a higher tail into a lower tail. -/
abbrev tupleTailToTailObjectMap (N p q : ℕ) (hpq : p ≤ q) :
    (E.tupleTailPresentation N q).U ⟶ (E.tupleTailPresentation N p).U :=
  E.tupleChartReindexObjectMap
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) (tupleTailIndexMap N p q hpq)

instance tupleTailToTailObjectMap_isOpenImmersion (N p q : ℕ) (hpq : p ≤ q) :
    IsOpenImmersion (E.tupleTailToTailObjectMap N p q hpq) :=
  E.tupleChartReindexObjectMap_isOpenImmersion _ _ (tupleTailIndexMap_injective N p q hpq)

/-- The chart comparison for a higher tail inside a lower tail. -/
abbrev tupleTailToTailChartIso (N p q : ℕ) (hpq : p ≤ q) :
    (E.tupleTailPresentation N q).R ≅
      Chart.arrows (E.tupleTailPresentation N p) (E.tupleTailToTailObjectMap N p q hpq) :=
  E.tupleChartReindexChartIso
    (fun i : {i : Fin (N + 1) // p ≤ i.val} => i.val.val) (tupleTailIndexMap N p q hpq)
    (tupleTailIndexMap_injective N p q hpq)

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
