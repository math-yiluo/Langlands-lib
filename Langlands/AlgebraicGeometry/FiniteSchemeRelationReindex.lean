import Langlands.AlgebraicGeometry.FiniteSchemeRelation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationChart

/-! # Subfamilies of finite scheme presentations as actual charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry

/-- The map of scheme coproducts induced by a map of indices. -/
def schemeSigmaReindexMap {I J : Type} (X : I → Scheme.{u}) (k : J → I) :
    (∐ fun j => X (k j)) ⟶ ∐ X :=
  Sigma.desc fun j => Sigma.ι X (k j)

@[reassoc (attr := simp)]
theorem schemeSigmaReindexMap_ι {I J : Type} (X : I → Scheme.{u})
    (k : J → I) (j : J) :
    Sigma.ι (fun j => X (k j)) j ≫ schemeSigmaReindexMap X k = Sigma.ι X (k j) := by
  simp [schemeSigmaReindexMap]

theorem mem_range_schemeSigmaReindexMap_iff {I J : Type} (X : I → Scheme.{u})
    (k : J → I) (x : (∐ X : Scheme.{u})) :
    x ∈ Set.range (schemeSigmaReindexMap X k) ↔
      ∃ j, x ∈ Set.range (Sigma.ι X (k j)) := by
  constructor
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨j⟩, y, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
      (Discrete.functor (fun j => X (k j))) y
    exact ⟨j, y, by simp [← Scheme.Hom.comp_apply]⟩
  · rintro ⟨j, y, rfl⟩
    exact ⟨Sigma.ι (fun j => X (k j)) j y, by simp [← Scheme.Hom.comp_apply]⟩

/-- An injective selection of components is an open immersion. -/
theorem schemeSigmaReindexMap_isOpenImmersion {I J : Type} (X : I → Scheme.{u})
    (k : J → I) (hk : Function.Injective k) :
    IsOpenImmersion (schemeSigmaReindexMap X k) := by
  apply isOpenImmersion_sigmaDesc
  intro j l hjl
  apply Set.disjoint_iff_forall_ne.mpr
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ heq
  exact hjl (hk (congrArg Sigma.fst ((sigmaι_eq_iff X (k j) (k l) x y).mp heq)))

/-- An injective selection from a finite family is also a closed immersion. -/
theorem schemeSigmaReindexMap_isClosedImmersion {I J : Type} [Finite I] [Finite J]
    (X : I → Scheme.{u}) (k : J → I) (hk : Function.Injective k) :
    IsClosedImmersion (schemeSigmaReindexMap X k) := by
  let := schemeSigmaReindexMap_isOpenImmersion X k hk
  apply isClosedImmersion_of_finite_coproduct
    (X := fun j => X (k j)) (schemeSigmaReindexMap X k)
  · intro j
    rw [schemeSigmaReindexMap_ι]
    exact isClosedImmersion_sigma_ι X (k j)
  · exact (schemeSigmaReindexMap X k).isOpenEmbedding.injective

namespace FiniteSchemeRelation

variable {I J : Type} (D : FiniteSchemeRelation.{u} I) (k : J → I)

/-- The relation data on a selected family of charts. -/
def reindex : FiniteSchemeRelation.{u} J where
  U j := D.U (k j)
  R j l := D.R (k j) (k l)
  t j l := D.t (k j) (k l)
  s j l := D.s (k j) (k l)
  closed_lift j l := D.closed_lift (k j) (k l)
  etale_t j l := D.etale_t (k j) (k l)
  etale_s j l := D.etale_s (k j) (k l)
  refl j := D.refl (k j)
  symm j l := D.symm (k j) (k l)
  trans j l m := D.trans (k j) (k l) (k m)

variable [Finite I] [Finite J]

/-- Include the selected object components in the full presentation. -/
abbrev reindexObjectMap : (D.reindex k).objectScheme ⟶ D.objectScheme :=
  schemeSigmaReindexMap D.U k

/-- Include all selected pairs of relation components in the full relation. -/
abbrev reindexRelationMap : (D.reindex k).relationScheme ⟶ D.relationScheme :=
  schemeSigmaReindexMap (fun p : I × I => D.R p.1 p.2)
    (fun p : J × J => (k p.1, k p.2))

omit [Finite I] [Finite J] in
@[reassoc (attr := simp)]
theorem reindexRelationMap_first :
    D.reindexRelationMap k ≫ D.first = (D.reindex k).first ≫ D.reindexObjectMap k := by
  apply Sigma.hom_ext
  intro p
  simp [reindexRelationMap, reindexObjectMap, reindex, first, schemeSigmaReindexMap]

omit [Finite I] [Finite J] in
@[reassoc (attr := simp)]
theorem reindexRelationMap_second :
    D.reindexRelationMap k ≫ D.second = (D.reindex k).second ≫ D.reindexObjectMap k := by
  apply Sigma.hom_ext
  intro p
  simp [reindexRelationMap, reindexObjectMap, reindex, second, schemeSigmaReindexMap]

omit [Finite I] [Finite J] in
theorem reindexObjectMap_isOpenImmersion (hk : Function.Injective k) :
    IsOpenImmersion (D.reindexObjectMap k) :=
  schemeSigmaReindexMap_isOpenImmersion D.U k hk

theorem reindexObjectMap_isClosedImmersion (hk : Function.Injective k) :
    IsClosedImmersion (D.reindexObjectMap k) :=
  schemeSigmaReindexMap_isClosedImmersion D.U k hk

omit [Finite I] [Finite J] in
theorem reindexRelationMap_isOpenImmersion (hk : Function.Injective k) :
    IsOpenImmersion (D.reindexRelationMap k) := by
  apply schemeSigmaReindexMap_isOpenImmersion
  intro p q hpq
  exact Prod.ext (hk (congrArg Prod.fst hpq)) (hk (congrArg Prod.snd hpq))

theorem reindexRelationMap_isClosedImmersion (hk : Function.Injective k) :
    IsClosedImmersion (D.reindexRelationMap k) := by
  apply schemeSigmaReindexMap_isClosedImmersion
  intro p q hpq
  exact Prod.ext (hk (congrArg Prod.fst hpq)) (hk (congrArg Prod.snd hpq))

omit [Finite I] [Finite J] in
/-- A relation point lies in the selected relation exactly when both
of its endpoints lie in the selected object family. -/
theorem mem_range_reindexRelationMap_iff (z : D.relationScheme) :
    z ∈ Set.range (D.reindexRelationMap k) ↔
      D.first z ∈ Set.range (D.reindexObjectMap k) ∧
      D.second z ∈ Set.range (D.reindexObjectMap k) := by
  constructor
  · rintro ⟨z, rfl⟩
    constructor
    · refine ⟨(D.reindex k).first z, ?_⟩
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun f => f z) (D.reindexRelationMap_first k).symm
    · refine ⟨(D.reindex k).second z, ?_⟩
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun f => f z) (D.reindexRelationMap_second k).symm
  · intro h
    obtain ⟨⟨⟨i, j⟩⟩, z, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
      (Discrete.functor (fun p : I × I => D.R p.1 p.2)) z
    have ht : Sigma.ι D.U i (D.t i j z) ∈ Set.range (D.reindexObjectMap k) := by
      simpa only [← Scheme.Hom.comp_apply, D.ι_first] using h.1
    have hs : Sigma.ι D.U j (D.s i j z) ∈ Set.range (D.reindexObjectMap k) := by
      simpa only [← Scheme.Hom.comp_apply, D.ι_second] using h.2
    obtain ⟨a, x, hx⟩ := (mem_range_schemeSigmaReindexMap_iff D.U k _).mp ht
    obtain ⟨b, y, hy⟩ := (mem_range_schemeSigmaReindexMap_iff D.U k _).mp hs
    have hi : i = k a :=
      (congrArg Sigma.fst ((sigmaι_eq_iff D.U (k a) i x _).mp hx)).symm
    have hj : j = k b :=
      (congrArg Sigma.fst ((sigmaι_eq_iff D.U (k b) j y _).mp hy)).symm
    subst i
    subst j
    apply (mem_range_schemeSigmaReindexMap_iff
      (fun p : I × I => D.R p.1 p.2) (fun p : J × J => (k p.1, k p.2)) _).mpr
    exact ⟨(a, b), z, rfl⟩

omit [Finite I] [Finite J] in
/-- The selected relation is the scheme-theoretic pullback along both
object endpoints. This is the chart comparison, rather than a source square. -/
theorem reindex_isPullback_pair (hk : Function.Injective k) :
    IsPullback (D.reindexRelationMap k)
      (prod.lift (D.reindex k).first (D.reindex k).second)
      (prod.lift D.first D.second)
      (prod.map (D.reindexObjectMap k) (D.reindexObjectMap k)) := by
  let := D.reindexObjectMap_isOpenImmersion k hk
  let := D.reindexRelationMap_isOpenImmersion k hk
  refine IsPullback.mk' (by ext <;> simp) ?_ ?_
  · intro T a b hab _
    exact (cancel_mono (D.reindexRelationMap k)).mp hab
  · intro T r v hw
    have ht : r ≫ D.first = (v ≫ prod.fst) ≫ D.reindexObjectMap k := by
      simpa using congrArg (· ≫ prod.fst) hw
    have hs : r ≫ D.second = (v ≫ prod.snd) ≫ D.reindexObjectMap k := by
      simpa using congrArg (· ≫ prod.snd) hw
    have hrange : Set.range r ⊆ Set.range (D.reindexRelationMap k) := by
      rintro _ ⟨x, rfl⟩
      apply (D.mem_range_reindexRelationMap_iff k _).mpr
      constructor
      · exact ⟨(v ≫ prod.fst) x, by
          simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f x) ht.symm⟩
      · exact ⟨(v ≫ prod.snd) x, by
          simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f x) hs.symm⟩
    let l := IsOpenImmersion.lift (D.reindexRelationMap k) r hrange
    have hl : l ≫ D.reindexRelationMap k = r := IsOpenImmersion.lift_fac _ _ _
    refine ⟨l, hl, ?_⟩
    apply prod.hom_ext
    · apply (cancel_mono (D.reindexObjectMap k)).mp
      simp only [Category.assoc, prod.lift_fst]
      rw [← D.reindexRelationMap_first, ← Category.assoc, hl]
      exact ht
    · apply (cancel_mono (D.reindexObjectMap k)).mp
      simp only [Category.assoc, prod.lift_snd]
      rw [← D.reindexRelationMap_second, ← Category.assoc, hl]
      exact hs

/-- The actual map from the selected relation to the induced chart relation. -/
def reindexChartMap :
    (D.reindex k).relationScheme ⟶
      EtaleEquivalenceRelation.Chart.arrows D.toEtaleEquivalenceRelation
        (D.reindexObjectMap k) :=
  EtaleEquivalenceRelation.Chart.lift D.toEtaleEquivalenceRelation
    (D.reindexObjectMap k) (D.reindex k).first (D.reindex k).second
    (D.reindexRelationMap k) (D.reindexRelationMap_first k)
    (D.reindexRelationMap_second k)

omit [Finite J] in
@[reassoc (attr := simp)]
theorem reindexChartMap_t :
    D.reindexChartMap k ≫ EtaleEquivalenceRelation.Chart.t
      D.toEtaleEquivalenceRelation (D.reindexObjectMap k) = (D.reindex k).first := by
  exact EtaleEquivalenceRelation.Chart.lift_t _ _ _ _ _ _ _

omit [Finite J] in
@[reassoc (attr := simp)]
theorem reindexChartMap_s :
    D.reindexChartMap k ≫ EtaleEquivalenceRelation.Chart.s
      D.toEtaleEquivalenceRelation (D.reindexObjectMap k) = (D.reindex k).second := by
  exact EtaleEquivalenceRelation.Chart.lift_s _ _ _ _ _ _ _

omit [Finite J] in
@[reassoc (attr := simp)]
theorem reindexChartMap_map :
    D.reindexChartMap k ≫ EtaleEquivalenceRelation.Chart.map
      D.toEtaleEquivalenceRelation (D.reindexObjectMap k) = D.reindexRelationMap k := by
  exact EtaleEquivalenceRelation.Chart.lift_map _ _ _ _ _ _ _

/-- The relation scheme of the selected presentation is isomorphic to the
actual relation scheme induced from the full presentation. -/
def reindexChartIso (hk : Function.Injective k) :
    (D.reindex k).relationScheme ≅
      EtaleEquivalenceRelation.Chart.arrows D.toEtaleEquivalenceRelation
        (D.reindexObjectMap k) :=
  (D.reindex_isPullback_pair k hk).isoIsPullback _ _
    (EtaleEquivalenceRelation.Chart.isPullback_pair
      D.toEtaleEquivalenceRelation (D.reindexObjectMap k))

omit [Finite J] in
@[simp]
theorem reindexChartIso_hom (hk : Function.Injective k) :
    (D.reindexChartIso k hk).hom = D.reindexChartMap k := by
  have h := (D.reindex_isPullback_pair k hk).isoIsPullback_hom_snd _ _
    (EtaleEquivalenceRelation.Chart.isPullback_pair
      D.toEtaleEquivalenceRelation (D.reindexObjectMap k))
  apply EtaleEquivalenceRelation.Chart.hom_ext
  · simpa [reindexChartIso] using congrArg (· ≫ prod.fst) h
  · simpa [reindexChartIso] using congrArg (· ≫ prod.snd) h

end FiniteSchemeRelation
end Langlands.AlgebraicGeometry
