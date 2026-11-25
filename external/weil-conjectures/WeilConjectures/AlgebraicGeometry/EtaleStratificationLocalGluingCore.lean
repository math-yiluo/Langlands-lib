/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Topology.Constructible

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

/-- A finite affine-local immersed partition admits a global immersed refinement with actual
factorization maps into its local representatives. Source: Stacks Project, Etale Cohomology,
Tag 03S0, locality reduction
(blueprint: theorem-comparison-constructible-sheaves).

Proof: Each affine chart is quasi-compact and therefore retrocompact in the quasi-separated
base. Its locally constructible strata are constructible in the base. Extend its partition by
its closed complement, realized by the reduced closed subscheme. Compose each local immersion
with the chart inclusion. Take the finite common refinement of the extended partitions using
intersections, represented by fibre products. Discard empty strata. Each remaining stratum
contains a point, and that point belongs to some chart. Refinement forces the whole stratum to
lie in one local part of that chart, rather than its complement. Replace its scheme
representative by its fibre product with this local representative. The resulting composite
immersion has the same image, by the image formula for scheme pullbacks, so constructibility,
disjointness and coverage are preserved. The second projection is the requested factorization.
If the base is empty, take the zero-stratum partition. -/
theorem exists_global_stratification_factoring_local
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (n : ℕ) (W : Fin n → X.Opens)
    (hW : ∀ a, IsAffineOpen (W a))
    (hcover : (⋃ a : Fin n, (W a : Set X)) = Set.univ)
    (T : ∀ a, Stratification (W a))
    (hc : ∀ a b, Topology.IsConstructible ((T a).stratum b)) :
    ∃ S : Stratification X,
      (∀ i, Topology.IsConstructible (S.stratum i)) ∧
      ∀ i, ∃ (a : Fin n) (b : Fin (T a).n)
        (q : S.domain i ⟶ (T a).domain b),
        q ≫ ((T a).immersion b ≫ (W a).ι) = S.immersion i := by
  classical
  let V (a : Fin n) : Set X := ⋃ b ∈ {b : Fin n | b < a}, (W b : Set X)
  have hVo (a : Fin n) : IsOpen (V a) :=
    isOpen_iUnion fun b ↦ isOpen_iUnion fun _ ↦ (W b).isOpen
  have hVc (a : Fin n) : Topology.IsConstructible (V a) :=
    .biUnion (Set.toFinite _) fun b _ ↦ (hW b).isCompact.isConstructible (W b).isOpen
  let I (a : Fin n) := IdealSheafData.vanishingIdeal (⟨(V a)ᶜ, (hVo a).isClosed_compl⟩)
  let c (a : Fin n) := (I a).subschemeι
  have hcr (a : Fin n) : Set.range (c a) = (V a)ᶜ := by
    simp [c, I, IdealSheafData.range_subschemeι]
  let K := (a : Fin n) × Fin (T a).n
  let e : Fin (Fintype.card K) ≃ K := (Fintype.equivFin K).symm
  let g (k : K) := (T k.1).immersion k.2 ≫ (W k.1).ι
  have hg (k : K) : IsImmersion (g k) := by
    have := (T k.1).isImmersion k.2
    dsimp [g]
    infer_instance
  let f (k : K) := pullback.fst (g k) (c k.1) ≫ g k
  have hf (k : K) : IsImmersion (f k) := by
    have := hg k
    dsimp [f, c]
    infer_instance
  have hgr (k : K) : Set.range (g k) = (W k.1).ι '' (T k.1).stratum k.2 := by
    rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, (T k.1).range_immersion]
  have hfr (k : K) : Set.range (f k) = Set.range (g k) ∩ (V k.1)ᶜ := by
    rw [Hom.comp_base, TopCat.coe_comp, Set.range_comp, Pullback.range_fst, hcr,
      Set.image_preimage_eq_inter_range, Set.inter_comm]
  have hgc (k : K) : Topology.IsConstructible (Set.range (g k)) := by
    rw [hgr]
    apply (hc k.1 k.2).image_of_isOpenEmbedding (W k.1).ι.isOpenEmbedding
    rw [Opens.range_ι]
    exact (hW k.1).isCompact.isRetrocompact (W k.1).isOpen
  have hfc (k : K) : Topology.IsConstructible (Set.range (f k)) := by
    rw [hfr]
    exact (hgc k).inter (hVc k.1).compl
  have hdis : Pairwise (fun k l : K ↦ Disjoint (Set.range (f k)) (Set.range (f l))) := by
    intro k l hkl
    apply Set.disjoint_left.mpr
    intro x hx hy
    rw [hfr] at hx hy
    rw [hgr] at hx hy
    by_cases ha : k.1 = l.1
    · rcases k with ⟨a, b⟩
      rcases l with ⟨a', b'⟩
      dsimp at ha
      subst a'
      have hb : b ≠ b' := fun h ↦ hkl (by cases h; rfl)
      obtain ⟨z, hz, hzx⟩ := hx.1
      obtain ⟨w, hw, hwx⟩ := hy.1
      have hzw : z = w := (W a).ι.isOpenEmbedding.injective (hzx.trans hwx.symm)
      exact Set.disjoint_left.mp ((T a).pairwise_disjoint_stratum hb) hz (hzw ▸ hw)
    · rcases lt_or_gt_of_ne ha with hal | hla
      · apply hy.2
        exact Set.mem_iUnion.mpr ⟨k.1, Set.mem_iUnion.mpr ⟨hal, by
          obtain ⟨z, _, rfl⟩ := hx.1
          exact z.property⟩⟩
      · apply hx.2
        exact Set.mem_iUnion.mpr ⟨l.1, Set.mem_iUnion.mpr ⟨hla, by
          obtain ⟨z, _, rfl⟩ := hy.1
          exact z.property⟩⟩
  have hcoverf : (⋃ k : K, Set.range (f k)) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have hex : ∃ a : Fin n, x ∈ (W a : Set X) :=
      Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    obtain ⟨a, hax, hmin⟩ := Set.exists_min_image {a : Fin n | x ∈ (W a : Set X)}
      (fun a ↦ a) (Set.toFinite _) hex
    let y : W a := ⟨x, hax⟩
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp
      ((T a).iUnion_stratum_eq_univ.symm ▸ Set.mem_univ y)
    refine Set.mem_iUnion.mpr ⟨⟨a, b⟩, ?_⟩
    rw [hfr, hgr]
    refine ⟨⟨y, hb, rfl⟩, ?_⟩
    intro hxV
    obtain ⟨a', hxV⟩ := Set.mem_iUnion.mp hxV
    obtain ⟨ha', hxa'⟩ := Set.mem_iUnion.mp hxV
    exact (not_lt_of_ge (hmin a' hxa')) ha'
  let S : Stratification X := {
    n := Fintype.card K
    stratum := fun i ↦ Set.range (f (e i))
    isLocallyClosed_stratum := fun i ↦ (f (e i)).isLocallyClosed_range
    isConstructible_stratum := fun i ↦ hfc (e i)
    iUnion_stratum_eq_univ := by
      rw [← hcoverf]
      exact e.surjective.iUnion_comp (fun k ↦ Set.range (f k))
    pairwise_disjoint_stratum := fun i j hij ↦ hdis (e.injective.ne hij)
    domain := fun i ↦ pullback (g (e i)) (c (e i).1)
    immersion := fun i ↦ f (e i)
    isImmersion := fun i ↦ hf (e i)
    range_immersion := fun i ↦ rfl }
  refine ⟨S, S.isConstructible_stratum, ?_⟩
  intro i
  exact ⟨(e i).1, (e i).2, pullback.fst _ _, rfl⟩

end AlgebraicGeometry.Scheme
