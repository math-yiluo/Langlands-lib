import Langlands.GroupScheme.SimplyConnected.AlmostSimpleSubproductGalois

/-! # Transitivity of the canonical action on actual almost-simple factors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct

section SubproductExtremes

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (D : SimplyConnectedAlmostSimpleProduct G)

/-- Noncommutative factors cannot occur in a subproduct with trivial range. -/
theorem eq_empty_of_range_subproductInclusion_eq_bot (s : Set D.Index)
    (h : SubgroupFunctor.range (D.subproductInclusion s) = ⊥) : s = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hle : SubgroupFunctor.range (D.inclusion i) ≤ ⊥ := by
    rw [← h]
    exact (D.range_subproductInclusion_le_iff s _).mp le_rfl i hi
  apply (D.isAlmostSimple i).noncommutative
  intro T x y
  have hall (z : T ⟶ (D.factor i).X) : z = 1 := by
    have hz := hle T (SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩)
    change z ≫ (D.inclusion i).hom.hom = 1 at hz
    have he := congrArg (fun v => v ≫ (D.projection i).hom.hom) hz
    simpa only [D.inclusion_projection_points_self, MonObj.one_comp] using he
  rw [hall x, hall y]

/-- A subproduct with full range includes every noncommutative factor. -/
theorem eq_univ_of_range_subproductInclusion_eq_top (s : Set D.Index)
    (h : SubgroupFunctor.range (D.subproductInclusion s) = ⊤) : s = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro i
  by_contra hi
  apply (D.isAlmostSimple i).noncommutative
  intro T x y
  have hall (z : T ⟶ (D.factor i).X) : z = 1 := by
    have hz : z ≫ (D.inclusion i).hom.hom ∈
        (SubgroupFunctor.range (D.subproductInclusion s)).carrier T := by
      rw [h]
      exact Subgroup.mem_top _
    have he := (D.mem_range_subproductInclusion_iff s _).mp hz i hi
    simpa only [D.inclusion_projection_points_self] using he
  rw [hall x, hall y]

end SubproductExtremes

section Galois

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    [IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k L)).obj G).X.hom]
    (D : SimplyConnectedAlmostSimpleProduct
      ((GroupScheme.baseChange (algebraBaseMap k L)).obj G))

/-- The orbit of a chosen actual almost-simple factor under canonical transport. -/
def galoisFactorOrbit (i : D.Index) : Set D.Index :=
  Set.range (fun σ : L ≃ₐ[k] L => D.galoisFactorIndex σ i)

@[simp] theorem mem_galoisFactorOrbit_self (i : D.Index) : i ∈ D.galoisFactorOrbit i :=
  ⟨1, D.galoisFactorIndex_one i⟩

/-- Each canonical factor orbit is invariant as an actual index subset. -/
theorem galoisFactorOrbit_image (σ : L ≃ₐ[k] L) (i : D.Index) :
    D.galoisFactorIndex σ '' D.galoisFactorOrbit i = D.galoisFactorOrbit i := by
  apply Set.Subset.antisymm
  · rintro j ⟨_, ⟨τ, rfl⟩, rfl⟩
    exact ⟨σ * τ, D.galoisFactorIndex_mul σ τ i⟩
  · rintro j ⟨τ, rfl⟩
    refine ⟨D.galoisFactorIndex (σ⁻¹ * τ) i, ⟨σ⁻¹ * τ, rfl⟩, ?_⟩
    rw [← D.galoisFactorIndex_mul, mul_inv_cancel_left]

/-- Almost-simplicity over the original field rules out a proper nonempty
invariant set of actual almost-simple factors over a Galois extension. -/
theorem eq_empty_or_univ_of_galoisFactorIndex_invariant
    [IsAffineHom G.X.hom] [IsGalois k L] (hG : IsAlmostSimple G)
    (s : Set D.Index) (hs : ∀ σ : L ≃ₐ[k] L, D.galoisFactorIndex σ '' s = s) :
    s = ∅ ∨ s = Set.univ := by
  obtain ⟨H, j, r, _, hj, hsm, hc, hn, hr⟩ :=
    D.exists_smoothConnectedNormal_subproduct_descent s hs
  have he : SubgroupFunctor.range (D.subproductInclusion s) =
      (SubgroupFunctor.range j).baseChange (algebraBaseMap k L) := by
    rw [← SubgroupFunctor.range_baseChangeHom, hr, SubgroupFunctor.range_iso_comp]
  rcases hG.normalSubgroup_trivial_or_full H j hj hsm hc hn with hb | ht
  · left
    apply D.eq_empty_of_range_subproductInclusion_eq_bot
    rw [he, hb, SubgroupFunctor.bot_baseChange]
  · right
    apply D.eq_univ_of_range_subproductInclusion_eq_top
    rw [he, ht, SubgroupFunctor.top_baseChange]

/-- Canonical Galois transport is transitive on the actual product factors of
an almost-simple ground-field group. -/
theorem exists_galoisFactorIndex_eq
    [IsAffineHom G.X.hom] [IsGalois k L] (hG : IsAlmostSimple G)
    (i j : D.Index) : ∃ σ : L ≃ₐ[k] L, D.galoisFactorIndex σ i = j := by
  have horbit : D.galoisFactorOrbit i = Set.univ := by
    rcases D.eq_empty_or_univ_of_galoisFactorIndex_invariant hG
        (D.galoisFactorOrbit i) (fun σ => D.galoisFactorOrbit_image σ i) with he | hu
    · have hi := D.mem_galoisFactorOrbit_self i
      rw [he] at hi
      exact False.elim hi
    · exact hu
  have hj : j ∈ D.galoisFactorOrbit i := by rw [horbit]; trivial
  exact hj

end Galois

end Langlands.GroupScheme.SimplyConnectedAlmostSimpleProduct
