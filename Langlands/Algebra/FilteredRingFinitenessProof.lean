import Langlands.Algebra.FilteredRingFinitenessStatement

/-! # Proof of finite-type finiteness descent -/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.FilteredRing

section

variable {J : Type u} [SmallCategory J] [IsFiltered J]
  (A B : J ⥤ CommRingCat.{u}) (α : A ⟶ B)
  (cA : Cocone A) (cB : Cocone B) (hcA : IsColimit cA) (hcB : IsColimit cB)
  (φ : cA.pt ⟶ cB.pt)
  (hφ : ∀ j, cA.ι.app j ≫ φ = α.app j ≫ cB.ι.app j)

include hcA in
omit B α cB hcB φ hφ in
lemma exists_monic_polynomial_lift (j₀ : J) (p : Polynomial cA.pt) (hp : p.Monic) :
    ∃ (k : J) (_r : j₀ ⟶ k) (q : Polynomial (A.obj k)),
      q.map (cA.ι.app k).hom = p ∧ q.Monic := by
  classical
  have hcA' := isColimitOfPreserves (forget CommRingCat) hcA
  choose i a ha using fun n : p.support ↦
    Types.jointly_surjective_of_isColimit hcA' (p.coeff n)
  let k (n : p.support) := IsFiltered.max j₀ (i n)
  let r (n : p.support) : j₀ ⟶ k n := IsFiltered.leftToMax j₀ (i n)
  let z (n : p.support) : A.obj (k n) := A.map (IsFiltered.rightToMax j₀ (i n)) (a n)
  have hz (n : p.support) : cA.ι.app (k n) (z n) = p.coeff n := by
    exact (congr($(cA.w (IsFiltered.rightToMax j₀ (i n))).hom (a n))).trans (ha n)
  obtain ⟨d⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan j₀ k r)
  have hl : p ∈ Polynomial.lifts (cA.ι.app d.pt).hom := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ∈ p.support
    · refine ⟨A.map (d.ι.app (some ⟨n, hn⟩)) (z ⟨n, hn⟩), ?_⟩
      exact (congr($(cA.w (d.ι.app (some ⟨n, hn⟩))).hom (z ⟨n, hn⟩))).trans
        (hz ⟨n, hn⟩)
    · have hz : p.coeff n = 0 := by
        simpa only [Polynomial.mem_support_iff, not_not] using hn
      exact ⟨0, (map_zero _).trans hz.symm⟩
  obtain ⟨q, hq, _, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hp
  exact ⟨d.pt, d.ι.app none, q, hq, hqm⟩

include hcA hcB hφ in
lemma exists_integral_element_stage (j₀ : J) (x : B.obj j₀)
    (hx : φ.hom.IsIntegralElem (cB.ι.app j₀ x)) :
    ∃ (k : J) (r : j₀ ⟶ k), (α.app k).hom.IsIntegralElem (B.map r x) := by
  obtain ⟨p, hp, he⟩ := hx
  obtain ⟨k, r, q, hq, hqm⟩ := exists_monic_polynomial_lift A cA hcA j₀ p hp
  have hw : (cB.ι.app k).hom.comp (α.app k).hom =
      φ.hom.comp (cA.ι.app k).hom := by
    exact congrArg CommRingCat.Hom.hom (hφ k).symm
  have heq : cB.ι.app k (q.eval₂ (α.app k).hom (B.map r x)) = cB.ι.app k 0 := by
    rw [Polynomial.hom_eval₂, hw]
    have hr : cB.ι.app k (B.map r x) = cB.ι.app j₀ x :=
      congr($(cB.w r).hom x)
    rw [hr, ← Polynomial.eval₂_map, hq, he, map_zero]
  have hcB' := isColimitOfPreserves (forget CommRingCat) hcB
  obtain ⟨l, s, t, hs⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hcB').mp heq
  refine ⟨l, r ≫ s, q.map (A.map s).hom, hqm.map _, ?_⟩
  have hn : (α.app l).hom.comp (A.map s).hom =
      (B.map s).hom.comp (α.app k).hom :=
    congrArg CommRingCat.Hom.hom (α.naturality s)
  simp only [Functor.map_comp, CommRingCat.comp_apply]
  rw [Polynomial.eval₂_map, hn, ← Polynomial.hom_eval₂]
  exact hs.trans ((B.map t).hom.map_zero)

end

theorem finiteTypeFinitenessDescent : FiniteTypeFinitenessDescent.{u} := by
  intro J _ _ A B α cA cB hcA hcB φ hφ j₀ hft hcart hfin
  classical
  let := (α.app j₀).hom.toAlgebra
  have hf : Algebra.FiniteType (A.obj j₀) (B.obj j₀) := hft
  obtain ⟨s, hs⟩ := hf.out
  choose k r hr using fun x : s ↦
    exists_integral_element_stage A B α cA cB hcA hcB φ hφ j₀ x
      (hfin.to_isIntegral _)
  obtain ⟨d⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan j₀ k r)
  let t : j₀ ⟶ d.pt := d.ι.app none
  let := (α.app d.pt).hom.toAlgebra
  have hs' (x : B.obj j₀) (hx : x ∈ s) :
      IsIntegral (A.obj d.pt) (B.map t x) := by
    let := (α.app (k ⟨x, hx⟩)).hom.toAlgebra
    let v : k ⟨x, hx⟩ ⟶ d.pt := d.ι.app (some ⟨x, hx⟩)
    have ht : r ⟨x, hx⟩ ≫ v = t := d.w (.init (⟨x, hx⟩ : s))
    rw [← ht]
    simp only [Functor.map_comp, CommRingCat.comp_apply]
    exact IsIntegral.map_of_comp_eq
      (A.map v).hom (B.map v).hom
      (congrArg CommRingCat.Hom.hom (α.naturality v))
      (hr ⟨x, hx⟩)
  let T := Algebra.adjoin (A.obj d.pt) (B.map t '' (s : Set (B.obj j₀)))
  have hgen : Subring.closure
      (Set.range (α.app j₀) ∪ (s : Set (B.obj j₀))) = ⊤ := by
    change Subring.closure
      (Set.range (algebraMap (A.obj j₀) (B.obj j₀)) ∪ (s : Set (B.obj j₀))) = ⊤
    rw [← Algebra.adjoin_eq_ring_closure, hs]
    exact Algebra.top_toSubring
  have hpre : (⊤ : Subring (B.obj j₀)) ≤ T.toSubring.comap (B.map t).hom := by
    rw [← hgen, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | hx)
    · change B.map t (α.app j₀ a) ∈ T
      have he : α.app d.pt (A.map t a) = B.map t (α.app j₀ a) :=
        congr($(α.naturality t).hom a)
      exact he ▸ T.algebraMap_mem (A.map t a)
    · exact Algebra.subset_adjoin (Set.mem_image_of_mem (B.map t) hx)
  have htopring : T.toSubring = ⊤ := by
    apply top_unique
    rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout (hcart t),
      Subring.closure_le]
    rintro x (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · exact hpre (by trivial)
    · exact T.algebraMap_mem a
  have htop : T = ⊤ := by
    apply Subalgebra.toSubring_injective
    exact htopring.trans Algebra.top_toSubring.symm
  have hfinite : Module.Finite (A.obj d.pt) T :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (s.finite_toSet.image (B.map t)) (by
      rintro _ ⟨x, hx, rfl⟩
      exact hs' x hx)
  rw [htop] at hfinite
  have := hfinite
  exact ⟨d.pt, t, Module.Finite.equiv
    (Subalgebra.topEquiv (R := A.obj d.pt) (A := B.obj d.pt)).toLinearEquiv⟩

end Langlands.Algebra.FilteredRing
