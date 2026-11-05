import Langlands.Algebra.FilteredRingSurjectivityStatement

/-! # Proof of finite-type surjectivity descent -/

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Algebra.FilteredRing

theorem finiteTypeSurjectivityDescent : FiniteTypeSurjectivityDescent.{u} := by
  intro J _ _ A B α cA cB hcA hcB φ hφ j₀ hft hcart hsurj
  classical
  have hcA' := isColimitOfPreserves (forget CommRingCat) hcA
  have hcB' := isColimitOfPreserves (forget CommRingCat) hcB
  let := (α.app j₀).hom.toAlgebra
  have hf : Algebra.FiniteType (A.obj j₀) (B.obj j₀) := hft
  obtain ⟨s, hs⟩ := hf.out
  have hlift (x : B.obj j₀) :
      ∃ (k : J) (r : j₀ ⟶ k), B.map r x ∈ (α.app k).hom.range := by
    obtain ⟨a, ha⟩ := hsurj (cB.ι.app j₀ x)
    obtain ⟨i, ai, hai⟩ := Types.jointly_surjective_of_isColimit hcA' a
    have heq : cB.ι.app j₀ x = cB.ι.app i (α.app i ai) := by
      calc
        _ = φ a := ha.symm
        _ = φ (cA.ι.app i ai) := congrArg φ hai.symm
        _ = cB.ι.app i (α.app i ai) := congr($(hφ i).hom ai)
    obtain ⟨k, r, t, ht⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hcB').mp heq
    refine ⟨k, r, RingHom.mem_range.mpr ⟨A.map t ai, ?_⟩⟩
    exact (congr($(α.naturality t).hom ai)).trans ht.symm
  choose k r hr using fun x : s ↦ hlift (x : B.obj j₀)
  obtain ⟨d⟩ := IsFiltered.cocone_nonempty (WidePushoutShape.wideSpan j₀ k r)
  let t := d.ι.app none
  have hs' (x : B.obj j₀) (hx : x ∈ s) :
      B.map t x ∈ (α.app d.pt).hom.range := by
    change B.map (d.ι.app none) x ∈ _
    rw [← d.w (.init ⟨x, hx⟩)]
    simp only [Functor.map_comp, CommRingCat.comp_apply]
    obtain ⟨a, ha⟩ := hr ⟨x, hx⟩
    refine RingHom.mem_range.mpr ⟨A.map (d.ι.app (some ⟨x, hx⟩)) a, ?_⟩
    exact (congr($(α.naturality (d.ι.app (some ⟨x, hx⟩))).hom a)).trans
      (congrArg (B.map (d.ι.app (some ⟨x, hx⟩))) ha)
  have hgen : Subring.closure
      (Set.range (α.app j₀) ∪ (s : Set (B.obj j₀))) = ⊤ := by
    change Subring.closure
      (Set.range (algebraMap (A.obj j₀) (B.obj j₀)) ∪ (s : Set (B.obj j₀))) = ⊤
    rw [← Algebra.adjoin_eq_ring_closure]
    rw [hs]
    exact Algebra.top_toSubring
  have hpre : (⊤ : Subring (B.obj j₀)) ≤
      ((α.app d.pt).hom.range).comap (B.map t).hom := by
    rw [← hgen, Subring.closure_le]
    rintro x (⟨a, rfl⟩ | hx)
    · exact RingHom.mem_range.mpr ⟨A.map t a, congr($(α.naturality t).hom a)⟩
    · exact hs' x hx
  refine ⟨d.pt, t, RingHom.range_eq_top.mp ?_⟩
  apply top_unique
  rw [← CommRingCat.closure_range_union_range_eq_top_of_isPushout (hcart t),
    Subring.closure_le]
  rintro x (⟨a, rfl⟩ | hx)
  · exact hpre (by trivial)
  · exact hx

end Langlands.Algebra.FilteredRing
