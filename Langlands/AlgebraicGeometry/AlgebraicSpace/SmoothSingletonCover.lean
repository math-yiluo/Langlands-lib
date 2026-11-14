import Langlands.AlgebraicGeometry.SmoothSurjectiveEtaleLocalSections

/-! # Smooth surjections generate big étale covering sieves -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- A smooth surjective morphism generates a covering sieve in the big
étale slice topology, since a surjective étale cover factors through it. -/
theorem generate_singleton_mem_etaleTopology_of_smooth {W T : Over S} (f : W ⟶ T)
    [Smooth f.left] [Surjective f.left] :
    Sieve.generate (Presieve.singleton f) ∈ Scheme.etaleTopology.over S T := by
  obtain ⟨V, e, s, he, hs, hfac⟩ :=
    Langlands.AlgebraicGeometry.smoothSurjectiveEtaleLocalSections
      W.left T.left f.left inferInstance inferInstance
  let V' : Over S := Over.mk (e ≫ T.hom)
  let e' : V' ⟶ T := Over.homMk e
  let s' : V' ⟶ W := Over.homMk s (by
    change s ≫ W.hom = e ≫ T.hom
    rw [← f.w, ← Category.assoc, hfac])
  let : Etale e'.left := he
  let : Surjective e'.left := hs
  apply (Scheme.etaleTopology.over S).superset_covering ?_
    (generate_singleton_mem_etaleTopology e')
  rw [Sieve.generate_le_iff, Presieve.singleton_le_iff]
  exact ⟨W, s', f, Presieve.singleton_self f, Over.OverMorphism.ext hfac⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
