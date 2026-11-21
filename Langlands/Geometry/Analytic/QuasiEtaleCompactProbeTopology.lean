import Langlands.Geometry.Analytic.LocalActionLifts

/-! # The quasi-étale topology tested by compact Hausdorff probes -/

noncomputable section

universe u v

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}

/-- The functor of underlying topological points on the quasi-étale site. -/
abbrev compactProbePointFunctor (X : LocalizedCategory.{u, v, v} (K := K)) :
    QuasiEtaleSite X ⥤ Type v :=
  MorphismProperty.Over.forget _ _ X ⋙ Over.forget X ⋙ localizedSpaceFunctor ⋙ forget TopCat

/-- A sieve contains a finite family from compact Hausdorff objects that is jointly
surjective on points. -/
def ContainsFiniteCompactSurjection {U : QuasiEtaleSite X} (S : Sieve U) : Prop :=
  ∃ (n : ℕ) (V : Fin n → QuasiEtaleSite X) (f : ∀ i, V i ⟶ U),
    (∀ i, IsCompactSpace (V i).left) ∧ (∀ i, S (f i)) ∧
      ∀ x : (compactProbePointFunctor X).obj U,
        ∃ i, x ∈ Set.range ((compactProbePointFunctor X).map (f i))

/-- A sieve covers if its pullback along every arrow from a compact Hausdorff object
contains a finite, jointly surjective family with compact Hausdorff sources. -/
def compactProbeQuasiEtaleTopology (X : LocalizedCategory.{u, v, v} (K := K)) :
    GrothendieckTopology (QuasiEtaleSite X) where
  sieves U := {S | ∀ ⦃C : QuasiEtaleSite X⦄ (g : C ⟶ U), IsCompactSpace C.left →
    ContainsFiniteCompactSurjection (S.pullback g)}
  top_mem' U := by
    intro C g hC
    refine ⟨1, fun _ => C, fun _ => 𝟙 C, fun _ => hC, fun _ => trivial, ?_⟩
    intro x
    refine ⟨0, x, ?_⟩
    exact ConcreteCategory.congr_hom ((compactProbePointFunctor X).map_id C) x
  pullback_stable' U V S f hS := by
    intro C g hC
    rw [← Sieve.pullback_comp]
    exact hS (g ≫ f) hC
  transitive' U S hS R hR := by
    classical
    intro C g hC
    obtain ⟨n, V, f, hV, hfS, hf⟩ := hS g hC
    have hRf (i : Fin n) : ContainsFiniteCompactSurjection (R.pullback (f i ≫ g)) := by
      have h := hR (hfS i) (𝟙 (V i)) (hV i)
      simpa only [Sieve.pullback_id] using h
    choose m W p hW hpR hp using hRf
    let e := Fintype.equivFin (Σ i : Fin n, Fin (m i))
    let Y i := W (e.symm i).1 (e.symm i).2
    let q (i) : Y i ⟶ C := p (e.symm i).1 (e.symm i).2 ≫ f (e.symm i).1
    refine ⟨_, Y, q, fun i => hW (e.symm i).1 (e.symm i).2, fun i => ?_, ?_⟩
    · change R ((p (e.symm i).1 (e.symm i).2 ≫ f (e.symm i).1) ≫ g)
      rw [Category.assoc]
      exact hpR (e.symm i).1 (e.symm i).2
    · intro x
      obtain ⟨i, y, hy⟩ := hf x
      obtain ⟨j, z, hz⟩ := hp i y
      refine ⟨e ⟨i, j⟩, ?_⟩
      have h := show x ∈ Set.range ((compactProbePointFunctor X).map (p i j ≫ f i)) from
        ⟨z, by simpa only [Functor.map_comp, types_comp_apply, hz] using hy⟩
      let hits (k : Σ i : Fin n, Fin (m i)) :=
        x ∈ Set.range ((compactProbePointFunctor X).map (p k.1 k.2 ≫ f k.1))
      change hits (e.symm (e ⟨i, j⟩))
      rw [e.symm_apply_apply]
      exact h

/-- The identity probe extracts a finite jointly surjective family with compact
Hausdorff sources from a covering sieve on a compact Hausdorff object. -/
theorem containsFiniteCompactSurjection_of_mem_compactProbeQuasiEtaleTopology
    {U : QuasiEtaleSite X} (hU : IsCompactSpace U.left) {S : Sieve U}
    (hS : S ∈ compactProbeQuasiEtaleTopology X U) :
    ContainsFiniteCompactSurjection S := by
  simpa only [Sieve.pullback_id] using hS (𝟙 U) hU

end Langlands.Analytic.SaturatedAtlasPresentation
