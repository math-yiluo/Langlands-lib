import Langlands.AlgebraicGeometry.LinearSystem.ChartMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Chart maps and graded-ring morphisms -/

noncomputable section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization

namespace Langlands.AlgebraicGeometry.LinearSystem

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {σ τ A B : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- Evaluate degree-zero fractions by first applying the graded localization map. -/
def awayLiftAlongGradedMap {R : Type*} [CommRing R]
    (f : 𝒜 →+*ᵍ ℬ) (e : B →+* R) (t : A) (hu : IsUnit (e (f t))) :
    Away 𝒜 t →+* R :=
  (awayLift ℬ e (f t) hu).comp (Away.map f t)

/-- Evaluating a degree-zero fraction after a graded map agrees with evaluating
the corresponding fraction in the image chart. -/
lemma awayLift_comp_gradedMap {R : Type*} [CommRing R]
    (f : 𝒜 →+*ᵍ ℬ) (e : B →+* R) {t : A} {d : ℕ}
    (ht : t ∈ 𝒜 d) (hu : IsUnit (e (f t))) :
    (awayLift ℬ e (f t) hu).comp (Away.map f t) =
      awayLift 𝒜 (e.comp f.toRingHom) t hu := by
  ext x
  obtain ⟨m, a, ha, rfl⟩ := Away.mk_surjective 𝒜 ht x
  simp only [RingHom.comp_apply, Away.map_mk, awayLift_mk,
    GradedRingHom.coe_toRingHom]

/-- The fraction evaluation through a graded map equals composite evaluation. -/
lemma awayLiftAlongGradedMap_eq {R : Type*} [CommRing R]
    (f : 𝒜 →+*ᵍ ℬ) (e : B →+* R) {t : A} {d : ℕ}
    (ht : t ∈ 𝒜 d) (hu : IsUnit (e (f t))) :
    awayLiftAlongGradedMap 𝒜 ℬ f e t hu =
      awayLift 𝒜 (e.comp f.toRingHom) t hu :=
  awayLift_comp_gradedMap 𝒜 ℬ f e ht hu

/-- A chart map followed by the actual `Proj.map` is the chart map of the
composite evaluation. -/
lemma chartMap_comp_projMap {T : Scheme.{u}}
    (f : 𝒜 →+*ᵍ ℬ)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (e : B →+* Γ(T, ⊤)) {t : A} {d : ℕ}
    (ht : t ∈ 𝒜 d) (hd : 0 < d) (hu : IsUnit (e (f t))) :
    chartMap ℬ e (t := f t) (d := d) (f.map_mem ht) hd hu ≫
        Proj.map (𝒜 := 𝒜) (ℬ := ℬ) f hf =
      chartMap 𝒜 (e.comp f.toRingHom) ht hd hu := by
  simp only [chartMap, Category.assoc]
  rw [Proj.awayι_comp_map f hf hd t ht, ← Spec.map_comp_assoc,
    ← CommRingCat.ofHom_comp, awayLift_comp_gradedMap 𝒜 ℬ f e ht hu]

end Langlands.AlgebraicGeometry.LinearSystem
