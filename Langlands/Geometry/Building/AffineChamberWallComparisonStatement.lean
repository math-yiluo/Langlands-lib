import Langlands.Geometry.Building.AffineChamberReflections
import Langlands.Geometry.Building.AffineReflectionGalleryGeometryStatement
import Langlands.Geometry.Building.RankZeroAffineRootSystem

/-! # Comparing chamber-simple reflections with separating wall reflections -/

noncomputable section

universe uV uA

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V : Type uV} {A : Type uA}
variable [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
variable {Ψ : Set (A →ᵃ[ℝ] ℝ)}

/-- A separating reflection is one of the actual generators of the affine Weyl group. -/
theorem reflectionSeparates_mem_affineWeylGroup {s : A ≃ᵃ[ℝ] A} {x y : A}
    (hs : reflectionSeparates Ψ s x y) : s ∈ affineWeylGroup Ψ := by
  obtain ⟨ψ, hψ, v, hv, rfl, _⟩ := hs
  exact affineReflection_mem_affineWeylGroup hψ hv

/-- The wall-reflection set already lies in the actual affine Weyl group. -/
theorem wallReflections_subset_affineWeylGroup (x : A) :
    wallReflections Ψ x ⊆ affineWeylGroup Ψ :=
  fun _ hs => reflectionSeparates_mem_affineWeylGroup hs.1

/-- Every literal chamber-simple reflection has square one. -/
theorem chamberSimpleReflection_mul_self {C : Set A} {s : affineWeylGroup Ψ}
    (hs : s ∈ chamberSimpleReflections Ψ C) : s * s = 1 := by
  obtain ⟨ψ, _, v, hv, hs⟩ := hs
  apply Subtype.ext
  change (s : A ≃ᵃ[ℝ] A) * (s : A ≃ᵃ[ℝ] A) = 1
  rw [hs]
  exact affineReflection_mul_self ψ hv.1

/-- Positivity on the nonempty chamber rules out the identity reflection. -/
theorem chamberSimpleReflection_ne_one {C : Set A} {s : affineWeylGroup Ψ}
    (hs : s ∈ chamberSimpleReflections Ψ C) : s ≠ 1 := by
  obtain ⟨ψ, hψ, v, hv, hs⟩ := hs
  obtain ⟨x, _, hx⟩ := hψ.2.2.1
  have hpos : 0 < ψ x := hψ.1.2 x (hx ▸ mem_facet_self Ψ x)
  intro h
  have he : (s : A ≃ᵃ[ℝ] A) = 1 := congrArg Subtype.val h
  have hfix : affineReflection ψ hv.1 x = x := by
    rw [← hs, he]
    rfl
  have hneg := apply_affineReflection ψ hv.1 x
  rw [hfix] at hneg
  linarith

/-- The identity is absent from the literal chamber-simple set. -/
theorem one_notMem_chamberSimpleReflections (C : Set A) :
    (1 : affineWeylGroup Ψ) ∉ chamberSimpleReflections Ψ C :=
  fun h => chamberSimpleReflection_ne_one h rfl

/-- Transfer ambient wall generation through the literal subtype inclusion.
The comparison and wall-generation equalities are explicit premises. -/
theorem closure_chamberSimpleReflections_eq_top_of_wall_generation
    (C : Set A) (x : A)
    (hcomparison : (affineWeylGroup Ψ).subtype '' chamberSimpleReflections Ψ C =
      wallReflections Ψ x)
    (hgeneration : Subgroup.closure (wallReflections Ψ x) = affineWeylGroup Ψ) :
    Subgroup.closure (chamberSimpleReflections Ψ C) = ⊤ := by
  have hmap : (Subgroup.closure (chamberSimpleReflections Ψ C)).map
      (affineWeylGroup Ψ).subtype = affineWeylGroup Ψ := by
    rw [MonoidHom.map_closure, hcomparison, hgeneration]
  apply eq_top_iff.2
  intro s _
  have hs : (s : A ≃ᵃ[ℝ] A) ∈
      (Subgroup.closure (chamberSimpleReflections Ψ C)).map
        (affineWeylGroup Ψ).subtype := by
    rw [hmap]
    exact s.property
  obtain ⟨t, ht, hts⟩ := hs
  have hts' : t = s := Subtype.ext hts
  exact hts' ▸ ht

end AffineRootSystem

/-- For an affine root system, the actual images of the positive indivisible
face-span reflections are exactly the unique separating wall reflections.
This is a geometric proof obligation, including nonreduced and rank-zero systems. -/
def AffineChamberWallComparisonStatement : Prop :=
  ∀ (V : Type uV) (A : Type uA) [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    (Ψ : Set (A →ᵃ[ℝ] ℝ)),
    AffineRootSystem.IsAffineRootSystemWithRankZero Ψ →
      ∀ x : A, (∀ ψ ∈ Ψ, ψ x ≠ 0) →
        (AffineRootSystem.affineWeylGroup Ψ).subtype ''
            AffineRootSystem.chamberSimpleReflections Ψ (AffineRootSystem.facet Ψ x) =
          AffineRootSystem.wallReflections Ψ x

end Langlands.Geometry.Building
