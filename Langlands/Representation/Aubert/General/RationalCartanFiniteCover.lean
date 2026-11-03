import Langlands.Representation.Aubert.General.RationalIwasawaCartan

/-! # The finite torus product cover from actual Cartan representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Langlands.Geometry.Building Langlands.BruhatTits.Cartan
open Langlands.Plancherel.RenardCartan

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G Z : GroupScheme (Spec (CommRingCat.of F))}
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : KPApartmentData i (localFieldOrder F)) (x : D.Apartment)
  (ν : cocharacterLattice S) {j : Z ⟶ G} {s : S.toGrp ⟶ Z}
  {h : Function.Bijective (restrictionEvaluation s)}

/-- The actual Cartan section gives a finite product cover with the literal
torus image and the same geometric compact subgroup. -/
theorem exists_finite_torus_product_cover
    (hs : s ≫ j = i) (hc : SpecialCompactRenardComparison D x ν j s h) :
    ∃ E : Set (rationalPoints G), E.Finite ∧
      ∀ g : rationalPoints G,
        ∃ k₁ ∈ D.specialCompactSubgroup x, ∃ a ∈ torusPoints i, ∃ e ∈ E,
          ∃ k₂ ∈ D.specialCompactSubgroup x, g = k₁ * a * e * k₂ := by
  obtain ⟨F0, hF0, -⟩ := hc.2.2.2.2.1
  have hA := (hc.2.2.2.2.2.1 F0 hF0).1
  refine ⟨rationalPoints.map j '' F0, hF0.1.image _, fun g => ?_⟩
  obtain ⟨⟨z, hz⟩, hq⟩ :=
    (specialCompactSectionMap_bijective D x ν j s h hc.1 _ hA).2
      (DoubleCoset.mk (D.specialCompactSubgroup x) (D.specialCompactSubgroup x) g)
  obtain ⟨k₁, hk₁, k₂, hk₂, hg⟩ := DoubleCoset.eq.mp hq
  obtain ⟨c, hc0, f, hf, rfl⟩ := (mem_tildeC0 s F0 z).mp hz.1
  obtain ⟨n, rfl⟩ := (mem_C0 S s c).mp hc0
  have ht : rationalPoints.map j
      (rationalPoints.map s (uniformizerSection S (Multiplicative.ofAdd n))) ∈
      torusPoints i := by
    rw [← rationalPoints_map_comp_apply, hs]
    exact ⟨uniformizerSection S (Multiplicative.ofAdd n), rfl⟩
  refine ⟨k₁, hk₁, _, ht, rationalPoints.map j f, ⟨f, hf, rfl⟩, k₂, hk₂, ?_⟩
  simpa only [map_mul, mul_assoc] using hg

end Langlands.Aubert.General.RationalPointFamily
