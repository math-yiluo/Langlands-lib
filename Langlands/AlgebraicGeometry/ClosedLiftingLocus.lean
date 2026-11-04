import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-! # Closed loci of liftings and of equalities over a field -/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ClosedLiftingLocus

variable {k : Type u} [Field k]

/-- For an affine scheme `X` over a field, a closed immersion `j : A ⟶ B` and a
morphism `Ψ : X × Y ⟶ B`, the maps `t : T ⟶ Y` for which `Ψ ∘ (X × t)` lifts
through `j` are exactly the maps factoring through one closed subscheme of `Y`. -/
theorem exists_lifting_locus (X Y A B : Over (Spec (CommRingCat.of k)))
    [IsAffineHom X.hom] (j : A ⟶ B) (hj : IsClosedImmersion j.left) (Ψ : X ⊗ Y ⟶ B) :
    ∃ (Z : Over (Spec (CommRingCat.of k))) (i : Z ⟶ Y), IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ Y),
        (∃ z : T ⟶ Z, z ≫ i = t) ↔ ∃ σ : X ⊗ T ⟶ A, σ ≫ j = (X ◁ t) ≫ Ψ := by
  let D : Over (Spec (CommRingCat.of k)) := pullback j Ψ
  let d : D ⟶ X ⊗ Y := pullback.snd j Ψ
  have hd : IsClosedImmersion d.left :=
    MorphismProperty.of_isPullback
      ((IsPullback.of_hasPullback j Ψ).map (Over.forget (Spec (CommRingCat.of k)))) hj
  have hcoords : Langlands.AlgebraicGeometry.HasFpqcProjectiveCoordinateModule X :=
    ⟨CommAlgCat.of (CommRingCat.of k) k, inferInstance, inferInstance⟩
  obtain ⟨Z, i, hi, hZ⟩ :=
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus
      (CommRingCat.of k) X inferInstance inferInstance hcoords Y D d hd
  refine ⟨Z, i, hi, fun T t => (hZ T t).trans ?_⟩
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q ≫ pullback.fst j Ψ, ?_⟩
    rw [Category.assoc, pullback.condition, ← Category.assoc, hq]
  · rintro ⟨σ, hσ⟩
    exact ⟨pullback.lift σ (X ◁ t) hσ, pullback.lift_snd _ _ _⟩

/-- For an affine scheme `X` over a field and a separated target `G`, the maps
`t : T ⟶ Y` on which two morphisms `X × Y ⟶ G` agree after `X × t` are exactly the
maps factoring through one closed subscheme of `Y`. -/
theorem exists_equalizer_locus (X Y G : Over (Spec (CommRingCat.of k)))
    [IsAffineHom X.hom] [IsSeparated G.hom] (f₁ f₂ : X ⊗ Y ⟶ G) :
    ∃ (Z : Over (Spec (CommRingCat.of k))) (i : Z ⟶ Y), IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec (CommRingCat.of k))) (t : T ⟶ Y),
        (∃ z : T ⟶ Z, z ≫ i = t) ↔ (X ◁ t) ≫ f₁ = (X ◁ t) ≫ f₂ := by
  have hcoords : Langlands.AlgebraicGeometry.HasFpqcProjectiveCoordinateModule X :=
    ⟨CommAlgCat.of (CommRingCat.of k) k, inferInstance, inferInstance⟩
  obtain ⟨Z, i, hi, hZ⟩ :=
    Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof.closedFactorizationLocus
      (CommRingCat.of k) X inferInstance inferInstance hcoords Y (equalizer f₁ f₂)
      (equalizer.ι f₁ f₂) inferInstance
  refine ⟨Z, i, hi, fun T t => (hZ T t).trans ?_⟩
  constructor
  · rintro ⟨q, hq⟩
    rw [← hq, Category.assoc, Category.assoc, equalizer.condition]
  · intro h
    exact ⟨equalizer.lift (X ◁ t) h, equalizer.lift_ι _ _⟩

end Langlands.AlgebraicGeometry.ClosedLiftingLocus
