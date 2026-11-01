import Langlands.AlgebraicGeometry.FiniteEtale.GeometricCardinality
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- Sections of the actual fibre are actual lifts of its defining point. -/
def fibreSectionsEquiv {X Y T : Scheme.{u}} (f : X ⟶ Y) (t : T ⟶ Y) :
    {z : T ⟶ pullback f t // z ≫ pullback.snd f t = 𝟙 T} ≃
      {z : T ⟶ X // z ≫ f = t} where
  toFun z := ⟨z.1 ≫ pullback.fst f t, by
    rw [Category.assoc, pullback.condition, ← Category.assoc, z.2, Category.id_comp]⟩
  invFun z := ⟨pullback.lift z.1 (𝟙 T) (by simpa using z.2),
    pullback.lift_snd _ _ _⟩
  left_inv z := by
    apply Subtype.ext
    apply pullback.hom_ext
    · exact pullback.lift_fst _ _ _
    · rw [pullback.lift_snd, z.2]
  right_inv z := by
    apply Subtype.ext
    exact pullback.lift_fst _ _ _

/-- Over a field, the rank of a finite flat scheme is the dimension of its
actual coordinate algebra. -/
theorem homFinrank_eq_coordinateFinrank {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (.of K)) [IsFinite f] [Flat f] (x : Spec (.of K)) :
    letI := coordinateAlgebra f
    f.finrank x = Module.finrank K Γ(X, ⊤) := by
  let := coordinateAlgebra f
  have : IsAffine X := isAffine_of_isAffineHom f
  let φ : CommRingCat.of K ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop
  have hφ : Spec.map φ = X.isoSpec.inv ≫ f := by
    dsimp [φ]
    rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv, Scheme.isoSpec_inv_naturality]
  have hfinite : φ.hom.Finite := by
    exact RingHom.Finite.comp f.finite_appTop
      (RingHom.Finite.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv).2)
  have hflat : φ.hom.Flat := by
    exact RingHom.Flat.comp
      (RingHom.Flat.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of K)).inv))
      f.flat_appTop
  rw [← Scheme.Hom.finrank_comp_left_of_isIso X.isoSpec.inv f, ← hφ,
    Scheme.Hom.finrank_SpecMap_eq_finrank hfinite hflat]
  change Module.rankAtStalk (R := K) Γ(X, ⊤) x = _
  rw [Module.rankAtStalk_eq_finrank_of_free]
  rfl

/-- Over a separably closed field, the number of actual sections is the native
scheme-theoretic rank. -/
theorem natCard_sections_eq_homFinrank {X : Scheme.{u}} {K : Type u} [Field K]
    [IsSepClosed K] (f : X ⟶ Spec (.of K)) [IsFinite f] [Etale f]
    (x : Spec (.of K)) :
    Nat.card {z : Spec (.of K) ⟶ X // z ≫ f = 𝟙 _} = f.finrank x :=
  (natCard_sections_eq_finrank f).trans (homFinrank_eq_coordinateFinrank f x).symm

/-- The actual lifts of a separably closed field point along a finite étale
morphism are counted by that morphism's native rank at the point. -/
theorem natCard_lifts_eq_finrank {X Y : Scheme.{u}} {K : Type u} [Field K]
    [IsSepClosed K] (f : X ⟶ Y) [IsFinite f] [Etale f]
    (t : Spec (.of K) ⟶ Y) (x : Spec (.of K)) :
    Nat.card {z : Spec (.of K) ⟶ X // z ≫ f = t} = f.finrank (t x) := by
  rw [← Nat.card_congr (fibreSectionsEquiv f t),
    natCard_sections_eq_homFinrank (pullback.snd f t) x,
    Scheme.Hom.finrank_pullback_snd]

end Langlands.AlgebraicGeometry.FiniteEtale
