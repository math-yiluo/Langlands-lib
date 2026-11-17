import Langlands.CategoryTheory.RenardCategoryDecomposition
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Left adjoints of inclusions of category decomposition factors -/

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

/-- Every factor of a category decomposition has a left adjoint to its
inclusion, with no size restriction on the index type. -/
theorem IsCategoryDecomposition.isRightAdjoint_ι
    {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {I : Type w}
    {P : I → ObjectProperty C} (h : IsCategoryDecomposition P) (i : I) :
    (P i).ι.IsRightAdjoint := by
  classical
  let A : C → I → C := fun X => (h.1 X).choose
  let legs : ∀ X, ∀ j, A X j ⟶ X := fun X => (h.1 X).choose_spec.choose
  have hA : ∀ X j, P j (A X j) := fun X => (h.1 X).choose_spec.choose_spec.1
  let hc : ∀ X, IsColimit (Cofan.mk X (legs X)) :=
    fun X => (h.1 X).choose_spec.choose_spec.2.some
  let proj : ∀ X, X ⟶ A X i := fun X =>
    Cofan.IsColimit.desc (hc X)
      (fun j => if hj : j = i then eqToHom (congrArg (A X) hj) else 0)
  have hself : ∀ X, legs X i ≫ proj X = 𝟙 _ := by
    intro X
    change (Cofan.mk X (legs X)).inj i ≫ Cofan.IsColimit.desc (hc X) _ = _
    rw [Cofan.IsColimit.fac]
    simp
  have hne : ∀ X j, j ≠ i → legs X j ≫ proj X = 0 := by
    intro X j hj
    change (Cofan.mk X (legs X)).inj j ≫ Cofan.IsColimit.desc (hc X) _ = _
    rw [Cofan.IsColimit.fac]
    simp [hj]
  let B : C → (P i).FullSubcategory := fun X => ⟨A X i, hA X i⟩
  let e : ∀ X Y, (B X ⟶ Y) ≃ (X ⟶ (P i).ι.obj Y) := fun X Y => {
    toFun := fun f => proj X ≫ f.hom
    invFun := fun g => ObjectProperty.homMk (legs X i ≫ g)
    left_inv := by
      intro f
      apply ObjectProperty.hom_ext
      change legs X i ≫ (proj X ≫ f.hom) = f.hom
      rw [← Category.assoc, hself X, Category.id_comp]
    right_inv := by
      intro g
      change proj X ≫ (legs X i ≫ g) = g
      apply Cofan.IsColimit.hom_ext (hc X)
      intro j
      change legs X j ≫ (proj X ≫ (legs X i ≫ g)) = legs X j ≫ g
      rw [← Category.assoc]
      by_cases hj : j = i
      · subst j
        rw [hself X, Category.id_comp]
      · rw [hne X j hj, zero_comp]
        exact (h.2 j i hj (A X j) Y.obj (hA X j) Y.property _).symm
  }
  exact (Adjunction.adjunctionOfEquivLeft e (fun X Y Y' g f => by
    change proj X ≫ (f.hom ≫ g.hom) = (proj X ≫ f.hom) ≫ g.hom
    exact (Category.assoc _ _ _).symm)).isRightAdjoint

set_option linter.defProp false in
/-- The factor-inclusion adjunction result as a defined proof term. -/
@[instance_reducible]
def categoryDecompositionFactorInclusionRightAdjoint :=
  @IsCategoryDecomposition.isRightAdjoint_ι

end Langlands.Renard
