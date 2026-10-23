import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonStatements

noncomputable section

universe u

open CategoryTheory MonoidalCategory BraidedCategory AlgebraicGeometry

namespace Langlands.Scheme.Modules

private lemma leftUnitor_comparison
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (P : C) {M : D} (c : F.obj P ≅ M) :
    (Functor.LaxMonoidal.ε F ⊗ₘ c.inv) ≫
      Functor.LaxMonoidal.μ F (𝟙_ C) P ≫ F.map (λ_ P).hom ≫ c.hom = (λ_ M).hom := by
  rw [tensorHom_def', Category.assoc, ← Functor.LaxMonoidal.left_unitality_assoc]
  simp only [leftUnitor_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

private lemma rightUnitor_comparison
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal] (P : C) {M : D} (c : F.obj P ≅ M) :
    (c.inv ⊗ₘ Functor.LaxMonoidal.ε F) ≫
      Functor.LaxMonoidal.μ F P (𝟙_ C) ≫ F.map (ρ_ P).hom ≫ c.hom = (ρ_ M).hom := by
  rw [tensorHom_def, Category.assoc, ← Functor.LaxMonoidal.right_unitality_assoc]
  simp only [rightUnitor_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

private lemma braiding_comparison
    {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D]
    (F : C ⥤ D) [F.LaxBraided] (P Q : C) {M N : D}
    (c : F.obj P ≅ M) (d : F.obj Q ≅ N) :
    ((c.inv ⊗ₘ d.inv) ≫ Functor.LaxMonoidal.μ F P Q) ≫ F.map (β_ P Q).hom =
      (β_ M N).hom ≫ (d.inv ⊗ₘ c.inv) ≫ Functor.LaxMonoidal.μ F Q P := by
  rw [Category.assoc, Functor.LaxBraided.braided, ← Category.assoc,
    braiding_naturality, Category.assoc]

/-- The localized left unitor agrees with the explicit sheafified left unitor. -/
theorem tensorMonoidalLeftUnitorComparison : TensorMonoidalLeftUnitorComparisonStatement.{u} := by
  intro X M
  exact leftUnitor_comparison (sheafify X) M.val ((sheafifyForgetIso X).app M)

/-- The localized right unitor agrees with the explicit sheafified right unitor. -/
theorem tensorMonoidalRightUnitorComparison : TensorMonoidalRightUnitorComparisonStatement.{u} := by
  intro X M
  exact rightUnitor_comparison (sheafify X) M.val ((sheafifyForgetIso X).app M)

/-- The localized braiding agrees with the explicit sheafified factor swap. -/
theorem tensorMonoidalSymmetryComparison : TensorMonoidalSymmetryComparisonStatement.{u} := by
  intro X M N
  exact braiding_comparison (sheafify X) M.val N.val
    ((sheafifyForgetIso X).app M) ((sheafifyForgetIso X).app N)

/-- The fixed localized tensor comparison preserves the explicit unitors and symmetry. -/
theorem tensorMonoidalComparison : TensorMonoidalComparisonStatement.{u} :=
  ⟨tensorMonoidalLeftUnitorComparison, tensorMonoidalRightUnitorComparison,
    tensorMonoidalSymmetryComparison⟩

end Langlands.Scheme.Modules
