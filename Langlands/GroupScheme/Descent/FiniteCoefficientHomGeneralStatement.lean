import Langlands.GroupScheme.Descent.Data

/-! # Finite coefficient descent of homomorphisms over arbitrary algebras -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Descent.FiniteCoefficient

/-- A supplied homomorphism over an arbitrary algebra descends to a finite
coefficient subalgebra, with its direct/iterated pullback compatibility. -/
def HomGeneralStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (G H : GroupScheme (Spec (CommRingCat.of R)))
    [QuasiCompact G.X.hom] [QuasiSeparated G.X.hom]
    [LocallyOfFinitePresentation H.X.hom]
    (f : (baseChange (Spec.algebraMap R A)).obj G ⟶
      (baseChange (Spec.algebraMap R A)).obj H) (s : Finset A),
    ∃ (T : Subalgebra R A), T.FG ∧ (s : Set A) ⊆ T ∧
      ∃ g : (baseChange (Spec.algebraMap R T)).obj G ⟶
          (baseChange (Spec.algebraMap R T)).obj H,
        (baseChange (Spec.algebraMap T A)).map g ≫
            (pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T A)
              (Spec.algebraMap R A)
              (by
                rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
                  ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                rfl) H).hom =
          (pullbackComparison (Spec.algebraMap R T) (Spec.algebraMap T A)
              (Spec.algebraMap R A)
              (by
                rw [Spec.algebraMap, Spec.algebraMap, Spec.algebraMap,
                  ← Spec.map_comp, ← CommRingCat.ofHom_comp]
                rfl) G).hom ≫ f

end Langlands.GroupScheme.Descent.FiniteCoefficient
