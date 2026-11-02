import Langlands.AlgebraicGeometry.Morphisms.LocallyOfFiniteTypeSourceDescentStatement
import Langlands.AlgebraicGeometry.Morphisms.SourceDescentReduction
import Langlands.Algebra.FaithfullyFlatFinitePresentationModel
import Langlands.Algebra.FlatFinitePresentationModel

/-! # Proof of local finite type descent along fppf covers of the source -/

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry

/-- Stacks 0367 for `CommRingCat` morphisms, given flat finitely presented models
(Stacks 10.168.1(1)), taken as an explicit hypothesis. -/
theorem finiteType_of_faithfullyFlat_finitePresentation_of_model
    (hmodel : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B],
      Algebra.FinitePresentation A B → Module.Flat A B →
        ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
          Algebra.FiniteType ℤ A₀ ∧ Algebra.FinitePresentation A₀ B₀ ∧ Module.Flat A₀ B₀ ∧
            Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B))
    {R A B : CommRingCat.{u}} (r : R ⟶ A) (s : A ⟶ B) (hff : s.hom.FaithfullyFlat)
    (hfp : s.hom.FinitePresentation) (hft : (r ≫ s).hom.FiniteType) : r.hom.FiniteType := by
  rw [CommRingCat.hom_comp] at hft
  algebraize [r.hom, s.hom, s.hom.comp r.hom]
  have : Module.FaithfullyFlat A B := hff
  exact Langlands.Algebra.finiteType_of_faithfullyFlat_of_flat_model R A B
    (hmodel A B hfp inferInstance)

/-- The main theorem, conditional on the flat model theorem. -/
theorem locallyOfFiniteType_sourceDescent_of_model
    (hmodel : ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B],
      Algebra.FinitePresentation A B → Module.Flat A B →
        ∃ (A₀ : Subalgebra ℤ A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
          Algebra.FiniteType ℤ A₀ ∧ Algebra.FinitePresentation A₀ B₀ ∧ Module.Flat A₀ B₀ ∧
            Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B)) :
    LocallyOfFiniteTypeSourceDescentStatement.{u} := by
  intro X Y S f g hs hf hfp hfg
  exact locallyOfFiniteType_sourceDescent_of_ring
    (fun r s => finiteType_of_faithfullyFlat_finitePresentation_of_model hmodel r s) f g

/-- **Stacks 02KL**, local finite type branch: if `f` is surjective, flat and locally of
finite presentation and `f ≫ g` is locally of finite type, then `g` is locally of finite type. -/
theorem locallyOfFiniteType_of_surjective_flat_locallyOfFinitePresentation_comp :
    LocallyOfFiniteTypeSourceDescentStatement.{u} :=
  locallyOfFiniteType_sourceDescent_of_model fun A B _ _ _ ↦
    Langlands.Algebra.exists_flat_finitePresentation_model A B

end Langlands.AlgebraicGeometry
