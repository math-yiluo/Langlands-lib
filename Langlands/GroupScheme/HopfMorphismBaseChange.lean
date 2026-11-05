import Langlands.GroupScheme.AffineHopfMorphism
import Langlands.GroupScheme.HopfBaseChange
import Langlands.CommutativeAlgebra.DiagonalCoalgebraLocus
import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-! # Scalar-extension coordinates of actual base-changed affine morphisms -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry CategoryTheory.Limits
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.HopfMorphismBaseChange

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]

/-- The actual base change of an affine spectrum, with the scalar factor first
in its tensor coordinates. -/
def tensorSpecIso (A : Type u) [CommRing A] [Algebra R A] :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj
      ((algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A)))).left ≅
        Spec (CommRingCat.of (S ⊗[R] A)) :=
  pullbackSymmetry .. ≪≫ pullbackSpecIso R S A

variable {R S}

set_option backward.isDefEq.respectTransparency false in
/-- The tensor-coordinate comparison commutes with every affine algebra map. -/
theorem tensorSpecIso_naturality {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
      ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)).left =
      (tensorSpecIso R S B).hom ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom) ≫
        (tensorSpecIso R S A).inv := by
  apply (cancel_epi (tensorSpecIso R S B).inv).mp
  simp only [Iso.inv_hom_id_assoc]
  apply pullback.hom_ext
  · simp [tensorSpecIso, Over.pullback_map_left, Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 1
  · simp [tensorSpecIso, Over.pullback_map_left, Category.assoc,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A base-changed morphism of affine spectra is a closed immersion exactly
when its tensor coordinate map is surjective. -/
theorem isClosedImmersion_baseChange_iff {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) :
    IsClosedImmersion
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)).left) ↔
      Function.Surjective (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  rw [tensorSpecIso_naturality]
  rw [MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion),
    MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)]
  let f' : CommRingCat.of (S ⊗[R] A) ⟶ CommRingCat.of (S ⊗[R] B) :=
    CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f).toRingHom
  change IsClosedImmersion (Spec.map f') ↔ Function.Surjective f'
  constructor
  · intro h
    let := h
    exact CentralExtensionHopfSpec.surjective_of_isClosedImmersion f'
  · exact IsClosedImmersion.spec_of_surjective f'

section Diagonal

variable {M : Type u} [AddCommMonoid M] {A : Type u} [CommRing A] [Algebra R A]

/-- The diagonal scalar-extension map is the ordinary tensor map followed by
the canonical monoid-algebra scalar-extension isomorphism. -/
theorem scalarExtension_eq (f : A →ₐ[R] AddMonoidAlgebra R M) :
    CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension f S =
      (AddMonoidAlgebra.scalarTensorEquiv R S (M := M)).toAlgHom.comp
        (Algebra.TensorProduct.map (AlgHom.id S S) f) := by
  ext a b
  simp

/-- Surjectivity in diagonal coordinates is the affine closed-immersion
condition for the actual base change. -/
theorem isClosedImmersion_diagonal_baseChange_iff
    (f : A →ₐ[R] AddMonoidAlgebra R M) :
    IsClosedImmersion
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op)).left) ↔
      Function.Surjective
        (CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension f S) := by
  rw [isClosedImmersion_baseChange_iff, scalarExtension_eq]
  exact ⟨fun h => (AddMonoidAlgebra.scalarTensorEquiv R S (M := M)).surjective.comp h,
    fun h y => by
      obtain ⟨x, hx⟩ := h (AddMonoidAlgebra.scalarTensorEquiv R S (M := M) y)
      exact ⟨x, (AddMonoidAlgebra.scalarTensorEquiv R S (M := M)).injective hx⟩⟩

end Diagonal

section HopfDiagonal

variable {M : Type u} [AddCommGroup M] {A : Type u} [CommRing A] [HopfAlgebra R A]

/-- The criterion also applies to the actual group homomorphism supplied by
the Hopf spectrum functor, with its actual group-scheme base change. -/
theorem isClosedImmersion_hopf_diagonal_baseChange_iff
    (f : A →ₐc[R] AddMonoidAlgebra R M) :
    IsClosedImmersion
      (((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R S)))).map
        ((hopfSpec (CommRingCat.of R)).map (CommHopfAlgCat.ofHom f).op)).hom.hom.left) ↔
      Function.Surjective
        (CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension f.toAlgHom S) :=
  isClosedImmersion_diagonal_baseChange_iff f.toAlgHom

end HopfDiagonal

end Langlands.GroupScheme.HopfMorphismBaseChange
