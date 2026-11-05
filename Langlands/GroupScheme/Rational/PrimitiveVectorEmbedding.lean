import Langlands.GroupScheme.Rational.CommutativePTorsionVectorProof
import Langlands.GroupScheme.AffineCoordinatesFiniteType

/-! # Closed vector embeddings from primitive algebra generators -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HopfPrimitive

section Family

variable {R : CommRingCat.{u}} (A : CommHopfAlgCat.{u} R) {n : ℕ} {y : Fin n → A}
  (hy : ∀ i, Bialgebra.IsPrimitiveElem R (y i))

/-- Primitive functions which generate the coordinate algebra give a closed immersion
into the standard vector group. -/
theorem isClosedSubgroup_familyHom (hgen : Algebra.adjoin R (Set.range y) = ⊤) :
    IsClosedSubgroup (familyHom A hy) := by
  change IsClosedImmersion (familyHom A hy).hom.hom.left
  rw [familyHom_left]
  apply IsClosedImmersion.spec_of_surjective
  exact (AlgHom.range_eq_top (aeval y : MvPolynomial (Fin n) R →ₐ[R] A)).mp
    ((Algebra.adjoin_range_eq_range_aeval R y).symm.trans hgen)

/-- The vector coordinates of the image are the pullbacks of the chosen primitive
functions on every relative scheme test. -/
theorem coordinates_familyHom {T : Over (Spec R)}
    (x : T ⟶ ((hopfSpec R).obj (op A)).X) :
    (VectorGroup.coordinates R n T (x ≫ (familyHom A hy).hom.hom)).toAdd =
      fun i => x.left.appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv (y i)) := by
  funext i
  rw [VectorGroup.coordinates_apply, Over.comp_left, Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  congr 1
  have key := appTop_specMap_inv
    (CommRingCat.ofHom (aeval y : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom) (X i)
  exact key.trans (congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv (aeval_X y i))

end Family

section Field

variable {k : Type u} [Field k] (A : CommHopfAlgCat.{u} (CommRingCat.of k))
  [Algebra.FiniteType k A]

/-- Finite type and generation by primitive elements produce an actual closed
immersion into a finite-dimensional vector group. -/
theorem exists_closed_vectorEmbedding_of_primitive_generation
    (hgen : Algebra.adjoin k {a : A | Bialgebra.IsPrimitiveElem k a} = ⊤) :
    ∃ (n : ℕ) (j : (hopfSpec (CommRingCat.of k)).obj (op A) ⟶
        VectorGroup.groupScheme (CommRingCat.of k) n),
      IsClosedSubgroup j := by
  obtain ⟨n, y, hy, h⟩ :=
    Langlands.Algebra.PTorsionHopf.exists_isPrimitiveGenerating hgen
  exact ⟨n, familyHom A hy, isClosedSubgroup_familyHom A hy h⟩

/-- A chosen finite-dimensional closed vector embedding from primitive generation. -/
def closedVectorEmbeddingOfPrimitiveGeneration
    (hgen : Algebra.adjoin k {a : A | Bialgebra.IsPrimitiveElem k a} = ⊤) :
    Σ n : ℕ, {j : (hopfSpec (CommRingCat.of k)).obj (op A) ⟶
      VectorGroup.groupScheme (CommRingCat.of k) n // IsClosedSubgroup j} :=
  let h := exists_closed_vectorEmbedding_of_primitive_generation A hgen
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

end Field

end Langlands.GroupScheme.HopfPrimitive
