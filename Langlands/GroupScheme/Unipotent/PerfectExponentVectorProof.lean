import Langlands.GroupScheme.Unipotent.PerfectExponentVectorStatement
import Langlands.GroupScheme.Rational.CommutativePTorsionVectorProof
import Langlands.GroupScheme.Rational.SmoothPTorsionPrimitiveGenerators

/-! # Groups of exponent `p` over perfect fields are vector groups -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory MvPolynomial
open Langlands.Algebra.PTorsionHopf

namespace Langlands.GroupScheme

/-- Milne 14.54: a smooth connected commutative affine group killed by `p` over a
perfect field of characteristic `p` is a vector group. -/
theorem perfectFieldExponentVectorGroup : PerfectFieldExponentVectorGroupStatement.{u} := by
  classical
  intro k _ _ p _ _ G _ _ _ hConnected hExponent
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let A := AffineCoordinates.hopfAlgebra G
  let e := AffineCoordinates.hopfSpecIso G
  have : Algebra.Smooth (CommRingCat.of k) A := AffineCoordinates.hopfAlgebraSmooth G
  have : Algebra.FiniteType k A := inferInstanceAs (Algebra.FiniteType (CommRingCat.of k) A)
  have : IsDomain A := Langlands.Algebra.GradedHopf.isDomain_of_hopfSpec A
    (RelativeRoot.smooth_hom_of_iso e inferInstance)
    (RelativeRoot.connectedSpace_left_of_iso e hConnected)
  have hGenerate : Algebra.adjoin k {a : A | Bialgebra.IsPrimitiveElem k a} = ⊤ :=
    AffineCoordinates.adjoin_primitive_eq_top_of_smooth_uniformExponent G p hExponent
  have hExists := exists_isPrimitiveGenerating hGenerate
  obtain ⟨y, hy⟩ := Nat.find_spec hExists
  have hSurj : Function.Surjective
      (aeval y : MvPolynomial (Fin (Nat.find hExists)) k →ₐ[k] A) := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
    exact hy.2
  have hInj := injective_aeval_of_minimal p y hy fun _ hlt => Nat.find_min hExists hlt
  exact ⟨Nat.find hExists, ⟨e.symm ≪≫ HopfPrimitive.isoVectorGroup A hy.1 ⟨hInj, hSurj⟩⟩⟩

end Langlands.GroupScheme
