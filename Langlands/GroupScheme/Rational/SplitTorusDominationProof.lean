import Langlands.GroupScheme.Rational.PointedPrimitiveSplit
import Langlands.GroupScheme.Rational.CorepresentedPrimitiveGenerators

/-! # Unipotent splitness from pointed split-torus domination -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The commutative prime-exponent case follows from primitive generation over
the original field and the supplied pointed split-torus domination. -/
theorem primeExponentSplitTorusDomination :
    PrimeExponentSplitTorusDominationCase.{u} := by
  intro k _ p _ _ G _ _ _ _ _ hG hdom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨T, hT⟩ :=
    AffineCoordinates.exists_finite_corepresented_primitive_generators_of_smooth_uniformExponent
      G p hG
  exact isSplitUnipotent_of_pointed_finitePrimitiveGenerators (p := p) G hdom T hT

/-- Every smooth connected affine unipotent group with actual pointed
split-torus domination is split unipotent over its original ground field. -/
theorem unipotentSplitTorusDomination :
    UnipotentSplitTorusDominationStatement.{u} :=
  unipotentSplitTorusDomination_of_primeExponent primeExponentSplitTorusDomination

end Langlands.GroupScheme
