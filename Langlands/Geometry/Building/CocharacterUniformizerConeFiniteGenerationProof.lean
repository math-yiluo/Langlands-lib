import Langlands.Geometry.Building.CocharacterUniformizerConeFiniteGenerationStatement
import Langlands.Geometry.Building.CocharacterUniformizerConeQuotientProof
import Langlands.GroupScheme.Rational.CocharacterConeFiniteGenerationProof
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Finite generation of the actual nonnegative uniformizer quotient -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CocharacterUniformizer

theorem coneQuotientFiniteGeneration : ConeQuotientFiniteGenerationStatement.{u} := by
  intro F _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hG.smooth
  intro ν hν A a ha f hf
  let R := simpleRelativeRoots i ν
  have hR : R.Finite := hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν
  have hcone : AddMonoid.FG (CocharacterCone.quotient T R) :=
    (AddMonoid.fg_iff_addSubmonoid_fg _).2 (cocharacterConeFiniteGeneration F T R hR)
  have : Monoid.FG (Multiplicative (CocharacterCone.quotient T R)) :=
    AddMonoid.fg_iff_mul_fg.mp hcone
  obtain ⟨e, _⟩ := coneQuotientComparison F G hG T i hi ν hν A a ha f hf
  exact (Monoid.fg_iff_submonoid_fg (CAplusQuotient F T R A f)).1
    (Monoid.fg_of_surjective e.toMonoidHom e.surjective)

end Langlands.GroupScheme.CocharacterUniformizer
