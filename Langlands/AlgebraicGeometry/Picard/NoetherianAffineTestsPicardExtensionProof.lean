import Langlands.AlgebraicGeometry.Picard.NoetherianAffineTestsPicardExtensionStatement
import Langlands.AlgebraicGeometry.Picard.NoetherianAffineTestsPicardExtension

/-! # Proof: representability of the Picard class sheaf from noetherian affine tests -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Proof of `NoetherianAffineTestsPicardExtensionStatement`. -/
theorem noetherianAffineTestsPicardExtension :
    NoetherianAffineTestsPicardExtensionStatement.{u} := by
  intro R _ _ X f hprop hflat hint hsec P hP hα
  obtain ⟨ε, hε⟩ := hsec
  obtain ⟨α⟩ := hα
  exact NoetherianAffineTests.nonempty_representableBy_of_noetherianAffine f ε hε α

end Langlands.AlgebraicGeometry.Picard
