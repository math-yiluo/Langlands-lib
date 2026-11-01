import Langlands.AbelianScheme.AlgebraicallyClosedSectionSeedExistenceStatement
import Langlands.AlgebraicGeometry.Picard.FiniteSeedOfSeparationProof
import Langlands.AlgebraicGeometry.Picard.PrimeGermPointwiseSeparation
import Langlands.AlgebraicGeometry.Picard.PrimeGermDivisorSectionProof

/-! # Finite section seeds at the unit over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.Picard

/-- Prime-germ divisor sections give finite section seeds at the unit. -/
theorem algebraicallyClosedSectionSeedExistence_of_primeGermDivisorSection
    (hS1 : PrimeGermDivisorSectionStatement.{u}) :
    AlgebraicallyClosedSectionSeedExistenceStatement.{u} := by
  intro K _ _ G _ hsm hpr hgc
  have : CompactSpace G.X.left := QuasiCompact.compactSpace_of_compactSpace G.X.hom
  have : IsLocallyNoetherian G.X.left := LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : IsNoetherian G.X.left := {}
  let z := (1 : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X).left
  have hz : IsRationalPoint G.X.hom z := Over.w (1 : Over.mk (𝟙 _) ⟶ G.X)
  obtain ⟨hpt, htan⟩ := separation_of_primeGermDivisorSection hS1 K G z hz
  exact finiteSeedOfSeparation K G.X.left G.X.hom z hpt htan

/-- Every smooth, proper, geometrically connected commutative group scheme over an
algebraically closed field has a finite point-tangent section seed at its unit. -/
theorem algebraicallyClosedSectionSeedExistence :
    AlgebraicallyClosedSectionSeedExistenceStatement.{u} :=
  algebraicallyClosedSectionSeedExistence_of_primeGermDivisorSection primeGermDivisorSection

end Langlands.GroupScheme
