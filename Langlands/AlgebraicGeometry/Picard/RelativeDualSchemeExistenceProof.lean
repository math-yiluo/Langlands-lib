import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonProof
import Langlands.AlgebraicGeometry.Picard.PicardZeroQuasiSeparatedExtensionProof
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityOfFiniteTypeProof
import Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityProof

/-!
# Existence of the universal Picard-zero family over a quasi-separated base: proof

For every quasi-separated base scheme `S` and every abelian scheme `A` over `S`, the
proof produces an actual parameter scheme over `S` with an actual universal rigidified
geometric Picard-zero family classifying every test scheme. It composes four published
results: the finite-type representer `finiteTypeSmoothFamilyAbelianRepresentability`,
its extension `smoothFamilyAbelianRepresentabilityOfFiniteType` to all quasi-separated
bases, the predicate comparison `smoothFamilyPicardZeroComparison`, and the extension
`picardZeroQuasiSeparatedExtension` from quasi-separated tests to all test schemes.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A rigidified family on a parameter `P` that is universal for smooth-family classes on
quasi-separated tests is also universal for geometric Picard-zero classes on quasi-separated
tests: the same family, classifying maps and uniqueness are reused through the published
comparison of the two predicates. -/
theorem universalPicardZeroOnQuasiSeparatedTests_of_smoothFamily
    {S : Scheme.{u}} (A : AbelianScheme S) {P : Over S}
    (L : RigidifiedFamily A P)
    (hL : IsUniversalSmoothFamilyOnQuasiSeparatedTests A L) :
    IsUniversalPicardZeroOnQuasiSeparatedTests A L := by
  have comparison := smoothFamilyPicardZeroComparison.{u}
  refine ⟨(comparison.2.2.1 S A P L).mp hL.1, ?_⟩
  intro T _ q
  exact hL.2 T
    ⟨q.val, (comparison.2.2.2 S A T q.val).mpr q.property⟩

/-- Every abelian scheme over a quasi-separated base has a dual scheme: an actual parameter
over the base with an actual universal rigidified geometric Picard-zero family classifying
every test scheme by a unique parameter morphism. -/
theorem relativeDualSchemeExistence : RelativeDualSchemeExistenceStatement.{u} := by
  intro S _ A
  obtain ⟨B, L, hL⟩ :=
    smoothFamilyAbelianRepresentabilityOfFiniteType
      finiteTypeSmoothFamilyAbelianRepresentability.{u} S A
  exact ⟨B.X, L, picardZeroQuasiSeparatedExtension S A B.X L
    (universalPicardZeroOnQuasiSeparatedTests_of_smoothFamily A L hL)⟩

end Langlands.AbelianScheme
