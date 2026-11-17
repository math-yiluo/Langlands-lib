import Langlands.AlgebraicGeometry.Picard.SmoothFamilyFlatStatement
import Langlands.AlgebraicGeometry.Picard.FiniteTypeSmoothFamilyAbelianRepresentabilityProof
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyAbelianRepresentabilityOfFiniteTypeProof
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyUniversalComparisonProof

/-!
# Flatness of a universal smooth-family Picard parameter: proof

The published finite-type representer and its published reduction to arbitrary
quasi-separated bases supply an abelian scheme `B` with a universal family. The
published comparison of universal parameters identifies the supplied parameter `P`
with `B.X` over the base. The structure morphism of `B.X` is smooth, hence flat, and
flatness transfers along the isomorphism.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Over a quasi-separated base, the parameter of every universal rigidified
smooth-family algebraically trivial family on quasi-separated tests is flat over the
base. -/
theorem smoothFamilyFlat : SmoothFamilyFlatStatement.{u} := by
  intro S _ A P L hL
  -- The common abelian-scheme representer over the quasi-separated base `S`.
  obtain ⟨B, N, hN⟩ :=
    smoothFamilyAbelianRepresentabilityOfFiniteType
      finiteTypeSmoothFamilyAbelianRepresentability.{u} S A
  -- `B.X.left` is quasi-separated: `B.X.hom` is proper and `S` is quasi-separated.
  have : QuasiSeparatedSpace B.X.left :=
    quasiSeparatedSpace_of_quasiSeparated B.X.hom
  -- Compare the two universal parameters.
  obtain ⟨e, _, _⟩ := smoothFamilyUniversalComparison S A B.X P N L hN hL
  have : IsIso e.inv.left := by
    change IsIso ((Over.forget S).map e.inv)
    infer_instance
  -- `P.hom = e.inv.left ≫ B.X.hom`, an isomorphism followed by a smooth morphism.
  rw [← Over.w e.inv]
  infer_instance

end Langlands.AbelianScheme
