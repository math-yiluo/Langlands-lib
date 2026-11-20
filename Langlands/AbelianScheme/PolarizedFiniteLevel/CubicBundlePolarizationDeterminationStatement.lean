import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle
import Langlands.AlgebraicGeometry.Picard.LineBundleTensor

/-! # The polarization is determined by its cubic bundle up to a twist from the base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard

/-- Let `a` and `b` be ordinary polarized finite-level data over the same locally
noetherian base `S`, and let `e : a.abelian ≅ b.abelian` be an isomorphism of abelian
schemes. Suppose the pullback along `e` of the cubic bundle of `b` is isomorphic to the
cubic bundle of `a` tensored with the pullback of some line bundle `N` on `S`. Then `e`
carries the polarization of `b` to the polarization of `a`: the polarization of `a` is
`e`, followed by the polarization of `b`, followed by the dual of `e` (computed with the
two data's own dual witnesses). This proposition is a statement, not a proof of it. -/
def CubicBundlePolarizationDeterminationStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (S : Scheme.{u}) [IsLocallyNoetherian S] (g d n : ℕ)
    (a b : Datum P S g d n) (e : a.abelian ≅ b.abelian) (N : LineBundle S),
    Nonempty ((LineBundle.pullback (hom e.hom)).obj b.cubicBundle ≅
      LineBundle.tensor P.preservation a.cubicBundle
        ((LineBundle.pullback a.abelian.X.hom).obj N)) →
    a.polarization = e.hom ≫ b.polarization ≫ a.dualWitness.map P b.dualWitness e.hom

end Langlands.AbelianScheme.PolarizedFiniteLevel
