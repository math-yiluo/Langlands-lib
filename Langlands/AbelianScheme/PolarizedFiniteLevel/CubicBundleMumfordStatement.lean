import Langlands.AbelianScheme.PolarizedFiniteLevel.CanonicalBundle

/-! # The Mumford map of the actual cubic diagonal bundle -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme.PolarizedFiniteLevel

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The actual tensor cube of the canonical diagonal bundle has Mumford map
`6 • polarization`, with all normalization data supplied as conclusions. -/
def CubicBundleMumfordStatement : Prop :=
  ∀ (P : Prerequisites.{u}) (K : Type u) [Field K] (g d n : ℕ)
    (a : Datum P (Spec (CommRingCat.of K)) g d n),
    ∃ (B : LineBundle (Spec (CommRingCat.of K)))
      (evaluationB : tensorObj ((Scheme.Modules.pullback (unitSection a.abelian)).obj
        a.cubicBundle.obj) B.obj ≅ structureSheaf (Spec (CommRingCat.of K)))
      (M : LineBundle a.abelian.X.left)
      (evaluation : tensorObj (LineBundle.normalize P.preservation a.abelian.X.hom
        (unitSection a.abelian) (unitSection_comp a.abelian) a.cubicBundle B
        evaluationB).obj.carrier M.obj ≅ structureSheaf a.abelian.X.left),
      mumfordSchemeMapOfLineBundle P.preservation a.abelian a.cubicBundle B evaluationB
        M evaluation P.square a.dualWitness.hasDual =
          (groupHom (6 • a.polarization)).hom.hom

end Langlands.AbelianScheme.PolarizedFiniteLevel
