import Langlands.Geometry.Analytic.GroundFieldExtensionMaps
import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms

/-! # Ground field extension preserves full atlas quasi-isomorphisms -/

universe u v w u'

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

/-- The actual scalar extension of a compatible strong quasi-isomorphism has a
homeomorphic ambient map and represents its chart image at every admissible pair. -/
def GroundFieldExtensionQuasiIsoStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L]
    [NormedAlgebra K L] {A B : AffinoidAtlasPresentation.{u, v, w} K}
    (f : CompatibleStrongHom A B),
    f.toStrongHom.IsQuasiIso → (compatibleMap K L f).toStrongHom.IsQuasiIso

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
