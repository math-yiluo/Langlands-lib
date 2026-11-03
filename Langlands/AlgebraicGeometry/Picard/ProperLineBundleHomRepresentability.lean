import Langlands.AlgebraicGeometry.Picard.LineHom.Reduction
import Langlands.AlgebraicGeometry.Picard.LineHom.NoetherianModelProof

/-! # Affine representation of actual line-bundle Hom presheaves

For a proper, flat, locally finitely presented morphism `f : X ⟶ S`, a test `T` over `S` and two
line bundles `L`, `M` on `T ×_S X`, the relative Hom presheaf of `L` and `M` on `Over T.left` is
represented by a scheme affine and locally of finite presentation over `T.left`.
-/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- **Representability of line-bundle Hom.** -/
theorem properLineBundleHomRepresentability : ProperLineBundleHomRepresentabilityStatement.{u} :=
  LineHom.properLineBundleHomRepresentability_of_noetherianModel LineHom.noetherianModel

end Langlands.AlgebraicGeometry.Picard
