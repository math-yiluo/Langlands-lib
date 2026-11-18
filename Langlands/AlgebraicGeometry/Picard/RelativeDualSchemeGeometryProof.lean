import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeGeometryStatement
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeExistenceProof
import Langlands.AlgebraicGeometry.Picard.DualSchemeSmoothTransport
import Langlands.AlgebraicGeometry.Picard.DualSchemeGeometryAssembly
import Langlands.AlgebraicGeometry.Picard.RelativeDualSchemeValuativeExistenceProof

/-!
# Geometry of the chosen dual parameter scheme over a quasi-separated base: proof

Over a quasi-separated base `S`, the published representer
`smoothFamilyAbelianRepresentabilityOfFiniteType finiteTypeSmoothFamilyAbelianRepresentability`
gives an abelian scheme `B` over `S` whose underlying scheme carries an actual universal
Picard-zero family. The chosen dual `dualScheme A hA` is isomorphic to `B.X` over `S`, so its
structure morphism is smooth. Valuative existence and the assembly lemma
`dualSchemeGeometry_of_smooth` then give smoothness, properness and geometric connectedness.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over a quasi-separated base, the structure morphism of the chosen dual is smooth: it is
isomorphic over the base to the abelian scheme produced by the published representer. -/
theorem dualScheme_smooth_of_quasiSeparated {S : Scheme.{u}} [QuasiSeparatedSpace S]
    (A : AbelianScheme S) (hA : HasDualScheme A) : Smooth (dualScheme A hA).hom := by
  obtain ⟨B, L, hL⟩ :=
    smoothFamilyAbelianRepresentabilityOfFiniteType
      finiteTypeSmoothFamilyAbelianRepresentability.{u} S A
  have hU : IsUniversalPicardZero A L :=
    picardZeroQuasiSeparatedExtension S A B.X L
      (universalPicardZeroOnQuasiSeparatedTests_of_smoothFamily A L hL)
  exact (smooth_dualScheme_iff_of_universal A hA L hU).mpr inferInstance

/-- Over a quasi-separated base, the actual universal Picard-zero parameter scheme is smooth,
proper and geometrically connected. -/
theorem relativeDualSchemeGeometry : RelativeDualSchemeGeometryStatement.{u} := by
  intro S _ A hA
  have := dualScheme_smooth_of_quasiSeparated A hA
  exact dualSchemeGeometry_of_smooth relativeDualSchemeValuativeExistence A hA

end Langlands.AbelianScheme
