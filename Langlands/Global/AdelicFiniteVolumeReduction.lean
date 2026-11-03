import Langlands.Global.AdelicLeviFiniteVolume
import Langlands.Global.AdelicReductiveFiniteVolumeStatement
import Langlands.Global.TriangularRationalQuotientCompact
import Langlands.GroupScheme.Reductive.CharacteristicZeroLeviStatement

/-! # Reduction of finite volume to the connected reductive case

Finite volume of `G(F) \ G(𝔸_F)¹` for every smooth connected affine `G` over a number field
follows from three inputs: the characteristic-zero Levi decomposition, triangular coordinates
on smooth connected unipotent groups, and finite volume in the connected reductive case.
-/

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

/-- Finite volume of `G(F) \ G(𝔸)¹` for a smooth connected `G`, from a Levi decomposition of
`G`, compactness of the rational quotient of smooth connected unipotent groups and finite
volume for connected reductive groups. -/
theorem isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_levi
    (hlevi : CharacteristicZeroLeviDecompositionStatement.{u})
    (hunip : UnipotentRationalQuotientCompactStatement.{u})
    (hred : ConnectedReductiveFiniteVolumeStatement.{u})
    (F : Type u) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hs : Smooth G.X.hom) (hc : ConnectedSpace G.X.left) :
    IsFiniteMeasure (normOneRationalQuotientHaarMeasure F G) := by
  obtain ⟨L, p, j, hjp, hL, hUs, hUc, hUu⟩ := hlevi F G hs hc
  have : IsAffineHom L.X.hom := hL.isAffineHom
  have : IsAffine L.X.left := isAffine_of_isAffineHom L.X.hom
  have : Smooth L.X.hom := hL.smooth
  have := kernel_isAffine F p
  have := kernel_locallyOfFiniteType F p
  exact leviReductionFiniteVolumeStatement F G L p j hjp
    (hunip F (GroupScheme.kernel p) hUs hUc hUu) (hred F L hL)

/-- **Reduction of the finite-volume target.** The characteristic-zero Levi decomposition,
triangular coordinates on smooth connected unipotent groups and finite volume in the
connected reductive case together imply `NormOneRationalQuotientFiniteVolumeStatement`. -/
def NormOneFiniteVolumeReductionStatement : Prop :=
  CharacteristicZeroLeviDecompositionStatement.{u} →
    UnipotentTriangularCoordinatesStatement.{u} →
      ConnectedReductiveFiniteVolumeStatement.{u} →
        NormOneRationalQuotientFiniteVolumeStatement.{u}

theorem normOneFiniteVolumeReductionStatement : NormOneFiniteVolumeReductionStatement.{u} :=
  fun hlevi htri hred F _ _ G _ _ hs hc =>
    isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_levi hlevi
      (unipotentRationalQuotientCompact_of_triangularCoordinates htri) hred F G hs hc

end Langlands.Global.AdelicGroupPoints
