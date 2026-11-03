import Langlands.Representation.Aubert.General.DynamicNestedParabolicTopology
import Langlands.Representation.Aubert.General.NestedParabolicTransitivity

/-! # Normalized transitivity for actual nested dynamic parabolics -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

universe u uV

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Aubert.General

/-- Both normalized comparisons for actual dynamic parabolics, at the exact
published field scope and independent representation-carrier universe. -/
theorem dynamicNestedParabolicTransitivity :
    DynamicNestedParabolicTransitivityStatement.{u, uV} := by
  intro F _ _ _ _ G hG χ ψ hPair hNested
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (RationalPoint F G.X) := rationalPointTopology F G.X
  dsimp only
  intro _ _ hN hU hL
  have : Smooth G.X.hom := hG.smooth
  have : SecondCountableTopology F := localField_secondCountableTopology F
  have : SecondCountableTopology (RationalPoint F G.X) :=
    rationalPoint_secondCountableTopology F G
  let X := Over.mk (𝟙 (Spec (CommRingCat.of F)))
  let hP := dynamic_isSemidirectDecomposition χ X
  let hQ := dynamic_isSemidirectDecomposition ψ X
  let hInner := dynamic_nested_isSemidirectDecomposition_in_levi χ ψ hNested X
  have hML := hPair.2.1 X
  have hPQ := hPair.1 X
  have hprod :
      ((Dynamic.unipotent χ).carrier X : Set (RationalPoint F G.X)) =
        ((Dynamic.centralizer ψ).carrier X ⊓ (Dynamic.unipotent χ).carrier X :
          Subgroup (RationalPoint F G.X)) *
        ((Dynamic.unipotent ψ).carrier X : Set (RationalPoint F G.X)) :=
    (hNested X).2.2.2.2.2.1
  have hp : Continuous hQ.projection := continuous_dynamic_projection F G ψ
  have hNc : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((Dynamic.unipotent χ).carrier X) :=
    BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
      BruhatTits.dynamicUnipotentCompactOpenContainment F G hG χ
  have hUc : Jacquet.Localization.IsLimitOfCompactSubgroups
      ((Dynamic.unipotent ψ).carrier X) :=
    BruhatTits.dynamicUnipotent_isLimitOfCompactSubgroups
      BruhatTits.dynamicUnipotentCompactOpenContainment F G hG ψ
  have hWc := compactLimit_subgroupOf
    ((Dynamic.unipotent χ).carrier X) ((Dynamic.centralizer ψ).carrier X) hL hNc
  have hδN := isUnimodularModulus_of_isLimitOfCompactSubgroups _ hN hNc
  have hδU := isUnimodularModulus_of_isLimitOfCompactSubgroups _ hU hUc
  have hχ := NestedParabolic.halfCharacterProduct
    hP hQ hL hN hU hPQ hprod hp hInner
  exact ⟨⟨NestedInduction.iso.{u, uV}
      hP hQ hL hML hInner hN hU hPQ (NestedParabolic.unipotent_le hprod)
      hp hδN hδU hχ⟩,
    ⟨NestedParabolic.jacquetIso.{u, uV}
      hP hQ hL hN hU hPQ hprod hp hML hInner hWc⟩⟩

end Langlands.Aubert.General
