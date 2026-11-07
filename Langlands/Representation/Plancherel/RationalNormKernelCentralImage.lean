import Langlands.Representation.Plancherel.RationalImageCharacters
import Langlands.Representation.Plancherel.SplitComponentLatticeBridge
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Subgroup images in the actual norm-kernel quotient -/

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))

/-- The image of a normal point subgroup in the actual norm-kernel quotient
corresponds to its image under the actual valuation-image projection. -/
def rationalNormKernelSubgroupQuotientEquiv
    (A : Subgroup (GroupScheme.rationalPoints G)) [A.Normal] :
    ((GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) ⧸
      A.map (QuotientGroup.mk' (rationalCommonNormKernel G))) ≃*
      (rationalDiscreteValuationImage G ⧸ A.map (rationalValuationImageProjection G)) := by
  letI : (A.map (rationalValuationImageProjection G)).Normal :=
    Subgroup.normal_of_isMulCommutative _
  apply QuotientGroup.congr (H := rationalDiscreteValuationImage G) _ _
    (rationalNormKernelQuotientEquiv G)
  rw [Subgroup.map_map]
  congr 1

@[simp]
theorem rationalNormKernelSubgroupQuotientEquiv_mk
    (A : Subgroup (GroupScheme.rationalPoints G)) [A.Normal]
    (g : GroupScheme.rationalPoints G) :
    rationalNormKernelSubgroupQuotientEquiv G A
        (QuotientGroup.mk (QuotientGroup.mk g)) =
      QuotientGroup.mk (rationalValuationImageProjection G g) := rfl

/-- Finiteness transfers to the literal quotient of the norm-kernel quotient. -/
theorem finite_rationalNormKernelSubgroupQuotient
    (A : Subgroup (GroupScheme.rationalPoints G)) [A.Normal]
    [Finite (rationalDiscreteValuationImage G ⧸ A.map (rationalValuationImageProjection G))] :
    Finite ((GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) ⧸
      A.map (QuotientGroup.mk' (rationalCommonNormKernel G))) :=
  Finite.of_injective _ (rationalNormKernelSubgroupQuotientEquiv G A).injective

variable {G} {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- The mapped actual point image is exactly the existing split valuation image.
The identity itself needs no centrality or splitness. -/
theorem rationalSplitPointImage_map_valuationProjection (s : T.toGrp ⟶ G) :
    (GroupScheme.rationalPoints.map s).range.map (rationalValuationImageProjection G) =
      RenardCartan.splitValuationImage s :=
  MonoidHom.map_range _ _

/-- The exact valuation quotient used by unitary detection is finite under
the explicit split-image finite-index premise. -/
theorem finite_rationalValuationQuotient_of_splitIndex (s : T.toGrp ⟶ G)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    Finite (rationalDiscreteValuationImage G ⧸
      (GroupScheme.rationalPoints.map s).range.map (rationalValuationImageProjection G)) := by
  rw [rationalSplitPointImage_map_valuationProjection]
  change Finite (rationalCharacterValuationImage G ⧸ RenardCartan.splitValuationImage s)
  let := hindex
  infer_instance

/-- A split component and injectivity of rational-character restriction supply
the exact finite valuation quotient. Injectivity remains an explicit premise. -/
theorem finite_rationalValuationQuotient_of_injective
    (hG : GroupScheme.IsConnectedReductive G) (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsSplitComponent s)
    (hinj : Function.Injective (GroupScheme.characterRestrict s)) :
    Finite (rationalDiscreteValuationImage G ⧸
      (GroupScheme.rationalPoints.map s).range.map (rationalValuationImageProjection G)) :=
  finite_rationalValuationQuotient_of_splitIndex s
    (RenardCartan.finiteIndex_splitValuationImage_of_injective hG s hs hinj)

/-- The corresponding literal quotient by the central image is finite, with
finite index of the actual valuation image retained as a premise. -/
theorem finite_rationalNormKernelCentralImageQuotient (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsCentral s)
    (hindex : (RenardCartan.splitValuationImage s).FiniteIndex) :
    Finite ((GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) ⧸
      (GroupScheme.rationalPoints.map s).range.map
        (QuotientGroup.mk' (rationalCommonNormKernel G))) := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  let := finite_rationalValuationQuotient_of_splitIndex s hindex
  exact finite_rationalNormKernelSubgroupQuotient G (GroupScheme.rationalPoints.map s).range

/-- Character restriction injectivity supplies the finite central-image quotient
for an actual split component. -/
theorem finite_rationalNormKernelCentralImageQuotient_of_injective
    (hG : GroupScheme.IsConnectedReductive G) (s : T.toGrp ⟶ G)
    (hs : GroupScheme.IsSplitComponent s)
    (hinj : Function.Injective (GroupScheme.characterRestrict s)) :
    Finite ((GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) ⧸
      (GroupScheme.rationalPoints.map s).range.map
        (QuotientGroup.mk' (rationalCommonNormKernel G))) :=
  finite_rationalNormKernelCentralImageQuotient s hs.isCentralSplitTorus.isCentral
    (RenardCartan.finiteIndex_splitValuationImage_of_injective hG s hs hinj)

end Langlands.Plancherel
