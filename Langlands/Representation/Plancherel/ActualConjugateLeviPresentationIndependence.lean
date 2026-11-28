import Langlands.Representation.Plancherel.ActualConjugateLeviCoherenceStatement
import Langlands.Representation.Plancherel.ActualCommonLeviCoherenceProof

/-! # Presentation independence for the actual translated comparison -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology Langlands.GroupScheme

namespace Langlands.Plancherel.ActualConjugateLeviCoherence

open DynamicOppositeStandardIntertwining ActualConjugateLeviTwist

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  LeviNormalization.normal LeviNormalization.quotientMeasurable
  LeviNormalization.quotientBorel LeviNormalization.quotientHaar LeviNormalization.quotientInversion

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (d : LeviNormalization χ A)

set_option maxHeartbeats 1000000 in
/-- Two certified translated comparisons at the same actual source and target
coincide by presentation independence for the common-Levi comparison at the
target. The unitary translation preceding it is fixed by the rational point. -/
theorem presentationIndependence :
    PresentationIndependence χ hG A K hK d := by
  intro g dg P Q T S
  obtain ⟨_, _, U, hU, hTU, _⟩ := T.property
  obtain ⟨_, _, V, hV, hSV, _⟩ := S.property
  have hcommon := ActualCommonLeviCoherence.closedCommonLeviCoherence
    (χ ≫ (G.innerIso (g : RationalPoint F G.X)).hom) hG
    (conjugateRepresentation χ (g : RationalPoint F G.X) A)
    dg.center dg.central dg.quotientMeasure dg.squareIntegrable dg.irreducible K hK dg.splitCenter
  have hUV := hcommon.2 _ _ U V hU hV
  subst V
  exact eq_of_heq (hTU.trans hSV.symm)

end Langlands.Plancherel.ActualConjugateLeviCoherence
