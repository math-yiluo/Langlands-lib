import Langlands.Representation.Plancherel.ActualConjugateLeviExistence
import Langlands.Representation.Plancherel.ActualConjugateLeviPresentationIndependence
import Langlands.Representation.Plancherel.ActualConjugateLeviCompositionLaw
import Langlands.Representation.Plancherel.ActualConjugateLeviInverseLaw

/-! # Actual conjugate-Levi coherence of Waldspurger V.3.2 -/

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
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
  (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  (d : LeviNormalization χ A)

/-- Waldspurger V.3.2 for the actual conjugate-Levi comparisons, with the
  prescribed source normalization and the canonical fiber transports. -/
theorem closedV32 : ClosedV32Statement χ hG A K hK d := by
  intro hd
  exact ⟨existenceLaw χ hG A K hK d hd, presentationIndependence χ hG A K hK d,
    identityLaw χ hG A K hK d, compositionLaw χ hG A K hK d, inverseLaw χ hG A K hK d⟩

end Langlands.Plancherel.ActualConjugateLeviCoherence
