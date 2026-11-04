import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.Geometry.Building.KPParahoric

/-!
# The centralizer part of `G(F)^0_Ω`

KP Lemma 7.4.3: for a non-empty subset `Ω` of the apartment,
`Z(F) ∩ G(F)^0_Ω = Z(F)^0`. This is a Prop-valued target on actual data,
with the corrected Chapter 7 apartment premises explicit.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- KP Lemma 7.4.3 on the actual fixed apartment: for every non-empty
`Ω ⊆ A(S)`, the points of `G(F)` centralizing `S` that lie in
`P_Ω = Z(F)^0 · G(F)^♯_Ω` form exactly the image of `Z(F)^0` under the
actual centralizer inclusion `j : Z_G(S) → G`. It retains the corrected
Chapter 7 apartment axioms, including AS 5, as a premise and asserts no
existence of data. -/
def CentralizerParahoricIntersectionStatement : Prop :=
  P.apartment.SatisfiesApartmentAxioms P.centralizer →
  ∀ Ω : Set P.Apartment, Ω.Nonempty →
    centralizerPoints P.i ⊓ P.parahoric Ω =
      P.centralizerZero.map (rationalPoints.map P.centralizer.j)

end Langlands.Geometry.Building.ParahoricBuildingData
