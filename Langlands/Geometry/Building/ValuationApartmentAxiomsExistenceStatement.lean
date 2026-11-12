import Langlands.Geometry.Building.ValuationBuildingAxioms

/-! # Existence of actual valuation data satisfying the Chapter 7 apartment axioms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- For every connected reductive group `G` over a nonarchimedean local field `F` there are
actual valuation-building data `B` for `G` (a maximal split torus `S`, an `N(F)`-stable
equipollence class `A(S)` of valuations of the root datum of `(G, S)` normalized by
`ω = ord_F`, the actual centralizer `Z_G(S)`, and V 6 on all of `Z(F)`) whose class satisfies
V 7 and AS 2–AS 5. This is KP Theorem 9.6.5 together with the verification of Axiom 4.1.6 in
KP §9.5, transported to the valuation class by the comparison of KP 9.6.6. -/
def ValuationApartmentAxiomsExistenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∃ B : ValuationBuildingData G, B.SatisfiesApartmentAxioms

end Langlands.Geometry.Building
