import Langlands.Geometry.Building.FullValidity.ChamberAxioms

/-! # Axiom 4.1.16 for the building of a valuation of the root datum -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Geometry.Building

/-- KP Axiom 4.1.16 (Iwahori decomposition) for the building of KP Chapter 7, on supplied data
over a nonarchimedean local field. Assume V 7 and AS 2–AS 5 for the class `A(S)` of
`P : ParahoricBuildingData G` (the Chapter 7 hypotheses as corrected in 2024, with V 7 in
addition). Then for every chamber `C` of `A(S)` and every positive system of roots, given by a
generic cocharacter `ν` of `S`, with `I` the stabilizer of the image of `C` in `G(F)^0`:
`(U⁺(F) ∩ I) × Z(F)^0 × (U⁻(F) ∩ I) → I` is bijective, and `∏ U_{ψ_a} → U^±(F) ∩ I` is
bijective in every order of the non-divisible roots `a` of either sign, where `ψ_a` is the
smallest affine functional with derivative `a` that is non-negative on `C`.

In KP this follows from Corollary 7.4.9 and Proposition 7.6.4 (1) (KP 4.1.28). No existence
of the data is asserted. -/
def IwahoriDecompositionAxiomStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
    P.SatisfiesApartmentAxioms → P.HasIwahoriDecomposition

end Langlands.Geometry.Building
