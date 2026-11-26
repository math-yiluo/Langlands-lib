import Langlands.Geometry.Building.KPMinimalCongruentCentralizer

/-! # Unramified descent of the minimal congruent Moy–Prasad groups -/

noncomputable section

universe u

open AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

/-- KP Remark 13.2.3 and Proposition 9.8.3(2) at finite depths, with the minimal
congruent torus filtration. The upstairs subgroup is invariant under coefficient
conjugation, and the image of the downstairs subgroup is its fixed subgroup. -/
def MinimalCongruentMoyPrasadDescentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G), P.SatisfiesApartmentAxioms →
    ∀ (h : P.MinimalCongruentCentralizerOrder)
      (t : P.UnramifiedComparisonTorus) (L : t.ApartmentLift) (x : P.Apartment) (r : ℝ≥0),
      let K := UnramifiedClosure F
      let Q := L.buildingData.minimalCongruentMoyPrasad L.centralizer_isTorus (L.e x) r
      let fixed := (GaloisPoint.fixedSubgroup F K G).comap
        (baseChangeCoeffEquiv F K G).toMonoidHom
      (∀ σ : K ≃ₐ[F] K, Q.map (rationalConjugate F K G σ).toMonoidHom = Q) ∧
        (P.minimalCongruentMoyPrasad h x r).map (rationalExtend F K G) = Q ⊓ fixed

end Langlands.Geometry.Building
