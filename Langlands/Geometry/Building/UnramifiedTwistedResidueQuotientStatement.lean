import Langlands.Geometry.Building.FiniteFieldChamberQuotient
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.GroupScheme.Descent.FiniteUnramifiedAutomorphismLift

/-! # Residue quotient at a twisted-fixed point for a Frobenius lift -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedTwistedResidueQuotientAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- The residue quotient at a twisted-fixed point, for every automorphism of the
inertia fixed field that reduces to the arithmetic Frobenius. It supplies one
quotient of a subgroup of the point fixer onto the actual geometric points of a
connected reductive group over the residue field of `F`, compatible with the
twist and with canonical Frobenius descent. The kernel fixes every chamber with
a closure presentation through the point, and the subgroup permutes those
chambers transitively. Its existence is not proved here. -/
def UnramifiedTwistedResidueQuotientStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
        (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
        (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
          rationalPoints (baseChanged F (inertiaFixedField F) G)),
        (∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ)) →
        (∃ E : IntermediateField F (inertiaFixedField F), FiniteDimensional F E ∧
          ∀ σ ∈ E.fixingSubgroup, c σ = 1) →
        ∀ y : (UnramifiedBuildingDescent.buildingData iT
            (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
            hiT D C h6).ReducedBuilding,
          (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            c σ • (UnramifiedBuildingDescent.semilinearData iT
              (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
              hiT C h6 hD).action σ y = y) →
          letI : Fintype 𝓀[F] := Fintype.ofFinite _
          letI : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
            (residueToFixedField F).toAlgebra
          letI : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
            fixedFieldResidueIsAlgClosure F
          ∀ φ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            (∀ x : fixedFieldIntegers F,
              IsLocalRing.residue (fixedFieldIntegers F)
                  (Langlands.GroupScheme.Descent.FiniteUnramified.fixedFieldIntegerAut
                    F φ x) =
                IsLocalRing.residue (fixedFieldIntegers F) x ^ Nat.card 𝓀[F]) →
            ∃ R : GroupScheme (Spec (CommRingCat.of 𝓀[F])), IsConnectedReductive R ∧
              ∃ (P : Subgroup (rationalPoints (baseChanged F (inertiaFixedField F) G)))
                (q : P →* (Over.mk (𝟙 (Spec (CommRingCat.of
                    (IsLocalRing.ResidueField (fixedFieldIntegers F))))) ⟶
                  ((GroupScheme.baseChange (algebraBaseMap 𝓀[F]
                    (IsLocalRing.ResidueField (fixedFieldIntegers F)))).obj R).X))
                (θP : P → P),
                P ≤ (UnramifiedBuildingDescent.buildingData iT
                  (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                  hiT D C h6).fixer y ∧
                Function.Surjective q ∧
                (∀ g : P, (θP g : rationalPoints (baseChanged F (inertiaFixedField F) G)) =
                  c φ * rationalConjugate F (inertiaFixedField F) G φ g * (c φ)⁻¹) ∧
                (∀ g : P, q (θP g) =
                  descentBasePoint
                    (algebraBaseMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)))
                    (galoisBaseMap 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))
                      (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
                        (IsLocalRing.ResidueField (fixedFieldIntegers F))))
                    (galoisBaseMap_over 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F))
                      (FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[F]
                        (IsLocalRing.ResidueField (fixedFieldIntegers F))))
                    R (q g)) ∧
                (∀ Y : Set (UnramifiedBuildingDescent.buildingData iT
                    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                    hiT D C h6).ReducedBuilding,
                  (UnramifiedBuildingDescent.buildingData iT
                    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                    hiT D C h6).HasChamberClosurePresentation Y y →
                  ∀ g : P, q g = 1 →
                    ((g : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) ''
                      Y = Y) ∧
                (∀ Y Y' : Set (UnramifiedBuildingDescent.buildingData iT
                    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                    hiT D C h6).ReducedBuilding,
                  (UnramifiedBuildingDescent.buildingData iT
                    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                    hiT D C h6).HasChamberClosurePresentation Y y →
                  (UnramifiedBuildingDescent.buildingData iT
                    (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
                    hiT D C h6).HasChamberClosurePresentation Y' y →
                  ∃ h : P,
                    Y' = ((h : rationalPoints (baseChanged F (inertiaFixedField F) G)) • ·) '' Y)

end Langlands.Geometry.Building
