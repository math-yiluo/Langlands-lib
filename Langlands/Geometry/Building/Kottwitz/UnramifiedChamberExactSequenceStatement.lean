import Langlands.Geometry.Building.Kottwitz.ReductiveMap
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic

/-! # KP Proposition 11.6.1: the exact sequence for a K-chamber -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.Kottwitz

private instance unramifiedChamberExactSequenceAffineHom
    {F : Type u} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- The actual Kottwitz map on the rational-point carrier of the base-changed group. -/
def reductiveKottwitzOnBaseChange
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G) :
    rationalPoints (baseChanged F (inertiaFixedField F) G) →*
      Multiplicative (ReductiveTarget F F G hG) :=
  (reductiveKottwitz F F G hG).comp
    (baseChangeCoeffEquiv F (inertiaFixedField F) G).toMonoidHom

/-- KP Proposition 11.6.1 on the canonical K-building attached to supplied
apartment data. No stability of the chamber under Galois is required. -/
def UnramifiedChamberExactSequenceStatement : Prop :=
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
          (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C),
          let B := UnramifiedBuildingDescent.buildingData iT
            (connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG)
            hiT D C h6
          ∀ (Cch : Set B.ReducedBuilding), B.IsChamber Cch →
            let P := MulAction.stabilizer
              (rationalPoints (baseChanged F (inertiaFixedField F) G)) Cch
            let κ := reductiveKottwitzOnBaseChange F G hG
            Function.Surjective (κ.domRestrict P) ∧
              ∀ E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G),
                E.zeroPoints ⊓ B.pointwiseFixer Cch = κ.ker ⊓ P

end Langlands.Geometry.Building.Kottwitz
