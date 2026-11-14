import Langlands.Geometry.Building.UnramifiedValuationDescentStatement
import Langlands.BruhatTits.IntegralModels.SpecialFibre
import Langlands.GroupScheme.IntegralModel.LocalField

/-! # Actual integral models and root depths at Galois-fixed apartment points -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

private instance unramifiedFixedRootModelAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **Actual models at the restricted Galois-fixed points.** There are actual
integral models, a closed split torus and the actual reductive special-fibre
quotient whose integral and radical-preimage root points are exactly the
nonnegative and strictly positive restricted root points, respectively. -/
def UnramifiedFixedRootModelStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T),
    CommGroupScheme.groupHom f ≫ iT = iS →
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    letI : Smooth G.X.hom := hG.smooth
    haveI := mono_of_isMaximalSplitTorus hiS
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      haveI : Mono ((GroupScheme.baseChange
          (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
        mono_of_isMaximalSplitTorus hiT
      ∀ (hE : RelativeRoot.HasOppositeFactorPairs
          (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
        IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
        let fixed : D.Apartment → Prop := fun x =>
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val
        let φ : D.Apartment → RootFunctionFamily S G := fun x =>
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
            (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        ∀ z : D.Apartment, fixed z →
          ∃ (D₀ : RelativeComponentModelData ↥𝒪[F] F G)
            (T₀ : IntegralTorusData D₀ S iS) (Q₀ : SpecialFibreQuotientData D₀),
            T₀.IsClosedSplit ∧ Q₀.IsReductiveQuotient ∧
              ∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a,
                (g ∈ D₀.neutral.integralPoints ↔ 0 ≤ φ z a g) ∧
                  (g ∈ Q₀.positivePoints ↔ 0 < φ z a g)

end Langlands.Geometry.Building
