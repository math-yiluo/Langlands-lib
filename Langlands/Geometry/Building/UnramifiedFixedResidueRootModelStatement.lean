import Langlands.BruhatTits.IntegralModels.RootSpecialization
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.Geometry.Building.SmoothRootModelLifting
import Langlands.Geometry.Building.UnramifiedRootJumpDescentStatement

/-! # Fixed-point models whose reductive quotients carry the vanishing restricted roots -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

set_option maxHeartbeats 1000000 in
/-- **Residue roots of the actual models at the restricted Galois-fixed points.**
At each Galois-fixed upper apartment point there are an actual relative-component
model, a closed split integral torus with maximal split special fibre, and the
actual reductive special-fibre quotient, in which the torus image is maximal
split. Integral and radical-preimage root points are exactly the nonnegative and
strictly positive restricted root points. Every upper affine root vanishing at
the point with nonzero restricted derivative has, up to a nonzero scalar, the
form of a relative root whose specialization is a root of that quotient. -/
def UnramifiedFixedResidueRootModelStatement : Prop :=
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
        letI : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
        let fixed : D.Apartment → Prop := fun x =>
          ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val
        let φ : D.Apartment → RootFunctionFamily S G := fun x =>
          torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
            hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
            (D.isRootDatumValuation_of_mem x.mem)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
        let P := torusFieldTranslationMap F (inertiaFixedField F) f iT hiS.isSplitSubtorus.1
        let Q : RealTorusSpace.V S →ₗ[ℝ] TranslationSpace iS := (rootAnnihilator iS).mkQ
        ∀ (x : D.Apartment), fixed x →
          ∃ (D₀ : RelativeComponentModelData ↥𝒪[F] F G)
            (T₀ : IntegralTorusData D₀ S iS) (hT₀ : IsSplitTorus T₀.torus.toGrp)
            (Q₀ : SpecialFibreQuotientData D₀),
            IsClosedSubgroup T₀.inclusion ∧ T₀.HasMaximalSplitSpecialFibre ∧
            Q₀.IsReductiveQuotient ∧
            IsMaximalSplitTorus (T₀.specialFibreInclusion ≫ Q₀.projection) ∧
            (∀ a ∈ relativeRoots iS, ∀ g ∈ rootGroupPoints iS a,
              (g ∈ D₀.neutral.integralPoints ↔ 0 ≤ φ x a g) ∧
                (g ∈ Q₀.positivePoints ↔ 0 < φ x a g)) ∧
            ∀ (ψ : D.affineRoots), ψ.val x = 0 → ψ.val.linear.comp P ≠ 0 →
              ∃ a : relativeRoots iS,
                T₀.characterSpecialization hT₀ a ∈
                    relativeRoots (T₀.specialFibreInclusion ≫ Q₀.projection) ∧
                  ∃ c : ℝ, c ≠ 0 ∧
                    (rootForm iS a).comp Q = c • (ψ.val.linear.comp P)

end Langlands.Geometry.Building
