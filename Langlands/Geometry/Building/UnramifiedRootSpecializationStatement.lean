import Langlands.BruhatTits.IntegralModels.RootSpecialization
import Langlands.BruhatTits.IntegralModels.DepthZeroInduction
import Langlands.Geometry.Building.SmoothRootModelLifting
import Langlands.Geometry.Building.UnramifiedRootJumpDescentStatement

/-! # Structural root specialization sufficient for unramified root-jump descent -/

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

namespace Langlands.BruhatTits.IntegralModels.IntegralRootSpecializationData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K] [HenselianLocalRing R]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {D : RelativeComponentModelData R K G}
  {S : CommGroupScheme (Spec (CommRingCat.of K))} {i : S.toGrp ⟶ G}
  {T : IntegralTorusData D S i} {hT : IsSplitTorus T.torus.toGrp}
  {Q : SpecialFibreQuotientData D} {a : characterLattice S}
  (A : IntegralRootSpecializationData T hT Q a)
  (φ : Langlands.Geometry.Building.RootFunctionFamily S G)

/-- The supplied actual residue-root quotient produces a generic value-zero
point when its integral values and positive-value kernel are compatible. -/
theorem exists_zero_rootPoint (hQ : Q.IsReductiveQuotient)
    (hc : Langlands.Geometry.Building.RootModelReductionCompatible
      a A.genericInclusion A.model φ A.residueProjection) :
    ∃ g : rationalPoints G,
      g ∈ Langlands.Geometry.Building.rootGroupPoints i a ∧ φ a g = (0 : WithTop ℝ) := by
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  exact Langlands.Geometry.Building.exists_zero_rootPoint_of_quotient_root
    A.representsGenericRoot A.model_smooth hc
    A.kernelInclusion A.kernel_closed A.kernel_split A.isQuotient
    (hT.baseChange (IntegralModel.residueBaseMap R))
    (T.specialFibreInclusion ≫ Q.projection) A.residue_root
    A.residueInclusion A.representsResidueRoot

end Langlands.BruhatTits.IntegralModels.IntegralRootSpecializationData

namespace Langlands.Geometry.Building

set_option maxHeartbeats 1000000 in
/-- Internal geometric existence target. A single actual downstairs model and
quotient at each fixed upper point supply compatible surviving residue roots
for all relevant vanishing upper affine roots, allowing proportional forms. -/
def UnramifiedRootSpecializationStatement : Prop :=
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
            ∀ (ψ : D.affineRoots), ψ.val x = 0 → ψ.val.linear.comp P ≠ 0 →
              ∃ (a : relativeRoots iS) (A : IntegralRootSpecializationData T₀ hT₀ Q₀ a),
                RootModelReductionCompatible a A.genericInclusion A.model (φ x)
                  A.residueProjection ∧
                ∃ c : ℝ, c ≠ 0 ∧
                  (rootForm iS a).comp Q = c • (ψ.val.linear.comp P)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option maxHeartbeats 2000000 in
/-- Structural specialization and the actual lifting theorem imply the exact
published root-jump descent statement, without an additional premise. -/
theorem unramifiedRootJumpDescent_of_rootSpecialization
    (h : UnramifiedRootSpecializationStatement.{u}) :
    UnramifiedRootJumpDescentStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hfactor hiT hE D C hΩ
  let : HenselianLocalRing ↥𝒪[F] := henselianLocalRing_integer
  intro fixed φ P Q x hx ψ hψ hnonzero
  have hpoint := h F G hG S iS hiS T iT f hfactor hiT hE D C hΩ x hx
  obtain ⟨D₀, T₀, hT₀, Q₀, _, _, hQ₀, _, hroots⟩ :=
    hpoint
  have hroot0 := hroots ψ
  have hroot1 := hroot0 hψ
  have hroot := hroot1 hnonzero
  obtain ⟨a, A, hc, c, hc0, hforms⟩ := hroot
  obtain ⟨g, hg, hzero⟩ := A.exists_zero_rootPoint _ hQ₀ hc
  refine ⟨a, g, hg, hzero, ?_⟩
  exact (congrArg LinearMap.ker hforms).trans (LinearMap.ker_smul _ c hc0)

end Langlands.Geometry.Building
