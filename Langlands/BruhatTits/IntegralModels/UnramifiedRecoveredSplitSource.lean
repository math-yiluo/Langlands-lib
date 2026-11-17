import Langlands.BruhatTits.IntegralModels.UnramifiedFixedSubsetModels
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredTorusClause
import Langlands.GroupScheme.Torus.UnipotentQuotientMaximalSplit

/-! # One integral split source for the generic group and a recovered quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 120000
set_option maxRecDepth 2500

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  {D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F))}
  (hG : IsConnectedReductive G)
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {iS : S.toGrp ⟶ G} {f : S ⟶ T}
  (hiS : IsMaximalSplitTorus iS)
  (hf : CommGroupScheme.groupHom f ≫ iT = iS)

namespace RecoveredApartmentFixerModels

include hG C hDC hiS hf in
/-- The same split integral torus has a maximal split generic map and a
maximal split residue map to every valid lower reductive quotient. -/
theorem exists_integralSplitSource {Ω : Set D.Apartment}
    (M : RecoveredApartmentFixerModels D Ω)
    (Q : SpecialFibreQuotientData M.lower) (hQ : Q.IsReductiveQuotient) :
    ∃ (A : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))),
      IsSplitTorus A.toGrp ∧
      ∃ a : ((CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj A).toGrp ⟶ G,
        IsMaximalSplitTorus a ∧
        ∃ s : ((CommGroupScheme.baseChange
            (Spec.algebraMap ↥𝒪[F] (IsLocalRing.ResidueField ↥𝒪[F]))).obj A).toGrp ⟶
            Q.quotient,
          IsMaximalSplitTorus s := by
  let A := M.lowerApartmentTorus C hDC hiS hf
  have hA : A.SatisfiesTorusClause :=
    M.lowerApartmentTorus_satisfiesTorusClause C hDC hiS hf hG
  have ha : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj A.torus)
      (A.genericIso.hom ≫ iS) :=
    IsMaximalSplitTorus.iso_comp
      (T' := (CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj A.torus)
      A.genericIso hiS
  refine ⟨A.torus, hA.1.1, A.genericIso.hom ≫ iS, ha,
    A.specialFibreInclusion ≫ Q.projection, ?_⟩
  let : Smooth Q.radical.X.hom := hQ.1.smooth
  let : ConnectedSpace Q.radical.X.left := hQ.1.connectedSpace
  let : Smooth Q.quotient.X.hom := hQ.2.2.smooth
  let : IsAffineHom M.lower.neutral.specialFibre.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd M.lower.neutral.group.X.hom
      (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  let : LocallyOfFiniteType M.lower.neutral.specialFibre.X.hom := by
    change LocallyOfFiniteType
      (CategoryTheory.Limits.pullback.snd M.lower.neutral.group.X.hom
        (IntegralModel.residueBaseMap ↥𝒪[F]))
    infer_instance
  exact (IsMaximalSplitTorus.comp_iff_of_perfect_field_unipotent_kernel
    Q.radicalInclusion hQ.1.isClosedSubgroup hQ.1.isUnipotent
    Q.projection hQ.2.1 A.specialFibreInclusion).mpr hA.2

end RecoveredApartmentFixerModels

/-- The source theorem specialized to the actual constructed models of a
coefficient-fixed apartment point. -/
def UnramifiedRecoveredSplitSourceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      haveI := mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
          (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
        (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
        (f : S ⟶ T),
        IsMaximalSplitTorus iS → CommGroupScheme.groupHom f ≫ iT = iS →
        ∀ (x : D.Apartment)
          (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
            RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val),
          let M := recoveredFixedPointModels D hG hiT C hDC x hx
          ∀ (Q : SpecialFibreQuotientData M.lower), Q.IsReductiveQuotient →
            ∃ (A : CommGroupScheme (Spec (CommRingCat.of ↥𝒪[F]))),
              IsSplitTorus A.toGrp ∧
              ∃ a : ((CommGroupScheme.baseChange
                  (Spec.algebraMap ↥𝒪[F] F)).obj A).toGrp ⟶ G,
                IsMaximalSplitTorus a ∧
                ∃ s : ((CommGroupScheme.baseChange
                    (Spec.algebraMap ↥𝒪[F]
                      (IsLocalRing.ResidueField ↥𝒪[F]))).obj A).toGrp ⟶ Q.quotient,
                  IsMaximalSplitTorus s

/-- Model recovery and the prescribed apartment torus construct the source
without an additional integral-torus or residue-rank premise. -/
theorem unramifiedRecoveredSplitSource :
    UnramifiedRecoveredSplitSourceStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  let := hG.isAffineHom
  intro hiT
  let := mono_of_isMaximalSplitTorus hiT
  intro D C hDC S iS f hiS hf x hx M Q hQ
  exact RecoveredApartmentFixerModels.exists_integralSplitSource
    hG C hDC hiS hf M Q hQ

end Langlands.BruhatTits.IntegralModels
