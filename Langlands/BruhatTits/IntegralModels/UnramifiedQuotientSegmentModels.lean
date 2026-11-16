import Langlands.Geometry.Building.ApartmentQuotientSegment
import Langlands.BruhatTits.IntegralModels.UnramifiedFixedBuildingPairRecovery
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.GeometricConnectedness

/-! # Actual quotient-fixed subsets and compatible segment models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.KPApartmentData

section General

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}
  (D : KPApartmentData i ω)

/-- The original pointwise-fixer subgroups of a closed segment and its
endpoint pair are literally equal. -/
theorem pointwiseFixer_chosenSegment_eq_pair
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hc : D.HasCommonApartments) (x y : D.ReducedBuilding) :
    D.pointwiseFixer (D.chosenSegment hc x y) = D.pointwiseFixer {x, y} := by
  ext g
  rw [D.mem_pointwiseFixer_chosenSegment_iff hG hi hc, D.mem_pointwiseFixer]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]

end General


end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.IntegralModels

open Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))

private instance unramifiedQuotientSegmentExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- Supplied smooth full models of a coefficient-fixed segment and its
endpoint pair are compatibly isomorphic, and share one actual descended
full/neutral model. -/
theorem exists_segment_pair_modelRecovery
    (hG : GeometricallyConnected G.X.hom)
    (hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G))
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hc : D.HasCommonApartments)
    (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
    (x y : D.ReducedBuilding)
    (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ x = x)
    (hy : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y)
    (E P : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hsegment : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.chosenSegment hc x y))
    (hpair : P.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer {x, y}) :
    ∃ e : E.full.Iso P.full (CategoryTheory.Iso.refl _),
      (E.neutralIso P e).iso.hom ≫ P.inclusion.hom = E.inclusion.hom ≫ e.iso.hom ∧
      E.neutral.integralPoints = P.neutral.integralPoints ∧
      ∃ L : RelativeComponentModelData ↥𝒪[F] F G,
        Nonempty (UnramifiedComponentModelRecovery L E) ∧
          Nonempty (UnramifiedComponentModelRecovery L P) := by
  have hpoints : E.full.integralPoints = P.full.integralPoints := by
    rw [hsegment, hpair, D.pointwiseFixer_chosenSegment_eq_pair hGK hiT hc]
  let e := IntegralModel.isoOfIntegralPointsEq E.full P.full
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
    E.full_smooth P.full_smooth hpoints
  refine ⟨e, E.neutralIso_hom_comp P e, E.neutral_integralPoints_eq P e, ?_⟩
  have hfixed : ∀ z ∈ D.chosenSegment hc x y,
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ z = z := by
    rintro z ⟨t, rfl⟩ σ
    exact KPApartmentData.galoisQuotientAction_chosenSegmentPoint_eq_of_endpoints_fixed
      F (inertiaFixedField F) iT D hD hGK hiT hc hx hy t σ
  obtain ⟨L, ⟨r⟩⟩ := exists_recovery_of_fixedBuildingSubset
    D hG hD (D.chosenSegment hc x y) hfixed E hsegment
  let e' : L.full.baseChangeUnramified.Iso P.full (CategoryTheory.Iso.refl _) :=
    { iso := r.fullIso.iso ≪≫ e.iso
      generic_comm := by
        change (GroupScheme.baseChange _).map (r.fullIso.iso.hom ≫ e.iso.hom) ≫
          P.full.genericIso.hom = _
        rw [CategoryTheory.Functor.map_comp, Category.assoc, e.generic_comm]
        simpa only [CategoryTheory.Iso.refl_hom, Category.comp_id] using
          r.fullIso.generic_comm }
  exact ⟨L, ⟨r⟩, ⟨UnramifiedComponentModelRecovery.ofFull L P e'⟩⟩

/-- From the original unramified apartment inputs, supplied segment and
endpoint-pair models have compatible full and neutral isomorphisms and one
common lower recovery. Neither model existence nor fixed coordinates are
additional conclusions of this statement. -/
def UnramifiedQuotientSegmentModelsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G),
    letI : IsAffineHom G.X.hom := hG.isAffineHom
    ∀ (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
      letI := mono_of_isMaximalSplitTorus hiT
      ∀ (D : KPApartmentData
        (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
        (IntegerValuation.order (MaximalUnramified.valuation F)))
        (C : CentralizerDatum
          (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
        (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
        (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
        (x y : D.ReducedBuilding),
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ x = x) →
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y) →
        let hc := MaximalUnramified.hasCommonApartments_of_apartment hG hiT D C h6
        ∀ E P : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
          (baseChanged F (inertiaFixedField F) G),
          E.full.integralPoints =
            characterValuationKernel (MaximalUnramified.valuation F)
                (baseChanged F (inertiaFixedField F) G) ⊓
              D.pointwiseFixer (D.chosenSegment hc x y) →
          P.full.integralPoints =
            characterValuationKernel (MaximalUnramified.valuation F)
                (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer {x, y} →
          ∃ e : E.full.Iso P.full (CategoryTheory.Iso.refl _),
            (E.neutralIso P e).iso.hom ≫ P.inclusion.hom =
              E.inclusion.hom ≫ e.iso.hom ∧
            E.neutral.integralPoints = P.neutral.integralPoints ∧
            ∃ L : RelativeComponentModelData ↥𝒪[F] F G,
              Nonempty (UnramifiedComponentModelRecovery L E) ∧
                Nonempty (UnramifiedComponentModelRecovery L P)

set_option maxHeartbeats 1600000 in
/-- Derive common apartments and geometric connectedness from the original
inputs, then compare and recover the supplied actual models. -/
theorem unramifiedQuotientSegmentModels :
    UnramifiedQuotientSegmentModelsStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  have : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD x y hx hy hc E P hsegment hpair
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have hgeo : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    hG.baseChange_of_algebraicExtension
  exact exists_segment_pair_modelRecovery D hgeo hGK hiT hc hD x y hx hy E P
    hsegment hpair

end Langlands.BruhatTits.IntegralModels
