import Langlands.Geometry.Building.UnramifiedSpecialApartmentChamberStatement
import Langlands.Geometry.Building.UnramifiedGaloisFixedApartmentProof
import Langlands.Geometry.Building.AffineInvariantRegularPoint
import Langlands.Geometry.Building.IntegerAffineRootLocalFiniteness
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # A fixed-direction criterion for special-apartment chambers -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)

private instance extendedAffine : IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ω)

/-- Every ordinary affine root through `p` is nonzero on a common fixed
direction of the actual coefficient action. -/
def HasIncidentGaloisDirections (p : D.Apartment) : Prop :=
  ∀ ψ ∈ D.affineRoots, ψ p = 0 →
    ∃ v : TranslationSpace
        (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        ((GroupScheme.baseChange (algebraBaseMap k K)).map i),
      (∀ σ : K ≃ₐ[k] K, galoisTranslationAction k K i σ v = v) ∧
        ψ.linear v ≠ 0

variable {v : Valuation K (WithZero (Multiplicative ℤ))}
  (D' : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i) (IntegerValuation.order v))
  (hG : IsConnectedReductive (baseChanged k K G))
  (hi : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
  (h6 : IntegerValuation.IsOmegaCompatible v D' C)
  (hD : GaloisStable k K i D')

include hG hi C h6

/-- The incident-root direction condition at a fixed point yields an ordinary
coefficient-stable chamber in this same supplied integer-valued apartment. -/
theorem exists_regular_galois_stable_facet_of_directions
    (p : D'.Apartment)
    (hp : ∀ σ : K ≃ₐ[k] K, galoisAffineAction k K i D' hD σ p = p)
    (hdir : HasIncidentGaloisDirections k K i D' p) :
    ∃ x : D'.Apartment, AffineRootSystem.GalleryGeometry.IsRegular D'.affineRoots x ∧
      ∀ σ : K ≃ₐ[k] K,
        galoisAffineAction k K i D' hD σ '' AffineRootSystem.facet D'.affineRoots x =
          AffineRootSystem.facet D'.affineRoots x := by
  let B := integerBuildingData D' hG hi C h6
  have hΨ : AffineRootSystem.IsLocallyFiniteReflectionArrangement D'.affineRoots :=
    B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs B.hasOppositeFactorPairs
  obtain ⟨x, hx, _, hxfix⟩ := hΨ.exists_regularPoint_fixed
    (fun σ => galoisAffineAction k K i D' hD σ) p hp hdir
  refine ⟨x, hx, fun σ => ?_⟩
  change galoisAction k K i D' hD σ '' AffineRootSystem.facet D'.affineRoots x = _
  rw [image_facet_galois, ← galoisAffineAction_apply, hxfix σ]

end KPApartmentData

private instance unramifiedRegularDirectionAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- The remaining arithmetic input to the invariant-direction construction:
incident ordinary roots are nonzero on coefficient-fixed directions in every
supplied compatible special apartment, at every coefficient-fixed point. -/
def UnramifiedSpecialApartmentRegularDirectionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G),
    IsMaximalSplitTorus iS →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G)
      (f : S ⟶ T),
      CommGroupScheme.groupHom f ≫ iT = iS →
      IsClosedSubgroup iT →
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
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)),
          IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C →
          ∀ (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
            (p : D.Apartment),
            (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
              KPApartmentData.galoisAffineAction F (inertiaFixedField F) iT D hD σ p = p) →
            KPApartmentData.HasIncidentGaloisDirections F (inertiaFixedField F) iT D p

set_option maxHeartbeats 8000000 in
/-- The direction statement, together with published fixed-point and local
finiteness results, proves the unchanged special-apartment chamber statement. -/
theorem unramifiedSpecialApartmentChamber_of_regularDirection
    (hdir : UnramifiedSpecialApartmentRegularDirectionStatement.{u}) :
    UnramifiedSpecialApartmentChamberStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf hclosed
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD
  obtain ⟨p, hp⟩ := unramifiedGaloisFixedApartment F G hG T iT hiT D hD
  have hp' : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisAffineAction F (inertiaFixedField F) iT D hD σ p = p := by
    intro σ
    apply KPApartmentData.Apartment.ext
    exact hp σ
  exact KPApartmentData.exists_regular_galois_stable_facet_of_directions
    F (inertiaFixedField F) iT D
    (hG.baseChange_of_algebraicExtension (K := inertiaFixedField F)) hiT C h6 hD p hp'
    (hdir F G hG S iS hiS T iT f hf hclosed hiT D C h6 hD p hp')

end Langlands.Geometry.Building
