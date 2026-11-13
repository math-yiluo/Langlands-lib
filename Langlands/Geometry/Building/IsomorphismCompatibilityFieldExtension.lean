import Langlands.Geometry.Building.ValuationBuildingChartIsoTransport
import Langlands.Geometry.Building.ValuationBuildingChartIsoFieldRestriction
import Langlands.Geometry.Building.CentralizerDatumBaseChange
import Langlands.Geometry.Building.IntegerCentralizerFieldRestriction
import Langlands.Geometry.Building.OmegaCompatibleApartmentUniquenessProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.Geometry.Building.SplitTorusValuation

/-!
# Equivariant building isomorphisms across a field extension

For local fields `F₁ → F₂`, a group `G₁` over `F₁`, an isomorphism `f_G : G₁ ×_{F₁} F₂ ≅ G₂`
and valuation data `B₁`, `B₂`, the reduced buildings are equivariantly isomorphic along
`g ↦ f_G(g_{F₂})`, provided the extension preserves the normalized order, the rational-point
extension is bijective and reflects the normalizer of the torus of `B₁`, and the base change of
that torus stays maximal split. These hypotheses hold for an isomorphism of valued fields.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

namespace KPApartmentData.IsChartIso

variable {k₁ k₂ k₃ : Type u} [Field k₁] [Field k₂] [Field k₃]
  {S₁ : CommGroupScheme (Spec (CommRingCat.of k₁))}
  {G₁ : GroupScheme (Spec (CommRingCat.of k₁))} {i₁ : S₁.toGrp ⟶ G₁}
  [Mono i₁.hom.hom.left] [IsAffineHom G₁.X.hom] {ω₁ : k₁ˣ → ℝ}
  {S₂ : CommGroupScheme (Spec (CommRingCat.of k₂))}
  {G₂ : GroupScheme (Spec (CommRingCat.of k₂))} {i₂ : S₂.toGrp ⟶ G₂}
  [Mono i₂.hom.hom.left] [IsAffineHom G₂.X.hom] {ω₂ : k₂ˣ → ℝ}
  {S₃ : CommGroupScheme (Spec (CommRingCat.of k₃))}
  {G₃ : GroupScheme (Spec (CommRingCat.of k₃))} {i₃ : S₃.toGrp ⟶ G₃}
  [Mono i₃.hom.hom.left] [IsAffineHom G₃.X.hom] {ω₃ : k₃ˣ → ℝ}

/-- Existence of chart isomorphisms is transitive, composing the group homomorphisms. -/
theorem exists_trans {D₁ : KPApartmentData i₁ ω₁} {D₂ : KPApartmentData i₂ ω₂}
    {D₃ : KPApartmentData i₃ ω₃} {θ₁ : rationalPoints G₁ →* rationalPoints G₂}
    {θ₂ : rationalPoints G₂ →* rationalPoints G₃}
    (h₁ : ∃ (c : rationalPoints G₂) (e : D₁.Apartment ≃ᵃ[ℝ] D₂.Apartment)
      (Φ : D₁.ReducedBuilding ≃ D₂.ReducedBuilding), IsChartIso D₁ D₂ θ₁ c e Φ)
    (h₂ : ∃ (c : rationalPoints G₃) (e : D₂.Apartment ≃ᵃ[ℝ] D₃.Apartment)
      (Φ : D₂.ReducedBuilding ≃ D₃.ReducedBuilding), IsChartIso D₂ D₃ θ₂ c e Φ) :
    ∃ (c : rationalPoints G₃) (e : D₁.Apartment ≃ᵃ[ℝ] D₃.Apartment)
      (Φ : D₁.ReducedBuilding ≃ D₃.ReducedBuilding), IsChartIso D₁ D₃ (θ₂.comp θ₁) c e Φ := by
  obtain ⟨c₁, e₁, Φ₁, h₁⟩ := h₁
  obtain ⟨c₂, e₂, Φ₂, h₂⟩ := h₂
  exact ⟨_, _, _, h₁.trans h₂⟩

end KPApartmentData.IsChartIso

namespace ValuationBuildingData

variable {F₁ F₂ : Type u} [Field F₁] [ValuativeRel F₁] [TopologicalSpace F₁]
  [IsNonarchimedeanLocalField F₁] [Field F₂] [ValuativeRel F₂] [TopologicalSpace F₂]
  [IsNonarchimedeanLocalField F₂] [Algebra F₁ F₂]
  {G₁ : GroupScheme (Spec (CommRingCat.of F₁))} [IsAffineHom G₁.X.hom]
  {G₂ : GroupScheme (Spec (CommRingCat.of F₂))} [IsAffineHom G₂.X.hom]

local notation "b" => algebraBaseMap F₁ F₂

/-- **Axiom 4.1.17 across a field extension.** If `F₁ → F₂` preserves the normalized order,
`G₁(F₁) → G₁(F₂)` is bijective and reflects the normalizer of the torus of `B₁`, and the base
change of that torus is maximal split, then for every `f_G : G₁ ×_{F₁} F₂ ≅ G₂` the reduced
buildings of `B₁` and `B₂` are equivariantly isomorphic along `g ↦ f_G(g_{F₂})`. -/
theorem exists_isEquivariantBuildingIso_of_fieldExtension
    (fG : baseChanged F₁ F₂ G₁ ≅ G₂) (B₁ : ValuationBuildingData G₁)
    (B₂ : ValuationBuildingData G₂)
    (horder : ∀ t : F₁ˣ,
      localFieldOrder F₂ (Units.map (algebraMap F₁ F₂).toMonoidHom t) = localFieldOrder F₁ t)
    (hθ : Function.Bijective (rationalExtend F₁ F₂ G₁))
    (hN : ∀ g : rationalPoints G₁,
      rationalExtend F₁ F₂ G₁ g ∈ normalizerPoints (T := (CommGroupScheme.baseChange b).obj B₁.S)
          ((GroupScheme.baseChange b).map B₁.i) ↔ g ∈ normalizerPoints B₁.i)
    (hmax : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj B₁.S)
      ((GroupScheme.baseChange b).map B₁.i)) :
    ∃ Φ : B₁.ReducedBuilding ≃ B₂.ReducedBuilding,
      IsEquivariantBuildingIso B₁ B₂
        ((rationalPoints.map fG.hom).comp (rationalExtend F₁ F₂ G₁)) Φ := by
  have hG₁ := B₁.isConnectedReductive
  have : Smooth G₁.X.hom := hG₁.smooth
  have : IsAffineHom (baseChanged F₁ F₂ G₁).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G₁.X.hom b)
    infer_instance
  have : Mono ((GroupScheme.baseChange b).map B₁.i).hom.hom.left :=
    mono_of_isMaximalSplitTorus hmax
  have hS₁ : IsSplitTorus B₁.S.toGrp := B₁.isMaximalSplitTorus.1.1
  have hE₁ : RelativeRoot.HasOppositeFactorPairs B₁.i := by
    have hrank := rootRankOneFactorization.{u} F₁ G₁ hG₁ B₁.S B₁.i B₁.isMaximalSplitTorus
    exact fun a ha x hx hx1 => (hrank a ha x hx hx1).1.exists
  -- conjugate the base-changed torus onto the torus of `B₂`
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy.{u} F₂ G₂ B₂.isConnectedReductive).1
    ((CommGroupScheme.baseChange b).obj B₁.S) B₂.S
    ((GroupScheme.baseChange b).map B₁.i ≫ fG.hom) B₂.i (hmax.comp_iso fG)
    B₂.isMaximalSplitTorus
  let σS : (CommGroupScheme.baseChange b).obj B₁.S ≅ B₂.S :=
    { hom := Additive.ofMul e.hom
      inv := Additive.ofMul e.inv
      hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
      inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
  let F : baseChanged F₁ F₂ G₁ ≅ G₂ := fG ≪≫ G₂.innerIso g
  have h : (GroupScheme.baseChange b).map B₁.i ≫ F.hom =
      CommGroupScheme.groupHom σS.hom ≫ B₂.i := by
    rw [Iso.trans_hom, ← Category.assoc]
    exact he
  -- the apartment of `B₂` carried to the base-changed torus, with V6 for the base-changed
  -- centralizer of `B₁`
  let DK := B₂.apartment.transport σS.symm F.symm (torusTransport_inverse_square σS F h)
  let CK := B₁.centralizer.baseChangeOfBasedIso B₂.centralizer σS F h
  have hDK : DK.IsOmegaCompatible CK :=
    B₂.isOmegaCompatible.transport_basedIso B₂.centralizer CK σS.symm F.symm
      (torusTransport_inverse_square σS F h)
  -- integer orders
  let v := FML.normalizedMultiplicativeValuation F₁
  let w := FML.normalizedMultiplicativeValuation F₂
  have horder' : ∀ t : F₁ˣ, IntegerValuation.order w
      (Units.map (algebraMap F₁ F₂).toMonoidHom t) = IntegerValuation.order v t := by
    intro t
    rw [IntegerValuation.order_normalized, IntegerValuation.order_normalized]
    exact horder t
  let DK' := DK.reindexOrder (IntegerValuation.order_normalized F₂).symm
  have hDK' : IntegerValuation.IsOmegaCompatible w DK' CK :=
    (KPApartmentData.isOmegaCompatible_normalized F₂ DK CK).2 hDK
  have hν : ∃ t : F₁ˣ, IntegerValuation.order v t ≠ 0 := by
    refine ⟨SplitTorusValuation.uniformizerUnit F₁, ?_⟩
    rw [IntegerValuation.order_normalized]
    simp [localFieldOrder, SplitTorusValuation.fieldOrderUnits_uniformizerUnit]
  -- restriction to `F₁` and uniqueness
  let R := IntegerValuation.fieldRestrictApartment hS₁ v w horder' B₁.i hE₁ hν DK'
  have hR : IntegerValuation.IsOmegaCompatible v R B₁.centralizer :=
    IntegerValuation.fieldRestrictApartment_isOmegaCompatible hS₁ v w horder' B₁.i hE₁ hν DK'
      B₁.centralizer CK.bijective hDK'
  have hEq : R.reindexOrder (IntegerValuation.order_normalized F₁) = B₁.apartment := by
    apply omegaCompatibleApartmentUniqueness.{u} F₁ G₁ hG₁ B₁.S B₁.i B₁.isMaximalSplitTorus
      B₁.centralizer
    · apply (KPApartmentData.isOmegaCompatible_normalized F₁ _ B₁.centralizer).1
      rw [KPApartmentData.reindexOrder_symm]
      exact hR
    · exact B₁.isOmegaCompatible
  let ω : F₂ˣ →* Multiplicative ℝ :=
    (Int.castAddHom ℝ).toMultiplicative.comp (IntegerValuation.orderUnits w)
  have hω : ∃ t : F₁ˣ, (ω (Units.map (algebraMap F₁ F₂).toMonoidHom t)).toAdd ≠ 0 := by
    obtain ⟨t, ht⟩ := hν
    exact ⟨t, by change IntegerValuation.order w _ ≠ 0; rw [horder']; exact ht⟩
  have hω' : (fun t : F₁ˣ => (ω (Units.map (algebraMap F₁ F₂).toMonoidHom t)).toAdd) =
      IntegerValuation.order v :=
    funext horder'
  let FR := KPApartmentData.fieldRestrict B₁.i hS₁ hE₁ ω hω DK'
  have hRFR : R = FR.reindexOrder hω' :=
    KPApartmentData.ext (by rw [KPApartmentData.reindexOrder_carrier]; rfl)
  -- the chain of chart isomorphisms
  have c1 : ∃ (c : rationalPoints G₁)
      (e : B₁.Apartment ≃ᵃ[ℝ]
        (B₁.apartment.reindexOrder (IntegerValuation.order_normalized F₁).symm).Apartment)
      (Φ : B₁.ReducedBuilding ≃
        (B₁.apartment.reindexOrder (IntegerValuation.order_normalized F₁).symm).ReducedBuilding),
      B₁.apartment.IsChartIso
        (B₁.apartment.reindexOrder (IntegerValuation.order_normalized F₁).symm)
        (MonoidHom.id _) c e Φ :=
    ⟨1, _, _, KPApartmentData.isChartIso_reindexOrder _ _⟩
  have c2 : ∃ (c : rationalPoints G₁)
      (e : (B₁.apartment.reindexOrder (IntegerValuation.order_normalized F₁).symm).Apartment ≃ᵃ[ℝ]
        R.Apartment)
      (Φ : (B₁.apartment.reindexOrder
        (IntegerValuation.order_normalized F₁).symm).ReducedBuilding ≃ R.ReducedBuilding),
      (B₁.apartment.reindexOrder (IntegerValuation.order_normalized F₁).symm).IsChartIso R
        (MonoidHom.id _) c e Φ := by
    obtain ⟨e, Φ, hc⟩ := KPApartmentData.exists_isChartIso_of_eq
      (show B₁.apartment.reindexOrder (IntegerValuation.order_normalized F₁).symm = R by
        rw [← hEq, KPApartmentData.reindexOrder_symm])
    exact ⟨1, e, Φ, hc⟩
  have c3 : ∃ (c : rationalPoints G₁) (e : R.Apartment ≃ᵃ[ℝ] (R.reindexOrder hω'.symm).Apartment)
      (Φ : R.ReducedBuilding ≃ (R.reindexOrder hω'.symm).ReducedBuilding),
      R.IsChartIso (R.reindexOrder hω'.symm) (MonoidHom.id _) c e Φ :=
    ⟨1, _, _, KPApartmentData.isChartIso_reindexOrder _ _⟩
  have c4 : ∃ (c : rationalPoints G₁) (e : (R.reindexOrder hω'.symm).Apartment ≃ᵃ[ℝ] FR.Apartment)
      (Φ : (R.reindexOrder hω'.symm).ReducedBuilding ≃ FR.ReducedBuilding),
      (R.reindexOrder hω'.symm).IsChartIso FR (MonoidHom.id _) c e Φ := by
    obtain ⟨e, Φ, hc⟩ := KPApartmentData.exists_isChartIso_of_eq
      (show R.reindexOrder hω'.symm = FR by rw [hRFR, KPApartmentData.reindexOrder_symm])
    exact ⟨1, e, Φ, hc⟩
  have c5 : ∃ (c : rationalPoints (baseChanged F₁ F₂ G₁)) (e : FR.Apartment ≃ᵃ[ℝ] DK'.Apartment)
      (Φ : FR.ReducedBuilding ≃ DK'.ReducedBuilding),
      FR.IsChartIso DK' (rationalExtend F₁ F₂ G₁) c e Φ :=
    ⟨1, _, _, KPApartmentData.isChartIso_fieldRestrictBuildingEquiv B₁.i hS₁ hE₁ ω hω hθ hN DK'⟩
  have c6 : ∃ (c : rationalPoints (baseChanged F₁ F₂ G₁))
      (e : DK'.Apartment ≃ᵃ[ℝ]
        (DK'.reindexOrder (IntegerValuation.order_normalized F₂)).Apartment)
      (Φ : DK'.ReducedBuilding ≃
        (DK'.reindexOrder (IntegerValuation.order_normalized F₂)).ReducedBuilding),
      DK'.IsChartIso (DK'.reindexOrder (IntegerValuation.order_normalized F₂))
        (MonoidHom.id _) c e Φ :=
    ⟨1, _, _, KPApartmentData.isChartIso_reindexOrder _ _⟩
  have c7 : ∃ (c : rationalPoints (baseChanged F₁ F₂ G₁))
      (e : (DK'.reindexOrder (IntegerValuation.order_normalized F₂)).Apartment ≃ᵃ[ℝ] DK.Apartment)
      (Φ : (DK'.reindexOrder (IntegerValuation.order_normalized F₂)).ReducedBuilding ≃
        DK.ReducedBuilding),
      (DK'.reindexOrder (IntegerValuation.order_normalized F₂)).IsChartIso DK
        (MonoidHom.id _) c e Φ := by
    obtain ⟨e, Φ, hc⟩ := KPApartmentData.exists_isChartIso_of_eq
      (KPApartmentData.reindexOrder_symm DK (IntegerValuation.order_normalized F₂).symm)
    exact ⟨1, e, Φ, hc⟩
  have c8 : ∃ (c : rationalPoints G₂) (e : DK.Apartment ≃ᵃ[ℝ] B₂.Apartment)
      (Φ : DK.ReducedBuilding ≃ B₂.ReducedBuilding),
      DK.IsChartIso B₂.apartment (rationalPoints.map F.hom) c e Φ := by
    obtain ⟨e, Φ, hc⟩ := KPApartmentData.exists_isChartIso_transport_symm σS F h B₂.apartment
    exact ⟨1, e, Φ, hc⟩
  have c9 : ∃ (c : rationalPoints G₂) (e : B₂.Apartment ≃ᵃ[ℝ] B₂.Apartment)
      (Φ : B₂.ReducedBuilding ≃ B₂.ReducedBuilding),
      B₂.apartment.IsChartIso B₂.apartment (MulAut.conj g⁻¹).toMonoidHom c e Φ :=
    ⟨_, _, _, KPApartmentData.IsChartIso.smul B₂.apartment g⁻¹⟩
  obtain ⟨c, eA, Φ, hΦ⟩ := KPApartmentData.IsChartIso.exists_trans c1
    (KPApartmentData.IsChartIso.exists_trans c2
    (KPApartmentData.IsChartIso.exists_trans c3
    (KPApartmentData.IsChartIso.exists_trans c4
    (KPApartmentData.IsChartIso.exists_trans c5
    (KPApartmentData.IsChartIso.exists_trans c6
    (KPApartmentData.IsChartIso.exists_trans c7
    (KPApartmentData.IsChartIso.exists_trans c8 c9)))))))
  have hF : ∀ y : rationalPoints (baseChanged F₁ F₂ G₁),
      rationalPoints.map F.hom y = g * rationalPoints.map fG.hom y * g⁻¹ := by
    intro y
    change (y ≫ fG.hom.hom.hom) ≫ (G₂.innerIso g).hom.hom.hom = _
    rw [comp_innerIso_hom, constantPoint_self]
    rfl
  have hθeq : ((((((((MulAut.conj g⁻¹).toMonoidHom.comp (rationalPoints.map F.hom)).comp
      (MonoidHom.id _)).comp (MonoidHom.id _)).comp (rationalExtend F₁ F₂ G₁)).comp
      (MonoidHom.id _)).comp (MonoidHom.id _)).comp (MonoidHom.id _)) =
      (rationalPoints.map fG.hom).comp (rationalExtend F₁ F₂ G₁) := by
    apply MonoidHom.ext
    intro x
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, hF]
    group
  have hsurj : Function.Surjective ((rationalPoints.map fG.hom).comp (rationalExtend F₁ F₂ G₁)) :=
    (isoPointsEquiv fG (Over.mk (𝟙 _))).surjective.comp hθ.2
  rw [hθeq] at hΦ
  exact ⟨Φ, isEquivariantBuildingIso_of_isChartIso hsurj hΦ⟩

end ValuationBuildingData

end Langlands.Geometry.Building
