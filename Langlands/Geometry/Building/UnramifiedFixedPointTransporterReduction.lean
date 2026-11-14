import Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentStatement
import Langlands.Geometry.Building.UnramifiedFixedPointTransporterStatement
import Langlands.Geometry.Building.UnramifiedLeviSharpApartmentTransportProof
import Langlands.Geometry.Building.TorusUnitApartmentFixation

/-! # Reduction of the split-centralizing transporter to two fixed points in one apartment -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- The depth-zero root groups of a point generate a subgroup fixing its image in the
reduced building. -/
theorem KPApartmentData.iSup_filtration_le_reducedFixer {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G} [Mono i.hom.hom.left]
    [IsAffineHom G.X.hom] {ω : kˣ → ℝ} (D : KPApartmentData i ω) (x : D.Apartment)
    (p : characterLattice S → Prop) :
    (⨆ (χ : characterLattice S) (_ : χ ∈ relativeRoots i) (_ : p χ), D.filtration x χ 0) ≤
      D.reducedFixer (D.apartmentMap x) := by
  refine le_trans ?_ (D.sharpFixer_le_reducedFixer x)
  refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun _ => ?_
  rw [← D.rootFixer_singleton]
  exact D.rootFixer_le_sharpFixer ⟨χ, hχ⟩ {x}

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Reduction.** The two-point special-apartment statement, together with the published
Levi sharp transport `unramifiedLeviSharpApartmentTransport`, implies the
split-centralizing transporter statement. -/
theorem unramifiedFixedPointTransporter_of_fixedPairSpecialApartment
    (hPair : UnramifiedFixedPairSpecialApartmentStatement.{u}) :
    UnramifiedFixedPointTransporterStatement.{u} := by
  intro F iF iV iTop iL G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  have : Mono ((GroupScheme.baseChange
      (baseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD x₀ hx₀ y hyΓ hyS
  have hx₀Γ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ
        (D.apartmentMap x₀) = D.apartmentMap x₀ := by
    intro σ
    have hσ : KPApartmentData.galoisAction F (inertiaFixedField F) iT D hD σ x₀ = x₀ :=
      KPApartmentData.Apartment.ext (hx₀ σ)
    exact (KPApartmentData.galoisQuotientAction_apartmentMap F (inertiaFixedField F) iT D hD
      σ x₀).trans (congrArg D.apartmentMap hσ)
  have hx₀S : IsFixedByUnramifiedTorusUnits F iS (D.apartmentMap x₀) := by
    have h := isFixedByScalarTorusUnits_apartmentMap F (inertiaFixedField F)
      (MaximalUnramified.valuation F) iT (CommGroupScheme.groupHom f) D C h6 x₀
    rwa [hf] at h
  obtain ⟨g, hgC, hgN, ⟨x₂, hx₂⟩, ⟨x₁, hx₁⟩⟩ :=
    @hPair F iF iV iTop iL G hG S iS hiS T iT f hf hiT D C h6 hD (D.apartmentMap x₀) y hx₀Γ hx₀S
      hyΓ hyS
  let n : normalizerPoints
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) :=
    ⟨g⁻¹, centralizerPoints_le_normalizerPoints _ (inv_mem hgC)⟩
  obtain ⟨h, hhC, hhU, hm⟩ := @unramifiedLeviSharpApartmentTransport F iF iV iTop iL G hG S iS hiS
    T iT f hf hiT D C h6 n x₀ ⟨x₂, eq_inv_smul_iff.mpr hx₂⟩
  change g⁻¹ * h ∈ _ at hm
  refine ⟨h, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [rationalPoints.map_apply]
    exact commute_of_mem_centralizerPoints _ hhC s
  · exact D.mem_reducedFixer.1 (D.iSup_filtration_le_reducedFixer x₀ _ hhU)
  · intro σ
    have key : h⁻¹ * rationalConjugate F (inertiaFixedField F) G σ h =
        (g⁻¹ * h)⁻¹ * (g⁻¹ * rationalConjugate F (inertiaFixedField F) G σ g) *
          rationalConjugate F (inertiaFixedField F) G σ (g⁻¹ * h) := by
      rw [map_mul, map_inv]
      group
    rw [key]
    exact mul_mem (mul_mem (inv_mem hm) (hgN σ))
      (rationalConjugate_mem_normalizerPoints F (inertiaFixedField F) iT σ hm)
  · refine ⟨(⟨(g⁻¹ * h)⁻¹, inv_mem hm⟩ : normalizerPoints
        (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
        ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)) • x₁, ?_⟩
    rw [D.apartmentMap_smul, ← hx₁, smul_smul]
    congr 1
    change h * (g⁻¹ * h)⁻¹ = g
    group

end Langlands.Geometry.Building
