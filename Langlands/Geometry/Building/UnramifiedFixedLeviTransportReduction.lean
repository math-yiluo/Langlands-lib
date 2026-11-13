import Langlands.Geometry.Building.UnramifiedFixedLeviTransportStatement
import Langlands.Geometry.Building.UnramifiedLeviSharpApartmentTransportStatement
import Langlands.Geometry.Building.UnramifiedNormalizerFixedApartmentLift
import Langlands.Geometry.Building.MaximalUnramifiedApartmentInjective
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Levi transport from a fixed-apartment lift and sharp apartment transport -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 200000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- If a product normalizes the apartment torus and its second factor is a sharp
fixer, its apartment action is determined by the quotient action of the first factor. -/
theorem KPApartmentData.normalizer_mul_smul_eq_of_mem_sharpFixer
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] {iT : T.toGrp ⟶ G} [Mono iT.hom.hom.left]
    {ω : kˣ → ℝ} (D : KPApartmentData iT ω)
    (hG : IsConnectedReductive G) (hiT : IsMaximalSplitTorus iT)
    (g h : rationalPoints G) (x y : D.Apartment)
    (hh : h ∈ D.sharpFixer {x})
    (hgh : g * h ∈ normalizerPoints iT)
    (hy : D.apartmentMap y = g • D.apartmentMap x) :
    (⟨g * h, hgh⟩ : normalizerPoints iT) • x = y := by
  apply D.apartmentMap_injective hG hiT
  rw [D.apartmentMap_smul]
  change (g * h) • D.apartmentMap x = D.apartmentMap y
  rw [mul_smul, D.mem_reducedFixer.1 (D.sharpFixer_le_reducedFixer x hh), hy]

/-- The two geometric prerequisites imply the unchanged Levi transport statement. -/
def UnramifiedFixedLeviTransportReductionStatement : Prop :=
  UnramifiedTorusUnitFixedApartmentStatement.{u} →
    UnramifiedLeviSharpApartmentTransportStatement.{u} →
      UnramifiedFixedLeviTransportStatement.{u}

/-- Fixed-apartment lifting supplies chart membership, Levi sharp transport supplies
its root-group correction, and apartment injectivity transfers coefficient fixedness. -/
theorem unramifiedFixedLeviTransport_of_fixedApartment_and_leviSharp :
    UnramifiedFixedLeviTransportReductionStatement.{u} := by
  intro hA hL F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : Mono iS.hom.hom.left := mono_of_isMaximalSplitTorus hiS
  intro hiT
  let : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C hDC
  dsimp only
  intro n x hx
  obtain ⟨y, hy, hmap⟩ := unramifiedNormalizerFixedApartmentLift
    F G hG S iS hiS T iT f hf hA hiT D C hDC n x hx
  let nK := normalizerPointsFieldExtend (K := inertiaFixedField F) iS n
  obtain ⟨h, hh, hlevi, hw⟩ := hL F G hG S iS hiS T iT f hf hiT D C hDC
    nK x ⟨y, hmap⟩
  refine ⟨h, hh, hlevi, hw, ?_⟩
  have hle : (⨆ (χ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T))
    (_ : χ ∈ relativeRoots
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (_ : (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f ≫
      χ = 0), D.filtration x χ 0) ≤ D.sharpFixer {x} :=
    iSup_le fun χ => iSup_le fun hχ => iSup_le fun _ => by
      rw [← D.rootFixer_singleton]
      exact D.rootFixer_le_sharpFixer ⟨χ, hχ⟩ {x}
  have hGK : IsConnectedReductive
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G) :=
    hG.baseChange_of_algebraicExtension (K := inertiaFixedField F)
  let : IsAffineHom
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G).X.hom :=
    hGK.isAffineHom
  have heq : D.normalizerAffineEquiv ⟨_, hw⟩ x = y :=
    KPApartmentData.normalizer_mul_smul_eq_of_mem_sharpFixer
      (k := inertiaFixedField F)
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      (G := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G)
      (iT := (GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
      (ω := IntegerValuation.order (MaximalUnramified.valuation F)) D hGK hiT
      (nK : rationalPoints ((GroupScheme.baseChange
        (algebraBaseMap F (inertiaFixedField F))).obj G)) h x y
      (hle hlevi) hw hmap
  rw [D.normalizerAffineEquiv_apply] at heq
  erw [heq]
  exact hy

end Langlands.Geometry.Building
