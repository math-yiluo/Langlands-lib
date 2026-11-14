import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelTorus
import Langlands.BruhatTits.IntegralModels.UnramifiedModelKernelReduction
import Langlands.Geometry.Building.UnramifiedSplitBoundedPoints
import Langlands.Geometry.Building.ScalarTorusUnitsFixApartment
import Langlands.Geometry.Building.SpecialTorusIntegralModelReduction
import Langlands.GroupScheme.IntegralModel.UnramifiedSplitMaximalTorus

/-! # Unipotence of the special-fibre kernel between unramified parahoric models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))} [IsAffineHom H.X.hom]

/-- **Bounded points of the maximal split torus lie in every `G(K)^0 ∩ G(K)_Ω`.** For building
data `C` of `H` over the maximal unramified extension `K`, a zero datum `E` and a subset `Ω`
of the apartment, the image of the character valuation kernel `S(K)^1` of the maximal split
torus `S` of `C` lies in `E(0) ∩ G(K)_Ω`. -/
theorem map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer
    (C : MaximalUnramified.BuildingData F H) (E : UnramifiedZeroDatum F H)
    (Ω : Set C.Apartment) :
    (characterValuationKernel (MaximalUnramified.valuation F) C.S.toGrp).map
        (rationalPoints.map C.i) ≤
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) := by
  intro x hx
  refine ⟨E.map_split_characterValuationKernel_le_zeroPoints C.isConnectedReductive C.S C.i
    C.isMaximalSplitTorus.1 hx, ?_⟩
  obtain ⟨s, hs, rfl⟩ := hx
  change rationalPoints.map C.i s ∈ C.apartment.pointwiseFixer _
  rw [KPApartmentData.mem_pointwiseFixer]
  rintro _ ⟨y, -, rfl⟩
  have h := KPApartmentData.map_torusUnits_smul_apartmentMap (MaximalUnramified.valuation F)
    C.apartment C.centralizer C.isOmegaCompatible (𝟙 C.S) s hs y
  rwa [show CommGroupScheme.groupHom (𝟙 C.S) ≫ C.i = C.i by
    rw [show CommGroupScheme.groupHom (𝟙 C.S) = 𝟙 C.S.toGrp from rfl, Category.id_comp]] at h

/-- **Unipotence of the special-fibre kernel between unramified parahoric models.** For
building data `C` of `H` over the maximal unramified extension `K`, a zero datum `E` and
subsets `Ω`, `Ω'` of the apartment, let `N` and `N'` be models of `H` over the integers of `K`,
with `N'` smooth, whose integral points contain `E(0) ∩ G(K)_Ω` and `E(0) ∩ G(K)_{Ω'}`. If the
kernel of the special-fibre map of a model morphism `N' → N` with identity generic fibre is
smooth and connected, it is unipotent. -/
theorem isUnipotent_kernel_specialFibreMap_of_apartment
    (C : MaximalUnramified.BuildingData F H) (E : UnramifiedZeroDatum F H)
    (Ω Ω' : Set C.Apartment)
    {N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) H}
    (hN' : N'.IsSmooth)
    (hpts : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) ≤ N.integralPoints)
    (hpts' : E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω') ≤ N'.integralPoints)
    (ψ : N'.Hom N (𝟙 H))
    [Smooth (kernel ψ.specialFibreMap).X.hom]
    [ConnectedSpace (kernel ψ.specialFibreMap).X.left] :
    IsUnipotent (kernel ψ.specialFibreMap) := by
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : Algebra 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (residueToFixedField F).toAlgebra
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  have : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  have : Smooth N'.group.X.hom := hN'
  exact IntegralModel.isUnipotent_kernel_specialFibreMap_of_bounded C.isConnectedReductive ψ
    (MaximalUnramified.valuation F) (SpecialTorusIntegralModel.valuation_units_eq_one F)
    C.isMaximalSplitTorus
    ((map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer C E Ω').trans hpts')
    ((map_characterValuationKernel_le_zeroPoints_inf_pointwiseFixer C E Ω).trans hpts)

private instance unramifiedModelKernelTorusAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- **KP Proposition 8.4.15 in the apartment: smoothness and connectedness.** The part of
`UnramifiedCompatibleModelKernelStatement` asserting only that the kernel of the special-fibre
map is smooth and connected, under the same hypotheses: no translation, the sets
`Ωa ⊆ closure Ωa'` taken in the apartment of `C`, and a zero datum `E` whose torus represents
the centralizer of the maximal split torus of `C`. This is an internal reduction target, not
a statement from the literature. -/
def UnramifiedCompatibleModelKernelSmoothConnectedStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G)),
    (torusCentralizer C.i).IsRepresentedBy E.i →
    ∀ (Ωa Ωa' : Set C.Apartment),
    Ωa.Nonempty →
    (∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa')) →
    Ωa ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ωa' →
    ∀ (N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
        (baseChanged F (inertiaFixedField F) G)),
      N.IsSmooth → N'.IsSmooth →
      N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa) →
      N'.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ωa') →
      ∀ ψ : N'.Hom N (𝟙 _),
        Smooth (kernel ψ.specialFibreMap).X.hom ∧
          ConnectedSpace (kernel ψ.specialFibreMap).X.left

set_option maxHeartbeats 1600000 in
/-- Smoothness and connectedness of the kernel give the whole compatible statement:
unipotence follows from `isUnipotent_kernel_specialFibreMap_of_apartment`. -/
theorem unramifiedCompatibleModelKernel_of_smoothConnected
    (h : UnramifiedCompatibleModelKernelSmoothConnectedStatement.{u}) :
    UnramifiedCompatibleModelKernelStatement.{u} := by
  intro F _ _ _ _ G _ C E hE Ωa Ωa' hne hbdd hcl N N' hN hN' hpts hpts' ψ
  obtain ⟨hs, hc⟩ := h F G C E hE Ωa Ωa' hne hbdd hcl N N' hN hN' hpts hpts' ψ
  exact ⟨hs, hc,
    isUnipotent_kernel_specialFibreMap_of_apartment C E Ωa Ωa' hN' hpts.ge hpts'.ge ψ⟩

/-- **KP Proposition 8.4.15 from its smooth-connected compatible case.** Given the
quasi-splitness of connected reductive groups over the maximal unramified extension and the
independence of `G(K)^0` from the zero datum, the smooth-connected part of the compatible
statement implies `UnramifiedModelKernelStatement`. -/
theorem unramifiedModelKernel_of_smoothConnected
    (hquasi : UnramifiedQuasiSplitStatement.{u})
    (hind : UnramifiedZeroPointsIndependenceStatement.{u})
    (h : UnramifiedCompatibleModelKernelSmoothConnectedStatement.{u}) :
    UnramifiedModelKernelStatement.{u} :=
  unramifiedModelKernel_of_compatible hquasi hind
    (unramifiedCompatibleModelKernel_of_smoothConnected h)

end Langlands.BruhatTits.IntegralModels
