import Langlands.Geometry.Building.AffineRootRestriction
import Langlands.Geometry.Building.FullValidity.Assignment
import Langlands.Geometry.Building.IntegerBuildingFacetClosure
import Langlands.Geometry.Building.SplitTorusTranslationBaseChange
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.GroupScheme.IntegralModel.Iso
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent

/-! # Unramified descent of KP building data (Axiom 4.1.27) -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.KPBuildingDatum

open BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

local notation "Fᵘʳ" => inertiaFixedField F
local notation "G_K" => baseChanged F Fᵘʳ G
local notation "b" => algebraBaseMap F Fᵘʳ

private instance unramifiedAffineHom : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable (D : KPBuildingDatum G)

/-- The special tori containing the maximal split torus of the chart `g · A(S)`. -/
def IsSpecialTorusInChart (g : rationalPoints G)
    {T : CommGroupScheme (Spec (CommRingCat.of F))} (iT : T.toGrp ⟶ G)
    (f : D.base.S ⟶ T) : Prop :=
  IsTorus T.toGrp ∧ IsClosedSubgroup iT ∧
    CommGroupScheme.groupHom f ≫ iT = D.base.i ≫ (G.innerIso g).hom ∧
    IsMaximalSplitTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map iT)

/-- UR 2 and the set equality of UR 3 for every translated apartment and every
special torus containing its maximal split torus. An upstairs chart for `T_K`
is a translate of the apartment of `C`, with its torus identified with `T_K`
by conjugation. -/
def HasUnramifiedApartmentComparison
    (C : MaximalUnramified.BuildingData F G_K)
    (Γ : MaximalUnramified.SemilinearApartmentData (G := G) C)
    (e : D.base.ReducedBuilding → C.ReducedBuilding) : Prop :=
  ∀ g : rationalPoints G,
    (∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G)
      (f : D.base.S ⟶ T), D.IsSpecialTorusInChart g iT f) ∧
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G)
      (f : D.base.S ⟶ T), D.IsSpecialTorusInChart g iT f →
      ∃ (h : rationalPoints G_K) (t : C.S ≅ (CommGroupScheme.baseChange b).obj T)
        (a : D.base.toValuationBuildingData.Apartment →ᵃ[ℝ] C.Apartment),
        let fK := (CommGroupScheme.baseChange b).map f ≫ t.inv
        C.i ≫ ((G_K).innerIso h).hom = CommGroupScheme.groupHom t.hom ≫
          (GroupScheme.baseChange b).map iT ∧
        Function.Injective a ∧
        (∀ x, e (D.base.translatedApartmentMap g x) = C.translatedApartmentMap h (a x)) ∧
        Set.range a = {y | ∀ σ : Fᵘʳ ≃ₐ[F] Fᵘʳ,
          Γ.action σ (C.translatedApartmentMap h y) = C.translatedApartmentMap h y} ∧
        a.linear.comp (rootAnnihilator D.base.i).mkQ =
          (rootAnnihilator C.i).mkQ.comp ((cocharacterMapReal fK).comp
            (splitCocharacterBaseChange (K := Fᵘʳ) D.base.S
              D.base.isMaximalSplitTorus.isSplitSubtorus.1).toLinearMap) ∧
        AffineRootSystem.restrictedRoots a C.affineRoots = D.base.affineRoots

/-- UR 4 for every actual nonempty bounded apartment subset. The upper models
are characterized by their integral point subgroups at `e '' Ω`. Both
generic-identity isomorphisms and both fixer intersection identities are required. -/
def HasUnramifiedModelComparison
    (C : MaximalUnramified.BuildingData F G_K)
    (e : D.base.ReducedBuilding → C.ReducedBuilding) (E : UnramifiedZeroDatum F G_K) : Prop :=
  ∀ Ω : BuildingModelIndex D.base.toValuationBuildingData,
    IsNonemptyBoundedApartmentSubset D.base.toValuationBuildingData Ω.val →
    let ΩK : Set C.ReducedBuilding := e '' Ω.val
    let fixer := IntegerValuationBuildingData.pointwiseFixer (G := G_K) C ΩK
    let oneFixer : Subgroup (rationalPoints G_K) :=
      characterValuationKernel (MaximalUnramified.valuation F) G_K ⊓ fixer
    let zeroFixer : Subgroup (rationalPoints G_K) := E.zeroPoints ⊓ fixer
    let M := D.models.model Ω
    ∃ N : RelativeComponentModelData (fixedFieldIntegers F) Fᵘʳ G_K,
      N.full.integralPoints = oneFixer ∧ N.neutral.integralPoints = zeroFixer ∧
      Nonempty (M.full.baseChangeUnramified.Iso N.full (CategoryTheory.Iso.refl G_K)) ∧
      Nonempty (M.neutral.baseChangeUnramified.Iso N.neutral (CategoryTheory.Iso.refl G_K)) ∧
      BuildingModelFamily.oneFixer Ω = oneFixer.comap (rationalExtend F Fᵘʳ G) ∧
      BuildingModelFamily.zeroFixer D.base Ω = zeroFixer.comap (rationalExtend F Fᵘʳ G)

/-- UR 1–UR 4 for the building and coefficient action specified below. -/
private def hasUnramifiedDescentWithAction
    (C : MaximalUnramified.BuildingData F G_K)
    (Γ : MaximalUnramified.SemilinearApartmentData (G := G) C) : Prop :=
  ∃ e : D.base.ReducedBuilding → C.ReducedBuilding,
    Function.Injective e ∧
    (∀ (g : rationalPoints G) (x : D.base.ReducedBuilding),
      e (g • x) = rationalExtend F Fᵘʳ G g • e x) ∧
    Set.range e = {y | ∀ σ : Fᵘʳ ≃ₐ[F] Fᵘʳ, Γ.action σ y = y} ∧
    D.HasUnramifiedApartmentComparison C Γ e ∧
    ∃ E : UnramifiedZeroDatum F G_K, D.HasUnramifiedModelComparison C e E

/-- Unramified descent over a nonarchimedean local field (KP Axiom 4.1.27,
with UR 3 in its set-equality form). The coefficient action on the valuation
apartment of a special `F`-torus induces the semilinear action on the upper
reduced building. UR 1 gives an equivariant embedding of the given reduced
building onto its fixed locus, and UR 2–UR 4 use that same embedding. -/
def SatisfiesUnramifiedDescent : Prop :=
  ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G)
    (f : D.base.S ⟶ T) (hT : D.IsSpecialTorusInChart 1 iT f),
    let hiT := hT.2.2.2
    letI := mono_of_isMaximalSplitTorus hiT
    ∃ (hGK : IsConnectedReductive G_K)
      (A : KPApartmentData (S := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map iT)
        (IntegerValuation.order (MaximalUnramified.valuation F)))
      (Z : CentralizerDatum (S := (CommGroupScheme.baseChange b).obj T)
        ((GroupScheme.baseChange b).map iT))
      (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) A Z)
      (hA : KPApartmentData.GaloisStable F Fᵘʳ iT A),
      let C := UnramifiedBuildingDescent.buildingData iT hGK hiT A Z h6
      let Γ := UnramifiedBuildingDescent.semilinearData iT hGK hiT Z h6 hA
      D.hasUnramifiedDescentWithAction C Γ

end Langlands.Geometry.Building.KPBuildingDatum
