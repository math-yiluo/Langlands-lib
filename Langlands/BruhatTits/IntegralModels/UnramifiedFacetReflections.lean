import Langlands.BruhatTits.IntegralModels.IntegralTorusNormalizer
import Langlands.GroupScheme.Reductive.RootDatumFiniteWeylAssembly
import Langlands.Geometry.Building.FilteredRootReflectionCells
import Langlands.Geometry.Building.ChamberIwahoriProof
import Langlands.Geometry.Building.ValuationBuildingApartmentCharts
import Langlands.Geometry.Building.SimplyConnectedImageNormal
import Langlands.BruhatTits.SpecialCompact.LeviSpecialPoint
import Langlands.GroupScheme.SimplyConnected.FieldExtensionProof
import Langlands.GroupScheme.Derived.FieldBaseChangeAssembly
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.IntegralModel.UnramifiedModelDescent
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport

/-! # Actual integral reflection representatives for descended facet models -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

private instance extensionAffineHom :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (inertiaFixedField F)))
  infer_instance

/-- Scalar extension carries the actual simply connected image into the zero
subgroup of every supplied unramified zero datum. -/
theorem rationalExtend_mem_zeroPoints_of_mem_simplyConnectedImage
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    {x : rationalPoints G} (hx : x ∈ P.simplyConnectedImage) :
    rationalExtend F (inertiaFixedField F) G x ∈ E.zeroPoints := by
  let b := baseMap F (inertiaFixedField F)
  have hcover := P.zeroDatum.isSimplyConnectedDerivedCover
  have hcoverK : IsSimplyConnectedDerivedCover
      ((GroupScheme.baseChange b).map P.zeroDatum.d)
      ((GroupScheme.baseChange b).map P.zeroDatum.π) :=
    ⟨connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G
        hcover.isConnectedReductive,
      hcover.isDerivedSubgroup.baseChange_of_eq b
        (derivedSubgroup_baseChange_eq_of_field b G),
      isSimplyConnectedCover_fieldExtension F (inertiaFixedField F)
        P.zeroDatum.C P.zeroDatum.D P.zeroDatum.π hcover.isSimplyConnectedCover⟩
  apply E.simplyConnectedImage_le_zeroPoints
  change rationalExtend F (inertiaFixedField F) G x ∈
    Langlands.Geometry.Building.simplyConnectedImage E.d E.π
  rw [← Langlands.Geometry.Building.simplyConnectedImage_eq
    hcoverK E.isSimplyConnectedDerivedCover]
  obtain ⟨c, hc⟩ := Langlands.Geometry.Building.mem_simplyConnectedImage.mp hx
  refine Langlands.Geometry.Building.mem_simplyConnectedImage.mpr
    ⟨rationalExtend F (inertiaFixedField F) P.zeroDatum.C c, ?_⟩
  rw [← Functor.map_comp, ← rationalExtend_map, hc]

/-- A derivative of an affine root vanishing on the subset has an actual
normalizer representative fixing that subset, in the simply connected image,
with the coroot of any supplied relative-root reflection datum. -/
theorem exists_facetReflection_normalizer
    (hA : P.SatisfiesApartmentAxioms) (hR : P.HasRootReflections)
    (Droot : RelativeRootReflectionData P.i) (Fa : Set P.Apartment)
    (a : relativeRoots P.i)
    (ha : a.val ∈ facetDerivativeRoots P.toValuationBuildingData Fa) :
    ∃ n : normalizerPoints P.i,
      (n : rationalPoints G) ∈ P.simplyConnectedImage ∧
      (∀ y ∈ Fa, n • y = y) ∧
      ∀ χ : characterLattice P.S,
        weylAction P.i n χ = χ - latticePairing P.S χ (Droot.coroot a) • a.val := by
  obtain ⟨_, ψ, hψ, hlin, hzero⟩ := ha
  obtain ⟨β, hβ, hjump⟩ := P.apartment.affineRoots_subset_extendedAffineRoots hψ
  have hβα : β = a := Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split
    P.isMaximalSplitTorus.isSplitSubtorus.1 P.i (hβ.symm.trans hlin)
  subst β
  obtain ⟨u, hu, hnu⟩ : ∃ u ∈ P.affineRootGroup a ψ,
      u ∉ P.apartment.affineRootGroupPlus a ψ := by
    by_contra hcon
    push Not at hcon
    exact hjump (le_antisymm (P.apartment.affineRootGroupPlus_le a ψ) hcon)
  obtain ⟨huRoot, hu1, hlevel⟩ := P.reflectionFunctional_eq_of_mem_diff hlin hu hnu
  obtain ⟨p, hp⟩ := P.hasOppositeFactorPairs a a.property u huRoot hu1
  let n := P.reflectionElement hp
  obtain ⟨hpair, hact⟩ := hp.coroot_spec P.i
    P.isMaximalSplitTorus.isSplitSubtorus.1 a.property.1 huRoot hu1
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  let : Finite (weylImage P.i) := splitTorusWeylImageFinite F G P.S
    P.isMaximalSplitTorus.isSplitSubtorus.1 P.i P.isMaximalSplitTorus.isSplitSubtorus.2
  have hcoroot := coroot_eq_of_weylAction_of_finite_weylImage P.i
    P.isMaximalSplitTorus.isSplitSubtorus.1 hpair (Droot.pair_self a) hact (Droot.action a)
  refine ⟨n, P.reflectionElement_mem_simplyConnectedImage hA huRoot hu1 hp,
    fun y hy => ?_, fun χ => ?_⟩
  · apply hR a u huRoot hu1 p hp y
    rw [P.reflectionHyperplane_eq huRoot hu1, hlevel]
    exact hzero y hy
  · simpa only [hcoroot, n, ValuationBuildingData.reflectionElement] using hact χ

/-- A simply connected image point fixing an apartment subset, after conjugation,
belongs to every model with the specified unramified zero-point/fixer image. -/
theorem conjugated_normalizer_mem_integralPoints
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (e : P.ReducedBuilding → C.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints G) (Fa : Set P.Apartment)
    (D : RelativeComponentModelData ↥𝒪[F] F G)
    (hD : D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer
        (e '' (P.translatedApartmentMap g '' Fa)))
    (n : normalizerPoints P.i)
    (hsc : (n : rationalPoints G) ∈ P.simplyConnectedImage)
    (hfix : ∀ y ∈ Fa, n • y = y) :
    rationalPoints.map (G.innerIso g).hom n ∈ D.neutral.integralPoints := by
  apply (D.neutral.mem_integralPoints_rationalExtend_iff_unramified _).mp
  rw [hD]
  constructor
  · apply rationalExtend_mem_zeroPoints_of_mem_simplyConnectedImage P E
    exact map_simplyConnectedImage_le P.zeroDatum.isSimplyConnectedDerivedCover
      P.zeroDatum.isSimplyConnectedDerivedCover (G.innerIso g) ⟨n, hsc, rfl⟩
  · apply C.apartment.mem_pointwiseFixer.mpr
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← he]
    apply congrArg e
    change (n.val ≫ (G.innerIso g).hom.hom.hom) •
      (g • P.apartmentMap y) = g • P.apartmentMap y
    rw [comp_innerIso_hom, constantPoint_self, mul_smul, mul_smul,
      inv_smul_smul, P.normalizer_smul_apartmentMap n, hfix y hy]

/-- Each derivative facet root has an actual integral section normalizing the
conjugated torus, with the prescribed generic root-coroot reflection formula. -/
theorem exists_integral_facetReflection
    (hA : P.SatisfiesApartmentAxioms) (hR : P.HasRootReflections)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (e : P.ReducedBuilding → C.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints G) (Fa : Set P.Apartment)
    (D : RelativeComponentModelData ↥𝒪[F] F G)
    (hD : D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer
        (e '' (P.translatedApartmentMap g '' Fa)))
    (Droot : RelativeRootReflectionData P.i) (a : relativeRoots P.i)
    (ha : a.val ∈ facetDerivativeRoots P.toValuationBuildingData Fa) :
    ∃ (x : D.neutral.integralSections) (σ : P.S ≅ P.S),
      IsNormalizingPoint (P.i ≫ (G.innerIso g).hom)
        (D.neutral.integralPointMap x) σ ∧
      ∀ χ : characterLattice P.S,
        characterAut σ χ = χ - latticePairing P.S χ (Droot.coroot a) • a.val := by
  obtain ⟨n, hnsc, hnfix, hnact⟩ :=
    exists_facetReflection_normalizer P hA hR Droot Fa a ha
  obtain ⟨x, hx⟩ := (D.neutral.mem_integralPoints _).mp
    (conjugated_normalizer_mem_integralPoints P C e he E g Fa D hD n hnsc hnfix)
  refine ⟨x, normalizingAut P.i n, ?_, hnact⟩
  rw [hx]
  have hn := (isNormalizingPoint_normalizingAut P.i n).transport
    (j := P.i ≫ (G.innerIso g).hom) (Iso.refl P.S) (G.innerIso g)
    (by change _ = 𝟙 _ ≫ _; rw [Category.id_comp])
  simpa only [Iso.refl_symm, Iso.refl_trans, Iso.trans_refl,
    rationalPoints.map_apply] using hn

/-- An actual quotient normalizer representative and its automorphism of the
actual special torus, realizing the specialized prescribed coroot reflection. -/
def facetReflectionQuotientRepresentative
    (hA : P.SatisfiesApartmentAxioms) (hR : P.HasRootReflections)
    (C : MaximalUnramified.BuildingData F (baseChanged F (inertiaFixedField F) G))
    (e : P.ReducedBuilding → C.ReducedBuilding)
    (he : ∀ (g : rationalPoints G) (z : P.ReducedBuilding),
      e (g • z) = rationalExtend F (inertiaFixedField F) G g • e z)
    (E : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (g : rationalPoints G) (Fa : Set P.Apartment)
    (D : RelativeComponentModelData ↥𝒪[F] F G)
    (hD : D.neutral.baseChangeUnramified.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer
        (e '' (P.translatedApartmentMap g '' Fa)))
    (Q : SpecialFibreQuotientData D)
    (T : IntegralTorusData D P.S (P.i ≫ (G.innerIso g).hom))
    (hT : T.IsClosedSplit)
    (Droot : RelativeRootReflectionData P.i) (a : relativeRoots P.i)
    (ha : a.val ∈ facetDerivativeRoots P.toValuationBuildingData Fa) :
    {p : rationalPoints Q.quotient × (T.specialFibre ≅ T.specialFibre) //
      IsNormalizingPoint (T.specialFibreInclusion ≫ Q.projection) p.1 p.2 ∧
      ∀ χ : characterLattice T.specialFibre,
        characterAut p.2 χ =
          χ - latticePairing T.specialFibre χ
              (T.cocharacterSpecialization hT.1 (Droot.coroot a)) •
            T.characterSpecialization hT.1 a.val} := by
  apply Classical.choice
  obtain ⟨x, σ, hx, hσ⟩ :=
    exists_integral_facetReflection P hA hR C e he E g Fa D hD Droot a ha
  exact ⟨⟨(rationalPoints.map Q.projection (D.neutral.reduction x),
      T.specializedAutomorphism hT.1 σ),
    T.isNormalizingPoint_quotient Q hT x σ hx,
    T.characterAut_specialized_reflection hT.1 σ a.val (Droot.coroot a) hσ⟩⟩

end Langlands.BruhatTits.IntegralModels
