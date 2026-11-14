import Langlands.Geometry.Building.UnramifiedZeroCentralizer
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylReduction
import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylAssembly
import Langlands.Geometry.Building.AffineChamberTransitivity
import Langlands.Geometry.Building.PointParahoricNormalizer
import Langlands.Geometry.Building.UnramifiedApartmentDescentStatement
import Langlands.Geometry.Building.KPZeroDatumExistence
import Langlands.Geometry.Building.GenericApartmentInjection
import Langlands.Geometry.Building.FacetFixingWeylReduction
import Langlands.Geometry.Building.ZeroSubgroupDatumIndependence
import Langlands.Geometry.Building.ValuationApartmentAxiomsExistenceStatement
import Langlands.Geometry.Building.UnramifiedZeroFacetNoInversionsStatement
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReductiveProof

/-! # Geometric steps in unramified zero descent -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

namespace Langlands.Geometry.Building

namespace AffineRootSystem

/-- An affine automorphism preserving the root set carries chambers to chambers. -/
private theorem IsChamber.image_of_mem_rootStabilizer
    {V A : Type u} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]
    {Ψ : Set (A →ᵃ[ℝ] ℝ)} {Ca : Set A} (hCa : IsChamber Ψ Ca)
    {e : A ≃ᵃ[ℝ] A} (he : e ∈ rootStabilizer Ψ) : IsChamber Ψ (e '' Ca) := by
  obtain ⟨x, hx, rfl⟩ := hCa
  refine ⟨e x, ?_, (image_facet he x).symm⟩
  intro ψ hψ
  exact hx (ψ.comp (e : A →ᵃ[ℝ] A)) ((comp_mem_iff he ψ).mpr hψ)

end AffineRootSystem

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- A simply connected image element corrects an arbitrary rational point to a
normalizer element preserving a prescribed apartment chamber. The only geometric
premise is the apartment axioms; the algebraic factorization and root-reflection
representatives are proved Library inputs. -/
theorem exists_simplyConnectedImage_mul_normalizer_stabilizing_chamber
    (hA : P.SatisfiesApartmentAxioms)
    {Ca : Set P.Apartment} (hCa : AffineRootSystem.IsChamber P.affineRoots Ca)
    (g : rationalPoints G) :
    ∃ c ∈ P.simplyConnectedImage, ∃ n : normalizerPoints P.i,
      c * g = (n : rationalPoints G) ∧ n • Ca = Ca := by
  obtain ⟨s, z, hg⟩ := simplyConnectedCentralizerProduct F P.S G P.centralizer.Z
    P.zeroDatum.C P.zeroDatum.D P.i P.centralizer.j P.zeroDatum.d P.zeroDatum.π
    P.zeroDatum.isSimplyConnectedDerivedCover P.isMaximalSplitTorus
    P.centralizer.isRepresentedBy g
  let c0 : rationalPoints G := rationalPoints.map (P.zeroDatum.π ≫ P.zeroDatum.d) s
  have hc0 : c0 ∈ P.simplyConnectedImage := ⟨s, rfl⟩
  let zN : normalizerPoints P.i := P.centralizer.toNormalizer z
  let e := P.apartment.normalizerAffineEquiv zN
  have he : e ∈ AffineRootSystem.rootStabilizer P.affineRoots :=
    AffineRootSystem.extendedAffineWeylGroup_le_rootStabilizer _
      (hA.range_le_extendedAffineWeylGroup ⟨zN, rfl⟩)
  have hCz := hCa.image_of_mem_rootStabilizer he
  obtain ⟨w, hw, -⟩ := affineChamberSimpleTransitivity (TranslationSpace P.i)
    P.Apartment P.affineRoots hA.isAffineRootSystem_affineRoots
    (e '' Ca) Ca hCz hCa
  let m := P.affineWeylRepresentative hA P.toValuationBuildingData.hasOppositeFactorPairs w
  have hm : P.apartment.normalizerAffineEquiv m = (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) :=
    P.normalizerAffineEquiv_affineWeylRepresentative hA
      P.toValuationBuildingData.hasOppositeFactorPairs w
  refine ⟨(m : rationalPoints G) * c0⁻¹,
    P.simplyConnectedImage.mul_mem (Subgroup.mem_subgroupOf.mp m.property)
      (P.simplyConnectedImage.inv_mem hc0),
    (m : normalizerPoints P.i) * zN, ?_, ?_⟩
  · change (m : rationalPoints G) * c0⁻¹ * g =
      (m : rationalPoints G) * rationalPoints.map P.centralizer.j z
    change g = c0 * rationalPoints.map P.centralizer.j z at hg
    rw [hg, mul_assoc, inv_mul_cancel_left]
  · change (fun x => ((m : normalizerPoints P.i) * zN) • x) '' Ca = Ca
    calc
      _ = P.apartment.normalizerAffineEquiv m '' (e '' Ca) := by
        rw [Set.image_image]
        apply Set.image_congr
        intro x _
        exact mul_smul (m : normalizerPoints P.i) zN x
      _ = (w : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' (e '' Ca) := by rw [hm]
      _ = Ca := hw

end ParahoricBuildingData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- A chamber-preserving normalizer point whose extension is a zero point acts
trivially on the apartment, provided facet descent and the upstairs
zero-facet property hold. -/
theorem normalizerAffineEquiv_eq_one_of_unramified_zero
    (hA : B.SatisfiesApartmentAxioms)
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
    (C : MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G))
    (e : B.ReducedBuilding → C.ReducedBuilding)
    (a : B.Apartment →ᵃ[ℝ] C.Apartment)
    (hinj : Function.Injective e)
    (hsmul : ∀ (g : rationalPoints G) (z : B.ReducedBuilding),
      e (g • z) = rationalExtend F (UnramifiedClosure F) G g • e z)
    (hapt : ∀ x : B.Apartment, e (B.apartmentMap x) = C.apartmentMap (a x))
    (hfacet : ∀ x : B.Apartment,
      a ⁻¹' AffineRootSystem.facet C.affineRoots (a x) =
        AffineRootSystem.facet B.affineRoots x)
    (hNoInv : ∀ (x y : C.Apartment) (g : rationalPoints (baseChanged F (UnramifiedClosure F) G)),
      y ∈ AffineRootSystem.facet C.affineRoots x → g ∈ E.zeroPoints →
        g • C.apartmentMap x = C.apartmentMap y → y = x)
    {Ca : Set B.Apartment} (hCa : AffineRootSystem.IsChamber B.affineRoots Ca)
    (n : normalizerPoints B.i)
    (hnK : rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G) ∈ E.zeroPoints)
    (hnCa : n • Ca = Ca) :
    B.apartment.normalizerAffineEquiv n = 1 := by
  apply AffineEquiv.ext_on
    (hCa.affineSpan_eq_top hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement)
  intro x hx
  have hnx : n • x ∈ Ca := by
    rw [← hnCa]
    exact ⟨x, hx, rfl⟩
  have hfx : AffineRootSystem.facet B.affineRoots x = Ca := by
    obtain ⟨w, _, hw⟩ := hCa
    have hxw : x ∈ AffineRootSystem.facet B.affineRoots w := by rwa [hw]
    exact (AffineRootSystem.facet_eq_of_mem hxw).trans hw
  have hfnx : a (n • x) ∈ AffineRootSystem.facet C.affineRoots (a x) := by
    change n • x ∈ a ⁻¹' AffineRootSystem.facet C.affineRoots (a x)
    rw [hfacet, hfx]
    exact hnx
  have hact : rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G) •
      C.apartmentMap (a x) = C.apartmentMap (a (n • x)) := by
    rw [← hapt, ← hsmul, B.normalizer_smul_apartmentMap, hapt]
  have hfix := hNoInv (a x) (a (n • x))
    (rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G)) hfnx hnK hact
  apply B.apartment.apartmentMap_injective B.isConnectedReductive B.isMaximalSplitTorus
  apply hinj
  rw [hapt, hapt]
  change C.apartmentMap (a (n • x)) = C.apartmentMap (a x)
  rw [hfix]

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- The reverse inclusion in unramified zero descent follows from supplied
apartment axioms, apartment descent, and the upstairs zero-facet property. -/
theorem comap_unramifiedZeroPoints_eq_of_geometric_inputs
    (hA : P.SatisfiesApartmentAxioms)
    (hDescent : UnramifiedApartmentDescentStatement.{u})
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
    (hNoInv : ∀ (C : MaximalUnramified.BuildingData F
        (baseChanged F (UnramifiedClosure F) G))
      (x y : C.Apartment) (g : rationalPoints (baseChanged F (UnramifiedClosure F) G)),
      y ∈ AffineRootSystem.facet C.affineRoots x → g ∈ E.zeroPoints →
        g • C.apartmentMap x = C.apartmentMap y → y = x) :
    E.zeroPoints.comap (rationalExtend F (UnramifiedClosure F) G) = P.zeroSubgroup := by
  apply le_antisymm
  · intro g hg
    obtain ⟨C, _, e, a, hinj, hsmul, hapt, _, _, _, hfacet, _⟩ :=
      hDescent F G P.isConnectedReductive P.toValuationBuildingData
    obtain ⟨x, hx⟩ :=
      hA.isAffineRootSystem_affineRoots.isLocallyFiniteReflectionArrangement.exists_regularPoint
    let Ca := AffineRootSystem.facet P.affineRoots x
    have hCa : AffineRootSystem.IsChamber P.affineRoots Ca := ⟨x, hx, rfl⟩
    obtain ⟨c, hc, n, hcg, hnCa⟩ :=
      P.exists_simplyConnectedImage_mul_normalizer_stabilizing_chamber hA hCa g
    have hcK : rationalExtend F (UnramifiedClosure F) G c ∈ E.zeroPoints :=
      E.simplyConnectedImage_le_zeroPoints
        (rationalExtend_mem_simplyConnectedImage F (UnramifiedClosure F)
          P.zeroDatum.isSimplyConnectedDerivedCover E.isSimplyConnectedDerivedCover hc)
    have hnK : rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G) ∈
        E.zeroPoints := by
      rw [← hcg, map_mul]
      exact E.zeroPoints.mul_mem hcK hg
    have hnact := P.toValuationBuildingData.normalizerAffineEquiv_eq_one_of_unramified_zero
      hA E C e a hinj hsmul hapt hfacet (hNoInv C) hCa n hnK hnCa
    have hncentral :=
      P.toValuationBuildingData.mem_centralizerPoints_of_normalizerAffineEquiv_eq_one n hnact
    rw [← torusCentralizer_carrier_base, ← P.centralizer.isRepresentedBy.2] at hncentral
    obtain ⟨z, hjz⟩ : ∃ z : rationalPoints P.centralizer.Z,
        rationalPoints.map P.centralizer.j z = (n : rationalPoints G) := hncentral
    have hzn : P.centralizer.toNormalizer z = n := Subtype.ext hjz
    have hnNorm : (n : rationalPoints G) ∈ Plancherel.rationalCommonNormKernel G := by
      rw [← characterValuationKernelDescent_proof F G]
      exact E.zeroPoints_le_characterValuationKernel hnK
    have hzNorm : z ∈ Plancherel.rationalCommonNormKernel P.centralizer.Z := by
      apply P.toValuationBuildingData.mem_rationalCommonNormKernel_of_smul_eq z
        (x := x)
      · rwa [hjz]
      · rw [hzn]
        exact congrArg (fun f : P.Apartment ≃ᵃ[ℝ] P.Apartment => f x) hnact
    have hzZero : z ∈ P.centralizerZero := by
      change z ∈ P.zeroDatum.centralizerZero
      rw [← P.zeroDatum.comap_unramifiedZeroPoints_inf_centralizerNormKernel E]
      refine ⟨?_, hzNorm⟩
      change rationalExtend F (UnramifiedClosure F) G
        (rationalPoints.map P.centralizer.j z) ∈ E.zeroPoints
      rwa [hjz]
    have hnZero : (n : rationalPoints G) ∈ P.zeroSubgroup := by
      rw [← hjz]
      exact P.zeroDatum.map_centralizerZero_le_zeroSubgroup ⟨z, hzZero, rfl⟩
    have hrecover : c⁻¹ * (n : rationalPoints G) = g := by
      rw [← hcg, inv_mul_cancel_left]
    rw [← hrecover]
    exact P.zeroSubgroup.mul_mem
      (P.zeroSubgroup.inv_mem (P.zeroDatum.simplyConnectedImage_le_zeroSubgroup hc)) hnZero
  · exact P.zeroDatum.zeroSubgroup_le_comap_unramifiedZeroPoints E

end ParahoricBuildingData

/-- The geometric reduction applies to every downstairs zero datum. Existence
chooses the building torus; independence of the downstairs zero subgroup removes
that choice. All three unresolved geometric inputs remain explicit. -/
theorem comap_unramifiedZeroPoints_eq_of_global_geometric_inputs
    (hExists : ValuationApartmentAxiomsExistenceStatement.{u})
    (hDescent : UnramifiedApartmentDescentStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
    (hNoInv : ∀ (C : MaximalUnramified.BuildingData F
        (baseChanged F (UnramifiedClosure F) G))
      (x y : C.Apartment) (g : rationalPoints (baseChanged F (UnramifiedClosure F) G)),
      y ∈ AffineRootSystem.facet C.affineRoots x → g ∈ E.zeroPoints →
        g • C.apartmentMap x = C.apartmentMap y → y = x)
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {Z : GroupScheme (Spec (CommRingCat.of F))}
    (i : S.toGrp ⟶ G) (j : Z ⟶ G) (Z0 : ZeroSubgroupDatum i j) :
    E.zeroPoints.comap (rationalExtend F (UnramifiedClosure F) G) = Z0.zeroSubgroup := by
  obtain ⟨B, hA⟩ := hExists F G hG
  obtain ⟨D, C, d, π, hcover⟩ := simplyConnectedDerivedCoverExistence F G hG
  have hZ : IsConnectedReductive B.centralizer.Z :=
    splitTorusCentralizerReductive F G hG B.S B.i B.isMaximalSplitTorus.1.1
      B.centralizer.Z B.centralizer.j B.centralizer.isRepresentedBy
  let EZ := UnramifiedZeroDatum.ofConnectedReductive
    (baseChanged F (UnramifiedClosure F) B.centralizer.Z)
    (connectedReductiveFieldExtensionStatement F (UnramifiedClosure F) B.centralizer.Z hZ)
  let P : ParahoricBuildingData G := {
    toValuationBuildingData := B
    zeroDatum := {
      isMaximalSplitTorus := B.isMaximalSplitTorus
      isRepresentedBy := B.centralizer.isRepresentedBy
      centralizerDatum := EZ
      D := D
      C := C
      d := d
      π := π
      isSimplyConnectedDerivedCover := hcover } }
  calc
    E.zeroPoints.comap (rationalExtend F (UnramifiedClosure F) G) = P.zeroSubgroup :=
      P.comap_unramifiedZeroPoints_eq_of_geometric_inputs hA hDescent E hNoInv
    _ = Z0.zeroSubgroup := P.zeroDatum.zeroSubgroup_eq_of_datum Z0

/-- Three geometric inputs suffice for clause 3 of unramified zero descent.
The conclusion retains every upstairs and downstairs zero datum. -/
def UnramifiedZeroDescentGeometricReductionStatement : Prop :=
  ValuationApartmentAxiomsExistenceStatement.{u} →
  UnramifiedApartmentDescentStatement.{u} →
  MaximalUnramified.ZeroFacetNoInversionsStatement.{u} →
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))), IsConnectedReductive G →
    ∀ (E : UnramifiedZeroDatum F (baseChanged F (UnramifiedClosure F) G))
      {S : CommGroupScheme (Spec (CommRingCat.of F))}
      {Z : GroupScheme (Spec (CommRingCat.of F))}
      (i : S.toGrp ⟶ G) (j : Z ⟶ G) (Z0 : ZeroSubgroupDatum i j),
      E.zeroPoints.comap (rationalExtend F (UnramifiedClosure F) G) = Z0.zeroSubgroup

/-- Apply the geometric argument and remove the building's choice of zero datum
using the published all-datum independence theorem. -/
theorem unramifiedZeroDescentGeometricReduction :
    UnramifiedZeroDescentGeometricReductionStatement.{u} := by
  intro hExists hDescent hNoInv F _ _ _ _ G hG E S Z i j Z0
  let : IsAffineHom G.X.hom := hG.isAffineHom
  exact comap_unramifiedZeroPoints_eq_of_global_geometric_inputs
    hExists hDescent F G hG E
    (fun C x y g hy hg hxy => hNoInv F _ C E x y g hy hg hxy) i j Z0

end Langlands.Geometry.Building
