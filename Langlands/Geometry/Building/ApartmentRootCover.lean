import Langlands.Geometry.Building.KPApartmentAxioms
import Langlands.GroupScheme.Derived.SplitTorusCommutators
import Langlands.GroupScheme.Derived.DynamicRootContainment
import Langlands.GroupScheme.Dynamic.CentralIsogenyRationalLift
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.SimplyConnected.DerivedCover
import Langlands.Geometry.Building.KPSharpCoverImageStatement

/-! # Actual root points lift through the derived cover under apartment axioms -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    (A : KPApartmentData i (localFieldOrder k)) (Z : CentralizerDatum i)

namespace KPApartmentData

/-- The apartment axioms supply, for each actual root, a positive contracting
cocharacter whose full image lies in the actual derived subgroup. -/
theorem exists_positive_derived_cocharacter (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (a : relativeRoots i) :
    ∃ ν : cocharacterLattice T, 0 < latticePairing T a.val ν ∧
      ν ∈ cocharactersLandingIn i (derivedSubgroup G) := by
  have hroot : rootForm i a ∈ AffineRootSystem.derivativeRoots A.affineRoots := by
    rw [hA.derivativeRoots_affineRoots]
    exact Set.mem_range_self a
  obtain ⟨ψ, hψ, hψlin⟩ := hroot
  obtain ⟨v, hv⟩ := hA.isAffineRootSystem_affineRoots.exists_isCoroot ψ hψ
  obtain ⟨n, hn⟩ := hA.affineWeylGroup_le_range
    (AffineRootSystem.affineReflection_mem_affineWeylGroup hψ hv)
  have hlin : translationAction i n = (AffineRootSystem.affineReflection ψ hv.1).linear :=
    congrArg (fun e : A.Apartment ≃ᵃ[ℝ] A.Apartment => e.linear) hn
  have hflip (x : TranslationSpace i) :
      rootForm i a (translationAction i n x) = -rootForm i a x := by
    rw [hlin, AffineRootSystem.affineReflection_linear, ← hψlin, Module.reflection_apply]
    simp only [map_sub, map_smul, hv.1, smul_eq_mul]
    ring
  obtain ⟨N, hN, ν, hν⟩ := hT.exists_pairing_eq_pos a.property.1
  have hpair : latticePairing T a.val (ν ≫ (normalizingAut i n).hom) =
      -latticePairing T a.val ν := by
    have h := hflip (Submodule.Quotient.mk ((1 : ℝ) ⊗ₜ[ℤ] ν))
    rw [translationAction_mk, rootForm_mk, rootForm_mk] at h
    change eval T a.val (normalizerAction i n ((1 : ℝ) ⊗ₜ[ℤ] ν)) = _ at h
    simpa only [normalizerAction_tmul, eval_tmul, one_mul, ← Int.cast_neg,
      Int.cast_inj] using h
  refine ⟨-(ν ≫ torusCommutatorEnd i n), ?_,
    (cocharactersLandingIn i (derivedSubgroup G)).neg_mem
      (cocharacter_torusCommutatorEnd_mem i (derivedSubgroup_containsCommutators G) n ν)⟩
  rw [map_neg, torusCommutatorEnd, Preadditive.comp_sub, Category.comp_id, map_sub, hpair, hν]
  omega

/-- A chosen positive cocharacter with full image in the actual derived subgroup. -/
def positiveDerivedCocharacter (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (a : relativeRoots i) : cocharacterLattice T :=
  (exists_positive_derived_cocharacter i A Z hA hT a).choose

theorem positiveDerivedCocharacter_pos (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (a : relativeRoots i) :
    0 < latticePairing T a.val (positiveDerivedCocharacter i A Z hA hT a) :=
  (exists_positive_derived_cocharacter i A Z hA hT a).choose_spec.1

theorem positiveDerivedCocharacter_mem (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (a : relativeRoots i) :
    positiveDerivedCocharacter i A Z hA hT a ∈
      cocharactersLandingIn i (derivedSubgroup G) :=
  (exists_positive_derived_cocharacter i A Z hA hT a).choose_spec.2

variable {D : GroupScheme (Spec (CommRingCat.of k))} {d : D ⟶ G}

/-- Factor the positive cocharacter through the supplied actual derived subgroup. -/
def derivedContractingCocharacter (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (hd : IsDerivedSubgroup d) (a : relativeRoots i) :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ D :=
  hd.isRepresentedBy.factorHom
    (CommGroupScheme.groupHom (positiveDerivedCocharacter i A Z hA hT a) ≫ i) (by
      rintro U x ⟨z, rfl⟩
      exact positiveDerivedCocharacter_mem i A Z hA hT a U z)

theorem derivedContractingCocharacter_comp (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (hd : IsDerivedSubgroup d) (a : relativeRoots i) :
    derivedContractingCocharacter i A Z hA hT hd a ≫ d =
      CommGroupScheme.groupHom (positiveDerivedCocharacter i A Z hA hT a) ≫ i :=
  hd.isRepresentedBy.factorHom_comp _ _

variable {C : GroupScheme (Spec (CommRingCat.of k))} {π : C ⟶ D}

/-- Every actual root-group rational point lifts through the supplied derived cover. -/
theorem exists_rootPoint_cover_lift (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (hcover : IsSimplyConnectedDerivedCover d π)
    (a : relativeRoots i) (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a.val) :
    ∃ c : rationalPoints C, c ≫ (π ≫ d).hom.hom = g := by
  let hd := hcover.isDerivedSubgroup
  let χ := derivedContractingCocharacter i A Z hA hT hd a
  have hgder : g ∈ (derivedSubgroup G).carrier (Over.mk (𝟙 _)) :=
    RelativeRoot.subgroup_le_derivedSubgroup i hT a.property.1 _ hg
  let gD : rationalPoints D :=
    (hd.isRepresentedBy.pointsEquiv _).symm ⟨g, hgder⟩
  have hgD : gD ≫ d.hom.hom = g :=
    hd.isRepresentedBy.pointsEquiv_symm_comp _
  have hgcontract :
      gD ∈ (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup χ d hd.1]
    change gD ≫ d.hom.hom ∈ (Dynamic.unipotent (χ ≫ d)).carrier _
    rw [hgD, derivedContractingCocharacter_comp]
    exact RelativeRoot.subgroup_le_dynamicUnipotent i
      (positiveDerivedCocharacter i A Z hA hT a)
      (positiveDerivedCocharacter_pos i A Z hA hT a) _ hg
  let : IsAffineHom C.X.hom :=
    hcover.isSimplyConnectedCover.isSimplyConnected.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine C.X.left := isAffine_of_isAffineHom C.X.hom
  let : IsAffineHom D.X.hom :=
    hcover.isSimplyConnectedCover.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine D.X.left := isAffine_of_isAffineHom D.X.hom
  refine ⟨Dynamic.centralIsogenyLift π hcover.isSimplyConnectedCover.isCentralIsogeny
    χ gD hgcontract, ?_⟩
  rw [Grp.comp_hom_hom, ← Category.assoc, Dynamic.centralIsogenyLift_comp, hgD]

/-- A chosen actual cover point above an actual root-group rational point. -/
def rootPointCoverLift (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (hcover : IsSimplyConnectedDerivedCover d π)
    (a : relativeRoots i) (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a.val) :
    rationalPoints C :=
  (exists_rootPoint_cover_lift i A Z hA hT hcover a g hg).choose

theorem rootPointCoverLift_comp (hA : A.SatisfiesApartmentAxioms Z)
    (hT : IsSplitTorus T.toGrp) (hcover : IsSimplyConnectedDerivedCover d π)
    (a : relativeRoots i) (g : rationalPoints G) (hg : g ∈ rootGroupPoints i a.val) :
    rootPointCoverLift i A Z hA hT hcover a g hg ≫ (π ≫ d).hom.hom = g :=
  (exists_rootPoint_cover_lift i A Z hA hT hcover a g hg).choose_spec

end KPApartmentData

namespace ParahoricBuildingData

variable (P : ParahoricBuildingData G)

/-- The actual root groups lie in the actual simply connected image under apartment axioms. -/
theorem rootGroup_le_simplyConnectedImage
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer) :
    P.zeroDatum.RootGroupLeSimplyConnectedImageStatement := by
  intro a ha g hg
  exact KPApartmentData.exists_rootPoint_cover_lift P.i P.apartment P.centralizer hA
    P.zeroDatum.isMaximalSplitTorus.1.1 P.zeroDatum.isSimplyConnectedDerivedCover ⟨a, ha⟩ g hg

/-- The actual sharp fixer of every subset lies in the simply connected image. -/
theorem sharpFixer_le_simplyConnectedImage
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer) (Ω : Set P.Apartment) :
    P.sharpFixer Ω ≤ P.simplyConnectedImage :=
  P.sharpFixer_le_simplyConnectedImage_of_rootGroups
    (P.rootGroup_le_simplyConnectedImage hA) Ω

/-- The unchanged full generated parahoric lies in the actual zero subgroup. -/
theorem parahoric_le_zeroSubgroup
    (hA : P.apartment.SatisfiesApartmentAxioms P.centralizer) (Ω : Set P.Apartment) :
    P.parahoric Ω ≤ P.zeroSubgroup :=
  P.parahoric_le_zeroSubgroup_of_rootGroups (P.rootGroup_le_simplyConnectedImage hA) Ω

end ParahoricBuildingData

end Langlands.Geometry.Building
