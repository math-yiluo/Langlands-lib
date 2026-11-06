import Langlands.Geometry.Building.TorusParahoricBuildingConstruction
import Langlands.Geometry.Building.AnisotropicBuildingRealization
import Langlands.Geometry.Building.FullValidity.AffineApartment
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations
import Langlands.GroupScheme.Rational.CommSplitTorusConjugacy
import Langlands.GroupScheme.Torus.HeightExistence
import Langlands.Representation.Plancherel.RationalNormKernelCentralCover
import Langlands.Representation.Plancherel.RationalNormKernelTopology

/-! # Actual torus buildings with all five metric-construction axiom families -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

private theorem commutative_innerIso_hom
    {k : Type u} [Field k] (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (g : rationalPoints T.toGrp) : (innerIso T.toGrp g).hom = 𝟙 T.toGrp := by
  refine hom_ext_points fun U x => ?_
  rw [Grp.id_hom_hom, comp_innerIso_hom, Category.comp_id,
    mul_comm (constantPoint T.toGrp g U) x, mul_inv_cancel_right]

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom T.toGrp.X.hom]
  (B : ValuationBuildingData T.toGrp)

/-- In a commutative ambient group the actual normalizer is the entire point group. -/
theorem normalizerPoints_eq_top_of_commutative : normalizerPoints B.i = ⊤ := by
  apply top_unique
  intro g _
  apply centralizerPoints_le_normalizerPoints B.i
  rw [mem_centralizerPoints, commutative_innerIso_hom, Category.comp_id]

/-- The original reduced quotient of supplied commutative data is a point. -/
theorem subsingleton_reducedBuilding_of_commutative : Subsingleton B.ReducedBuilding := by
  have : Smooth T.toGrp.X.hom := B.isConnectedReductive.smooth
  have hΦ := relativeRoots_eq_empty_of_commutative B.i B.isMaximalSplitTorus.1
  have hA := B.apartment.subsingleton_apartment_of_relativeRoots_eq_empty hΦ
  obtain ⟨x⟩ := (inferInstance : Nonempty B.Apartment)
  have hfix : B.apartment.reducedFixer (B.apartmentMap x) = ⊤ := by
    rw [B.apartment.reducedFixer_apartmentMap_of_relativeRoots_eq_empty hΦ,
      B.normalizerPoints_eq_top_of_commutative]
  have hall : ∀ y : B.ReducedBuilding, y = B.apartmentMap x := by
    intro y
    obtain ⟨g, z, rfl⟩ := B.exists_smul_apartmentMap y
    rw [hA.elim z x]
    exact B.apartment.mem_reducedFixer.1 (hfix ▸ Subgroup.mem_top g)
  exact ⟨fun y z => (hall y).trans (hall z).symm⟩

/-- Its norm-one stabilizers are the actual common rational character norm kernel. -/
theorem compactStabilizer_eq_normKernel_of_commutative (y : B.ReducedBuilding) :
    B.compactStabilizer y = rationalCommonNormKernel T.toGrp := by
  ext g
  rw [B.mem_compactStabilizer]
  exact and_iff_left (B.subsingleton_reducedBuilding_of_commutative.elim _ _)

/-- All actual torus point stabilizers are bounded and open in the canonical topology. -/
theorem hasBoundedOpenStabilizers_of_commutative : B.HasBoundedOpenStabilizers := by
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : Smooth T.toGrp.X.hom := B.isConnectedReductive.smooth
  let : TopologicalSpace (rationalPoints T.toGrp) := rationalPointTopology F T.toGrp.X
  change ∀ y : B.ReducedBuilding,
    IsOpen (B.compactStabilizer y : Set (rationalPoints T.toGrp)) ∧
      IsAlgebraicallyBounded F T.toGrp.X (B.compactStabilizer y : Set (rationalPoints T.toGrp))
  intro y
  rw [B.compactStabilizer_eq_normKernel_of_commutative y]
  refine ⟨isOpen_rationalCommonNormKernel _, isAlgebraicallyBounded_of_isCompact ?_⟩
  simpa only [CommGroup.center_eq_top, inf_top_eq] using
    isCompact_rationalCommonNormKernel_inf_center T.toGrp B.isConnectedReductive

/-- The actual maximal split tori of a commutative ambient group all give its sole apartment. -/
theorem hasTorusApartmentCorrespondence_of_commutative : B.HasTorusApartmentCorrespondence := by
  have : IsAffine T.X.left := isAffine_of_isAffineHom T.toGrp.X.hom
  have : Smooth T.toGrp.X.hom := B.isConnectedReductive.smooth
  have hA := B.apartmentImage_eq_univ_of_subsingleton B.subsingleton_reducedBuilding_of_commutative
  refine ⟨?_, ?_⟩
  · intro T₂ i₂ hi₂
    obtain ⟨g, e, he⟩ := subgroupConjugate_of_commGroup B.isMaximalSplitTorus hi₂
    let σ : B.S ≅ T₂ :=
      { hom := Additive.ofMul e.hom
        inv := Additive.ofMul e.inv
        hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
        inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
    exact ⟨g, σ, he⟩
  · intro g h
    simp only [conjTorus, commutative_innerIso_hom, Category.comp_id, hA,
      Set.smul_set_univ]

/-- The empty-factor realization of the actual reduced torus quotient. -/
def commutativeRealization : B.PolysimplicialRealization :=
  B.emptyFactorRealizationOfSubsingleton B.subsingleton_reducedBuilding_of_commutative

/-- All existing one-group KP 4.1.1 clauses hold for the actual reduced torus quotient. -/
theorem satisfiesBuildingAxiom_commutativeRealization :
    B.SatisfiesBuildingAxiom B.commutativeRealization := by
  have : Smooth T.toGrp.X.hom := B.isConnectedReductive.smooth
  exact B.satisfiesBuildingAxiom_emptyFactorRealizationOfSubsingleton _
    B.hasTorusApartmentCorrespondence_of_commutative
    (B.hasNormalizerApartmentStabilizer_of_relativeRoots_eq_empty
      (relativeRoots_eq_empty_of_commutative B.i B.isMaximalSplitTorus.1))

/-- Use the actual trivial derived subgroup and the whole maximal split torus as
central factor, keeping the original ambient group and apartment. -/
def commutativeApartmentSplitting : B.ApartmentSplitting where
  D := Grp.trivial (Over (Spec (CommRingCat.of F)))
  d := (commutativeDerivedCoverData T.toGrp B.isConnectedReductive).val
  derivedTorus := trivialCommGroupScheme _
  j := 𝟙 _
  e := 0
  centralTorus := B.S
  a := 𝟙 _

/-- The actual derived/central decomposition and every existing KP 4.1.4 field for tori. -/
theorem satisfiesAffineApartmentAxiom_commutativeApartmentSplitting :
    B.SatisfiesAffineApartmentAxiom B.commutativeApartmentSplitting := by
  have : Smooth T.toGrp.X.hom := B.isConnectedReductive.smooth
  let U := trivialCommGroupScheme (Spec (CommRingCat.of F))
  have hmax : IsMaximalSplitTorus (𝟙 U.toGrp) := by
    apply IsLargestSplitSubtorus.isMaximalSplitTorus
    refine ⟨⟨isSplitTorus_trivial _, IsClosedSubgroup.of_iso (Iso.refl _)⟩, ?_⟩
    intro A f _
    exact ⟨f, Category.comp_id _, fun g hg => by simpa only [Category.comp_id] using hg⟩
  have hclosed : IsClosedSubgroup (CommGroupScheme.groupHom (0 : U ⟶ B.S)) := by
    have : IsAffineHom B.S.toGrp.X.hom := by
      have : IsClosedImmersion B.i.hom.hom.left := B.isMaximalSplitTorus.1.2
      rw [← Over.w B.i.hom.hom]
      infer_instance
    have : IsSeparated B.S.toGrp.X.hom := inferInstance
    have he : CommGroupScheme.groupHom (0 : U ⟶ B.S) = kernelUnit B.S.toGrp :=
      Subsingleton.elim _ _
    rw [he]
    exact kernelUnit_isClosedSubgroup _
  have he0 : cocharacterMapReal (0 : U ⟶ B.S) = 0 := by
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul r ν => simp
    | add x y hx hy => simp [map_add, hx, hy]
  have ha1 : cocharacterMapReal (𝟙 B.S) = LinearMap.id := by
    apply LinearMap.ext
    intro v
    induction v using TensorProduct.inductionOn with
    | tmul r ν => simp
    | add x y hx hy => simp [map_add, hx, hy]
  have hA := B.apartment.subsingleton_apartment_of_relativeRoots_eq_empty
    (relativeRoots_eq_empty_of_commutative B.i B.isMaximalSplitTorus.1)
  refine ⟨(commutativeDerivedCoverData T.toGrp B.isConnectedReductive).property.isDerivedSubgroup,
    hmax, hclosed, ?_, ?_, ?_, ?_, ?_, B.hasAffineConjugations⟩
  · exact (inferInstance : Subsingleton
      (Grp.trivial (Over (Spec (CommRingCat.of F))) ⟶ T.toGrp)).elim _ _
  · change IsSplitComponent (CommGroupScheme.groupHom (𝟙 B.S) ≫ B.i)
    change IsSplitComponent (𝟙 B.S.toGrp ≫ B.i)
    rw [Category.id_comp]
    exact ⟨⟨B.isMaximalSplitTorus.1, isCentral_to_commGroupScheme B.i⟩,
      fun A a ha f hf => B.isMaximalSplitTorus.2 A a ha.1 f hf⟩
  · change IsCompl (LinearMap.range (cocharacterMapReal (0 : U ⟶ B.S)))
      (LinearMap.range (cocharacterMapReal (𝟙 B.S)))
    rw [he0, ha1, LinearMap.range_zero, LinearMap.range_id]
    exact isCompl_bot_top
  · intro n
    exact ⟨Iso.refl U, by simp [commutativeApartmentSplitting]⟩
  · intro n _
    apply AffineEquiv.ext
    intro x
    exact hA.elim _ _

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffineHom T.toGrp.X.hom]
  (P : ParahoricBuildingData T.toGrp)

/-- All seven original predicates representing the five axiom families, on supplied
actual parahoric-building data of a commutative group. -/
def commutativeFiveAxiomData :
    {RT : P.toValuationBuildingData.PolysimplicialRealization ×
        P.toValuationBuildingData.ApartmentSplitting //
      P.SatisfiesBuildingAxiom RT.1 ∧
      P.HasBoundedOpenStabilizers ∧
      P.SatisfiesAffineApartmentAxiom RT.2 ∧
      P.HasRootReflections ∧
      P.SatisfiesApartmentAxioms ∧
      P.HasCompatibleApartmentFacets ∧
      P.HasTitsSystem} := by
  have : Smooth T.toGrp.X.hom := P.isConnectedReductive.smooth
  have hΦ := ValuationBuildingData.relativeRoots_eq_empty_of_commutative P.i
    P.isMaximalSplitTorus.1
  have hR : P.HasRootReflections := by
    have : IsEmpty (relativeRoots P.i) := Set.isEmpty_coe_sort.2 hΦ
    intro α
    exact isEmptyElim α
  exact ⟨⟨P.toValuationBuildingData.commutativeRealization,
      P.toValuationBuildingData.commutativeApartmentSplitting⟩,
    P.toValuationBuildingData.satisfiesBuildingAxiom_commutativeRealization,
    P.toValuationBuildingData.hasBoundedOpenStabilizers_of_commutative,
    P.toValuationBuildingData.satisfiesAffineApartmentAxiom_commutativeApartmentSplitting,
    hR,
    P.apartment.satisfiesApartmentAxioms_of_relativeRoots_eq_empty P.centralizer hΦ,
    P.toValuationBuildingData.hasCompatibleApartmentFacets_of_relativeRoots_eq_empty hΦ,
    P.hasTitsSystem_of_subsingleton_of_normalizer_eq_top
      P.toValuationBuildingData.subsingleton_reducedBuilding_of_commutative
      P.toValuationBuildingData.normalizerPoints_eq_top_of_commutative⟩

end ParahoricBuildingData

/-- Construct actual data, realization and splitting satisfying all seven unchanged
metric-construction predicates for every torus over every nonarchimedean local field. -/
def torusBuildingConstructionData
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (hT : IsTorus T.toGrp) :
    letI : IsAffineHom T.toGrp.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
    Σ P : ParahoricBuildingData T.toGrp,
      {RT : P.toValuationBuildingData.PolysimplicialRealization ×
          P.toValuationBuildingData.ApartmentSplitting //
        P.SatisfiesBuildingAxiom RT.1 ∧
        P.HasBoundedOpenStabilizers ∧
        P.SatisfiesAffineApartmentAxiom RT.2 ∧
        P.HasRootReflections ∧
        P.SatisfiesApartmentAxioms ∧
        P.HasCompatibleApartmentFacets ∧
        P.HasTitsSystem} := by
  have : IsAffineHom T.toGrp.X.hom := hT.isConnectedReductive_of_fieldSplitting.isAffineHom
  let P := ParahoricBuildingData.ofTorus T hT
  exact ⟨P, P.commutativeFiveAxiomData⟩

end Langlands.Geometry.Building
