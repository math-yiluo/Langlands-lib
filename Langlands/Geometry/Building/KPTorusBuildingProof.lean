import Langlands.Geometry.Building.KPTorusRegressionStatement
import Langlands.Geometry.Building.TorusFiveAxiomConstruction
import Langlands.Geometry.Building.RootFreeBuildingGeometry
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.Derived.CommutativeTriviality
import Langlands.GroupScheme.Torus.RelativeCommutativity
import Langlands.GroupScheme.Torus.SplitPartCharacters
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.RelativeRankAssembly
import Langlands.Geometry.Building.FiniteRealTorusSpace
import Langlands.BruhatTits.Cartan.CentralizerRealComparison

/-!
# Tori: proof of `KPTorusBuildingStatement`

For a torus `T` over a nonarchimedean local field `F` and supplied KP building data of `T`,
the reduced building is one point, there is one facet, every stabilizer is computed, the
parahoric of the facet is `T(F)^0`, and the central factor of the enlarged building has
dimension the split rank of `T`. The final theorem `kpTorusBuilding` proves
`KPTorusBuildingStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Plancherel

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : GroupScheme (Spec (CommRingCat.of F))}

namespace ValuationBuildingData

variable [IsAffineHom T.X.hom] (B : ValuationBuildingData T)

/-- The reduced building of supplied data for a torus has at most one point. -/
theorem subsingleton_reducedBuilding_of_isTorus (hT : IsTorus T) :
    Subsingleton B.ReducedBuilding := by
  let U := hT.isRelativeTorus.commGroupScheme
  have : IsAffineHom U.toGrp.X.hom := ‹IsAffineHom T.X.hom›
  exact subsingleton_reducedBuilding_of_commutative (T := U) B

/-- A torus has no relative roots for the maximal split torus of supplied data. -/
theorem relativeRoots_eq_empty_of_isTorus (hT : IsTorus T) : relativeRoots B.i = ∅ := by
  let U := hT.isRelativeTorus.commGroupScheme
  have : IsAffineHom U.toGrp.X.hom := ‹IsAffineHom T.X.hom›
  have : Smooth U.toGrp.X.hom := B.isConnectedReductive.smooth
  exact relativeRoots_eq_empty_of_commutative (T := U) B.i B.isMaximalSplitTorus.1

/-- The reduced building of supplied data for a torus has exactly one point. -/
theorem nonempty_unique_reducedBuilding_of_isTorus (hT : IsTorus T) :
    Nonempty (Unique B.ReducedBuilding) := by
  have := B.subsingleton_reducedBuilding_of_isTorus hT
  obtain ⟨x⟩ := (inferInstance : Nonempty B.Apartment)
  exact ⟨uniqueOfSubsingleton (B.apartmentMap x)⟩

/-- Every point of the reduced building of a torus is fixed by all of `T(F)`. -/
theorem fixer_eq_top_of_isTorus (hT : IsTorus T) (y : B.ReducedBuilding) : B.fixer y = ⊤ := by
  have := B.subsingleton_reducedBuilding_of_isTorus hT
  exact top_unique fun g _ => B.mem_fixer.2 (Subsingleton.elim _ _)

/-- For a torus, `G(F)^1_y = T(F)^1` at every point `y` of the reduced building. -/
theorem compactStabilizer_eq_of_isTorus (hT : IsTorus T) (y : B.ReducedBuilding) :
    B.compactStabilizer y = rationalCommonNormKernel T := by
  have := B.subsingleton_reducedBuilding_of_isTorus hT
  ext g
  rw [B.mem_compactStabilizer]
  exact and_iff_left (Subsingleton.elim _ _)

/-- For a torus, every point of the enlarged building has stabilizer `T(F)^1`. -/
theorem enlargedStabilizer_eq_of_isTorus (hT : IsTorus T) (z : B.EnlargedBuilding) :
    B.enlargedStabilizer z = rationalCommonNormKernel T := by
  rw [B.enlargedStabilizer_eq_compactStabilizer, B.compactStabilizer_eq_of_isTorus hT]

/-- For a torus, the pointwise fixer of every subset of the reduced building is `T(F)`. -/
theorem pointwiseFixer_eq_top_of_isTorus (hT : IsTorus T) (Y : Set B.ReducedBuilding) :
    B.apartment.pointwiseFixer Y = ⊤ := by
  have := B.subsingleton_reducedBuilding_of_isTorus hT
  exact top_unique fun g _ => B.apartment.mem_pointwiseFixer.2 fun _ _ => Subsingleton.elim _ _

/-- The reduced building of a torus has exactly one facet. -/
theorem nonempty_unique_buildingFacet_of_isTorus (hT : IsTorus T) :
    Nonempty (Unique (BruhatTits.IntegralModels.BuildingFacet B)) := by
  have := B.subsingleton_reducedBuilding_of_isTorus hT
  obtain ⟨⟨y⟩⟩ := B.nonempty_unique_reducedBuilding_of_isTorus hT
  have hΦ := B.relativeRoots_eq_empty_of_isTorus hT
  have hY : B.IsFacet {y.default} :=
    (B.isFacet_iff_exists_singleton_of_relativeRoots_eq_empty hΦ _).2 ⟨_, rfl⟩
  refine ⟨{ default := ⟨{y.default}, hY⟩, uniq := fun Z => ?_ }⟩
  obtain ⟨z, hz⟩ := (B.isFacet_iff_exists_singleton_of_relativeRoots_eq_empty hΦ Z.val).1
    Z.property
  apply Subtype.ext
  change Z.val = {y.default}
  rw [hz, Subsingleton.elim z y.default]

end ValuationBuildingData

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- In a separated commutative group scheme, the image of `C(F) → G(F)` for a simply connected
cover `π : C → D` of the derived subgroup `d : D → G` is trivial. -/
theorem simplyConnectedImage_eq_bot_of_isCommMonObj
    {D C G : GroupScheme (Spec (CommRingCat.of F))}
    [IsCommMonObj G.X] [IsSeparated G.X.hom] {d : D ⟶ G} {π : C ⟶ D}
    (h : IsSimplyConnectedDerivedCover d π) : simplyConnectedImage d π = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨c, rfl⟩
  have hmem := h.range_comp_le_derivedSubgroup (Over.mk (𝟙 _)) ⟨c, rfl⟩
  rw [derivedSubgroup_eq_bot_of_isCommMonObj G] at hmem
  exact hmem

namespace ParahoricBuildingData

variable [IsAffineHom T.X.hom] (P : ParahoricBuildingData T)

/-- For a torus, `G(F)^0 = G(F)^♮ ⊔ Z(F)^0` is the image of `Z(F)^0`: the image of the simply
connected cover of the derived subgroup is trivial. -/
theorem zeroSubgroup_eq_of_isTorus (hT : IsTorus T) :
    P.zeroSubgroup = P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  have := hT.isCommMonObj
  change P.zeroDatum.simplyConnectedImage ⊔ _ = _
  rw [ZeroSubgroupDatum.simplyConnectedImage,
    simplyConnectedImage_eq_bot_of_isCommMonObj P.zeroDatum.isSimplyConnectedDerivedCover,
    bot_sup_eq]

end ParahoricBuildingData

namespace KPBuildingDatum

variable [IsAffineHom T.X.hom] (D : KPBuildingDatum T)

/-- For a torus and data satisfying the one-group axioms, the parahoric of every facet is the
image of `Z(F)^0` in `T(F)`. -/
theorem parahoric_eq_of_isTorus (hT : IsTorus T) (hD : D.SatisfiesGroupAxioms)
    (x : BruhatTits.IntegralModels.BuildingFacet D.base.toValuationBuildingData) :
    D.parahoric x = D.base.centralizerZero.map (rationalPoints.map D.base.centralizer.j) := by
  have h := hD.bruhatTitsGroupSchemes.neutral_points
    (BruhatTits.IntegralModels.BuildingModelIndex.ofFacet x)
  change (D.models.model _).neutral.integralPoints = _
  rw [h, BruhatTits.IntegralModels.BuildingModelFamily.zeroFixer,
    D.base.toValuationBuildingData.pointwiseFixer_eq_top_of_isTorus hT, top_inf_eq,
    D.base.zeroSubgroup_eq_of_isTorus hT]

end KPBuildingDatum

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The central factor of the enlarged building of a torus is finite-dimensional, of dimension
the split rank. -/
theorem centralFactor_finiteDimensional_finrank (hT : IsTorus T) :
    FiniteDimensional ℝ (CentralFactor T) ∧
      (Module.finrank ℝ (CentralFactor T) : ℕ∞) = splitRank T := by
  let U := hT.isRelativeTorus.commGroupScheme
  have hred : IsConnectedReductive T := hT.isConnectedReductive_of_fieldSplitting
  have : IsAffineHom U.toGrp.X.hom := hred.isAffineHom
  have : IsAffine U.X.left := isAffine_of_isAffineHom U.toGrp.X.hom
  have : Smooth U.toGrp.X.hom := hred.smooth
  obtain ⟨A, i, hi⟩ := exists_largestSplitSubtorus U
  have hmax : IsMaximalSplitTorus i := hi.isMaximalSplitTorus
  have hinj : Function.Injective (characterRestrict i) := hi.characterRestrict_injective hT
  have hcomponent : IsSplitComponent i :=
    ⟨⟨hmax.1, isCentral_to_commGroupScheme i⟩, fun A' a ha f hf => hmax.2 A' a ha.1 f hf⟩
  have hfi := hcomponent.finiteIndex_range_characterRestrict hred
  let e : RealTorusSpace.V A ≃ₗ[ℝ] CentralFactor T :=
    (@BruhatTits.Cartan.restrictionEvaluationEquiv F _ A U.toGrp hmax.1.1 i hinj hfi).trans
      (CentralFactor.dualEquiv T).symm
  have := hmax.1.1.finite_realCocharacterSpace
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq, hmax.1.1.finrank_realCocharacterSpace]
  exact (splitRank_eq_splitTorusRank_of_conjugacyStatement maximalSplitTorusConjugacy hred i
    hmax).symm

/-- The enlarged building of a torus has exactly one point if and only if the torus is
anisotropic. -/
theorem ValuationBuildingData.nonempty_unique_enlargedBuilding_iff_of_isTorus
    [IsAffineHom T.X.hom] (B : ValuationBuildingData T) (hT : IsTorus T) :
    Nonempty (Unique B.EnlargedBuilding) ↔ IsAnisotropic T := by
  obtain ⟨hfin, hrank⟩ := centralFactor_finiteDimensional_finrank hT
  have := B.subsingleton_reducedBuilding_of_isTorus hT
  obtain ⟨⟨y⟩⟩ := B.nonempty_unique_reducedBuilding_of_isTorus hT
  rw [IsAnisotropic, ← hrank, Nat.cast_eq_zero, Module.finrank_zero_iff]
  constructor
  · rintro ⟨u⟩
    exact ⟨fun a b =>
      congrArg Prod.snd ((u.uniq (y.default, a)).trans (u.uniq (y.default, b)).symm)⟩
  · intro h
    exact ⟨uniqueOfSubsingleton (y.default, 0)⟩

/-- Proof of `KPTorusBuildingStatement`. -/
theorem kpTorusBuilding : KPTorusBuildingStatement.{u} := by
  intro F _ _ _ _ T hT
  let : IsAffineHom T.X.hom := hT.isRelativeTorus.isAffineHom
  refine ⟨centralFactor_finiteDimensional_finrank hT, fun D hD => ?_⟩
  intro B T0
  exact ⟨B.nonempty_unique_reducedBuilding_of_isTorus hT,
    B.nonempty_unique_enlargedBuilding_iff_of_isTorus hT,
    B.nonempty_unique_buildingFacet_of_isTorus hT,
    D.base.zeroDatum.map_centralizerZero_le_zeroSubgroup.trans
      D.base.zeroDatum.zeroSubgroup_le_rationalCommonNormKernel,
    D.parahoric_eq_of_isTorus hT hD,
    fun y => ⟨B.compactStabilizer_eq_of_isTorus hT y, B.fixer_eq_top_of_isTorus hT y⟩,
    B.enlargedStabilizer_eq_of_isTorus hT⟩

end Langlands.Geometry.Building
