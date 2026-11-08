import Langlands.Representation.Plancherel.ParabolicGenericIrreducibilityStatement
import Langlands.Representation.Exponents.SplitUnitaryWeightRestriction
import Langlands.Representation.Exponents.ArbitraryParabolicJacquetAdmissibilityReduction

/-! # Unitary weight restriction on the literal parabolic Jacquet model -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel

universe u uV uW

open Aubert.General

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  {G M P U : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine M.X.left]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} {n : U ⟶ P}
  (pres : ParabolicRootPresentation p l a)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance parabolicJacquetUnitaryRestrictionTopologicalSpace : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
local instance parabolicJacquetUnitaryRestrictionTopologicalSpace2 : TopologicalSpace (rationalPoints M) := rationalPointTopology F M.X
local instance : T2Space F := BruhatTits.localField_t2Space F

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (hn : LeviSubgroup.IsGeometricUnipotentRadical n)
  (h : IsSemidirectDecomposition
    ((SubgroupFunctor.range p).carrier (Over.mk (𝟙 _)))
    (parabolicLeviPointSubgroup p l)
    ((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))))
  (hU : IsClosed (((SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _))) :
    Set (rationalPoints G)))

include pres hn

omit [IsAffine M.X.left] in
/-- A compatible root presentation supplies the actual contraction basis,
so this literal normalized Jacquet functor preserves admissibility. -/
theorem parabolicJacquet_obj_isAdmissible
    (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hπ : π.IsAdmissible) :
    ((jacquetFunctor h hU).obj π).IsAdmissible := by
  have := hG.smooth
  let χ := CommGroupScheme.groupHom pres.splitComponentCocharacter ≫ a ≫ l ≫ p
  have hN : (SubgroupFunctor.range (n ≫ p)).carrier (Over.mk (𝟙 _)) =
      (Dynamic.unipotent χ).carrier (Over.mk (𝟙 _)) := by
    rw [pres.range_comp_radical_eq hn]
  have hL : parabolicLeviPointSubgroup p l =
      (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    change (SubgroupFunctor.range (l ≫ p)).carrier _ = _
    rw [pres.levi_eq_splitComponentCocharacter]
  obtain ⟨g, hBasis⟩ := RationalPointFamily.dynamic_hasOppositeIwahoriContractionBasis G hG χ
  have hBasis' := hBasis.hasIwahoriContractionBasis
  rw [← hN, ← hL] at hBasis'
  exact isAdmissible_jacquetFunctor_obj_of_iwahoriContraction h hU
    ((Dynamic.unipotent (Dynamic.inverseCocharacter χ)).carrier (Over.mk (𝟙 _)))
    hBasis' π hπ

omit hn in
/-- The existing unitary selected-weight restriction on the actual normalized
Jacquet action of the literal Levi subgroup. -/
def parabolicJacquetUnitaryRestriction
    (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G))
    (σ : SmoothRep.{0, u, uW} ℂ (parabolicLeviPointSubgroup p l)) :=
  splitUnitaryWeightRestriction pres.isCompatible.splitComponent.isCentralSplitTorus.1.1
    ((jacquetFunctor h hU).obj π).representation σ.representation
    (parabolicSplitComponentPointHom pres)
    (fun t => parabolicSplitComponentPointHom_range_le_center pres ⟨t, rfl⟩)

/-- For an admissible ambient source and a Levi target with unitary central
scalar action, the literal unitary-weight restriction is injective. -/
theorem parabolicJacquetUnitaryRestriction_injective
    (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hπ : π.IsAdmissible)
    (σ : SmoothRep.{0, u, uW} ℂ (parabolicLeviPointSubgroup p l))
    (c : UnitaryCentralCharacter σ.representation) :
    Function.Injective (parabolicJacquetUnitaryRestriction pres h hU π σ) := by
  let := (isClosed_parabolicLeviPointSubgroup pres).locallyCompactSpace
  exact splitUnitaryWeightRestriction_injective _ _ _ _ _
    (parabolicJacquet_obj_isAdmissible pres hn h hU hG π hπ) c

/-- The target's exact split-center square-integrability predicate gives the
whole-Jacquet rank bound by the actual selected unitary split-weight Hom space. -/
theorem parabolicJacquetHom_rank_le_unitaryWeights
    (hG : IsConnectedReductive G)
    (π : SmoothRep.{0, u, uV} ℂ (rationalPoints G)) (hπ : π.IsAdmissible)
    (σ : SmoothRep.{0, u, uW} ℂ (parabolicLeviPointSubgroup p l)) :
    let C := (parabolicSplitComponentPointHom pres).range
    let hC := parabolicSplitComponentPointHom_range_le_center pres
    letI : C.Normal := C.normal_of_le_center hC
    ∀ [MeasurableSpace (parabolicLeviPointSubgroup p l ⧸ C)]
      (qMeasure : Measure (parabolicLeviPointSubgroup p l ⧸ C)) [IsHaarMeasure qMeasure],
      IsSquareIntegrableModCentralSubgroup C hC σ.representation qMeasure →
      Module.rank ℂ
        (((jacquetFunctor h hU).obj π).representation.IntertwiningMap σ.representation) ≤
        Module.rank ℂ ((selectedWeightPart ((jacquetFunctor h hU).obj π).representation
          (parabolicSplitComponentPointHom pres)
          (fun t => hC ⟨t, rfl⟩)
          (fun χ => SplitTorus.normalizedRealPart
            pres.isCompatible.splitComponent.isCentralSplitTorus.1.1 χ = 0)).toRepresentation.IntertwiningMap
              σ.representation) := by
  dsimp only
  intro _ qMeasure _ hσ
  let := Subgroup.normal_of_le_center (parabolicSplitComponentPointHom_range_le_center pres)
  let := (isClosed_parabolicLeviPointSubgroup pres).locallyCompactSpace
  exact hom_rank_le_splitUnitaryWeights_of_squareIntegrable _ _ _ _ _ _ _ qMeasure
    (parabolicJacquet_obj_isAdmissible pres hn h hU hG π hπ) hσ

end Langlands.Plancherel
