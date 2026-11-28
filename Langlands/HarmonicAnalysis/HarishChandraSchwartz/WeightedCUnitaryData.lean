import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCTranslatedLevi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionDensityNonzero

/-! # Nonvanishing of the ambient density package scalar -/

noncomputable section

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
  RationalPointFamily ActualCommonLeviV3 DynamicCommonLeviPresentations
  ActualCommonLeviTensor

universe u uV

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] translatedLeviAmbientAffine translatedLeviLeviAffineHom
  translatedLeviLeviAffine translatedLeviLeviFiniteType translatedLeviPointTopology

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  ActualCommonLeviV3.leviLocallyCompact ActualCommonLeviV3.leviMeasurable ActualCommonLeviV3.leviBorel

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)

local notation "M" => RationalPointFamily.levi i ν I
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)
local notation "χG" => CommGroupScheme.groupHom ζ ≫ i
local notation "eG" => standardLeviDynamicHomeomorph hG hi hν I hζ
local notation "fG" => standardLeviParameterIso hG hi hν I hζ

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ M₀) (hs : IsSplitComponent sc)

local notation "CM" => rationalLeviSplitCenter I sc
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

/-- The split central subgroup in the coordinates of the dynamic Levi used
by the ambient density package. -/
def standardLeviDensityCenter : Subgroup (levi χG) :=
  (CM).map (eG).symm.toMonoidHom

local notation "CG" => standardLeviDensityCenter hG hi hν I hζ sc

variable [(CM).Normal] [MeasurableSpace (M ⧸ CM)] [BorelSpace (M ⧸ CM)]
  (mu : Measure (M ⧸ CM)) [mu.IsHaarMeasure]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})

local notation "A₀" => SmoothRep.pullback eG π.obj

variable (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG A₀)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [(CM).Normal] [MeasurableSpace (M ⧸ CM)] [BorelSpace (M ⧸ CM)] in
private theorem standardLeviDensity_center_eq_range :
    CG = (rationalPoints.map (sc ≫ (fG).inv)).range.map
      (parameterHomeomorph χG).toMonoidHom := by
  rw [standardLeviDensityCenter, rationalLeviSplitCenter, Subgroup.map_map,
    MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  apply MonoidHom.ext
  intro x
  apply (eG).injective
  change (eG) ((eG).symm (leviRationalPointHomeomorph i ν I (rationalPoints.map sc x))) =
    (eG) (parameterHomeomorph χG (rationalPoints.map (sc ≫ (fG).inv) x))
  rw [ContinuousMulEquiv.apply_symm_apply, ← leviRationalPointHomeomorph_map_standardLeviParameterIso]
  congr 1
  rw [← rationalPoints_map_comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

include hs in
/-- The ambient density package has nonzero canonical scalar for the original
square-integrable representation on the standard Levi quotient. -/
theorem standardLeviDensityCanonicalScalarNonzero
    (hsq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mu) :
    PG.canonicalScalar ≠ 0 := by
  let C : Subgroup (levi χG) := CG
  let : C.Normal := Subgroup.Normal.map inferInstance (eG).symm.toMonoidHom (eG).symm.surjective
  let : MeasurableSpace (levi χG ⧸ C) := borel _
  let : BorelSpace (levi χG ⧸ C) := ⟨rfl⟩
  have hC : C ≤ Subgroup.center (levi χG) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (centerHomOfEquiv (eG).symm ⟨x, hCM hx⟩).property
  have hmap : C.map (eG).toMonoidHom = CM := by
    change ((CM).map (eG).symm.toMonoidHom).map (eG).toMonoidHom = CM
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id CM]
    congr 1
  let q := quotientContinuousMulEquiv (eG) CM C hmap
  let mq : Measure (levi χG ⧸ C) := mu.map q.symm
  let : mq.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _
  have hμ : mq.map q = mu := by
    rw [Measure.map_map (map_continuous q).measurable (map_continuous q.symm).measurable]
    convert Measure.map_id
    ext x
    exact q.apply_symm_apply x
  have hsq' := (isSquareIntegrableModCentralSubgroup_comp_iff (eG) CM hCM C hC hmap mu mq hμ
    π.obj.representation).mpr hsq
  have hIr : (A₀).representation.IsIrreducible :=
    (isIrreducible_comp_continuousMulEquiv_iff π.obj.representation (eG)).mpr π.property.1
  have hCs : IsActualSplitCenter χG C :=
    ⟨Tc, sc ≫ (fG).inv, hs.comp_iso (fG).symm, standardLeviDensity_center_eq_range hG hi hν I hζ sc⟩
  exact PG.canonicalScalar_ne_zero_of_squareIntegrable C hC mq hsq' hIr hCs

end Langlands.HarishChandraSchwartz.WeakExpansion
