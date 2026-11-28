import Langlands.Global.AdelicCharacteristicShellUnfolding
import Langlands.Global.AdelicRelativeParabolicQuotientMeasure
import Langlands.Global.AdelicConstantTermTransitivity
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # Relative split measure of an actual characteristic shell -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus
  AdelicSiegelFactors ArthurTruncation AdelicGroupPoints.ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p fam.bot) K)
  (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
    (Standard.leviScheme fam.i fam.ν ∅))

local notation "Γ" => rationalNormOneSubgroup F G
local notation "ΓJ" => parabolicRationalNormOneSubgroup (F := F) (fam.p J)
local notation "ΓS" =>
  parabolicRationalNormOneSubgroup (F := F) (Standard.parabolicHom fam.i fam.ν J.val)
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))
local notation "ΓN" =>
  AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))
local notation "M₁" => normOneSubgroup F (fam.M J)
local notation "ΓM" => rationalNormOneSubgroup F (fam.M J)
local notation "B" => relativePositiveSubgroup (fam.l J ≫ fam.p J) (fam.a J)
local notation "Δ" => simpleRelativeRoots fam.i fam.ν

/-- The actual rational parabolic subgroup lies in the ambient principal subgroup. -/
theorem parabolicRationalNormOneSubgroup_le : ΓJ ≤ Γ := by
  rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
  exact ⟨_, (mapNormOne_rationalNormOne F _ _ (fam.p J) q).symm⟩

omit [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
private theorem mem_parabolicRationalNormOneSubgroup_iff {P : GroupScheme (Spec (CommRingCat.of F))}
    (p : P ⟶ G) (x : normOneSubgroup F G) :
    x ∈ parabolicRationalNormOneSubgroup p ↔ x.val ∈ rationalImage F p := by
  constructor
  · rintro ⟨_, ⟨q, rfl⟩, rfl⟩
    exact ⟨q, rfl⟩
  · rintro ⟨q, hq⟩
    exact ⟨rationalNormOne F P q, ⟨q, rfl⟩, Subtype.ext hq⟩

private theorem eq_standardParabolicRationalNormOneSubgroup : ΓJ = ΓS := by
  have he := (fam.isCompatible J).parabolic_eq.trans
    (Standard.isRepresentedBy_parabolicHom fam.i fam.ν J.val).2.symm
  have hr : rationalImage F (fam.p J) = rationalImage F (Standard.parabolicHom fam.i fam.ν J.val) :=
    le_antisymm (rationalImage_le_of_range_le _ _ he.le) (rationalImage_le_of_range_le _ _ he.ge)
  ext x
  rw [mem_parabolicRationalNormOneSubgroup_iff, mem_parabolicRationalNormOneSubgroup_iff, hr]

/-- Representatives of the shell in the ambient norm-one adelic group. -/
def characteristicShellPoints (T₀ Tp S : V fam.T) : Set (normOneSubgroup F G) :=
  Subtype.val ⁻¹' characteristicHeightProduct fam.maximalSplit (fam.isIwasawaCompact_standardBot hK)
    fam.bijective_restrictToTorus_bot C
    (characteristicShell fam.connectedReductive fam.maximalSplit fam.coroots J T₀ Tp S)

/-- The actual characteristic shell in the rational quotient of the presented parabolic. -/
def presentedCharacteristicShellLift (T₀ Tp S : V fam.T) : Set (LeftCosetSpace ΓJ) :=
  LeftCosetSpace.mk ΓJ '' fam.characteristicShellPoints J hK C T₀ Tp S

private theorem measurableSet_presentedCharacteristicShellLift (T₀ Tp S : V fam.T) :
    MeasurableSet (fam.presentedCharacteristicShellLift J hK C T₀ Tp S) := by
  change MeasurableSet (LeftCosetSpace.mk ΓJ '' fam.characteristicShellPoints J hK C T₀ Tp S)
  rw [fam.eq_standardParabolicRationalNormOneSubgroup J]
  exact measurableSet_characteristicShellLift fam.connectedReductive fam.maximalSplit fam.coroots
    (fam.isIwasawaCompact_standardBot hK) fam.bijective_restrictToTorus_bot C J T₀ Tp S

local instance : IsClosedImmersion (fam.p J).hom.hom.left := fam.isClosedImmersion_p J
local instance : IsAffineHom (fam.M J).X.hom :=
  (fam.isCompatible J).levi.isConnectedReductive.isAffineHom
local instance : IsIso (subgroupMultiplication (fam.l J) (fam.iU J)) :=
  Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication
    (⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ :
      ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J)) fam.connectedReductive
    (fam.isUnipotentRadical J)

/-- The relative split Iwasawa coordinates of the parabolic determined by the family. -/
def characteristicShellCoordinates : (N × (B × M₁)) × K → LeftCosetSpace ΓJ :=
  normOneRelativeParabolicQuotientCoordinates (fam.p J) (fam.iU J) (fam.l J)
    (fam.isUnipotentRadical J) (fam.a J) (fam.isCompatible J).levi.isConnectedReductive
    (fam.isCompatible J).splitComponent hK.isCompact

/-- The relative split coordinate measure before restricting to the pullback of the shell. -/
def characteristicShellCoordinateMeasure (dn : Measure N) (da : Measure B) :
    Measure ((N × (B × M₁)) × K) :=
  (((dn.restrict (LeftCosetSpace.fundamentalDomain ΓN
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (fam.iU J ≫ fam.p J))))).prod
      ((da.withDensity (relativePositiveDensity (fam.p J) (fam.l J) (fam.a J))).prod
        ((Measure.haar : Measure M₁).restrict
          (LeftCosetSpace.fundamentalDomain ΓM (isDiscrete_rationalNormOneSubgroup F (fam.M J)))))).prod
    (compactHaarProbability F G K hK.isCompact))

/-- For sufficiently regular `T`, the weighted coordinate measure restricted to the
pullback of the characteristic shell maps to its actual ambient quotient measure. -/
def CharacteristicShellCoordinateMeasureStatement (dn : Measure N) (T₀ : V fam.T) : Prop :=
  ∃ R > 0, ∃ da : Measure B, da.IsHaarMeasure ∧ SigmaFinite da ∧
    ∀ Tp S : V fam.T, (∀ α ∈ Δ, R ≤ eval fam.T α Tp) →
      let f := fam.characteristicShellCoordinates J hK
      let g := LeftCosetSpace.projectionOfLE (fam.parabolicRationalNormOneSubgroup_le J)
      MeasurePreserving (g ∘ f)
        ((fam.characteristicShellCoordinateMeasure J hK dn da).restrict
          (f ⁻¹' fam.presentedCharacteristicShellLift J hK C T₀ Tp S))
        ((normOneRationalQuotientHaarMeasure F G).restrict
          (characteristicShellRegion fam.connectedReductive fam.maximalSplit fam.coroots
            (fam.isIwasawaCompact_standardBot hK) fam.bijective_restrictToTorus_bot C J T₀ Tp S))

set_option maxHeartbeats 1400000 in
/-- Apply the relative split Iwasawa formula to the presented parabolic, restrict to the
shell pullback, and use injective unfolding to its ambient quotient image. -/
theorem characteristicShellCoordinateMeasure_preserving (dn : Measure N) [dn.IsHaarMeasure]
    (hC : C.compactSubgroup = K) (hcov : IsRationalCovering C) (T₀ : V fam.T) :
    CharacteristicShellCoordinateMeasureStatement fam J hK C dn T₀ := by
  obtain ⟨R, hR, hproj⟩ := characteristicShellUnfolding fam.connectedReductive fam.maximalSplit
    fam.generic fam.coroots (fam.isIwasawaCompact_standardBot hK) fam.bijective_restrictToTorus_bot
    C (Measure.haar : Measure (normOneSubgroup F G)) hC hcov T₀
  obtain ⟨⟨ζ, hζ⟩, hcompare⟩ := standardCocharacter F G fam.connectedReductive fam.T fam.i
    fam.maximalSplit fam.ν fam.generic J.val J.property
  let χ := CommGroupScheme.groupHom ζ ≫ fam.i
  have hP : (Dynamic.parabolic χ).IsRepresentedBy (fam.p J) := by
    rw [← (hcompare ζ hζ).1, ← (fam.isCompatible J).parabolic_eq]
    exact (fam.isCompatible J).parabolic.isClosedSubgroup.isRepresentedBy_range
  have hU : (Dynamic.unipotent χ).IsRepresentedBy (fam.iU J ≫ fam.p J) := by
    rw [← (hcompare ζ hζ).2.2, ← fam.range_radical_eq_standardUnipotent J]
    exact (IsClosedSubgroup.isRepresentedBy_range (fam.closedU J))
  obtain ⟨da, hda, hsf, hmap⟩ := relativeParabolicQuotientMeasure (fam.p J) (fam.iU J) (fam.l J)
    (fam.isUnipotentRadical J) (fam.a J) (fam.isCompatible J).levi.isConnectedReductive
    (fam.isCompatible J).splitComponent fam.connectedReductive hP hU (fam.isIwasawaCompact_index hK J) dn
  refine ⟨R, hR, da, hda, hsf, fun Tp S hTp => ?_⟩
  let f := fam.characteristicShellCoordinates J hK
  let g := LeftCosetSpace.projectionOfLE (fam.parabolicRationalNormOneSubgroup_le J)
  let D := fam.presentedCharacteristicShellLift J hK C T₀ Tp S
  have hD : MeasurableSet D := fam.measurableSet_presentedCharacteristicShellLift J hK C T₀ Tp S
  let df := fam.characteristicShellCoordinateMeasure J hK dn da
  let dg := LeftCosetSpace.haarQuotientMeasure ΓJ (isDiscrete_parabolicRationalNormOneSubgroup (fam.p J))
  have hf : MeasurePreserving f df dg := ⟨
    measurable_normOneRelativeParabolicQuotientCoordinates (fam.p J) (fam.iU J) (fam.l J)
      (fam.isUnipotentRadical J) (fam.a J) (fam.isCompatible J).levi.isConnectedReductive
        (fam.isCompatible J).splitComponent hK.isCompact, hmap.symm⟩
  let Dest := characteristicShellRegion fam.connectedReductive fam.maximalSplit fam.coroots
    (fam.isIwasawaCompact_standardBot hK) fam.bijective_restrictToTorus_bot C J T₀ Tp S
  have transfer (Λ : Subgroup (normOneSubgroup F G)) (hle : Λ ≤ Γ)
      (hl : IsDiscrete (Λ : Set (normOneSubgroup F G))) (he : Λ = ΓS) :
      MeasurePreserving (LeftCosetSpace.projectionOfLE hle)
        ((LeftCosetSpace.haarQuotientMeasure Λ hl).restrict
          (LeftCosetSpace.mk Λ '' fam.characteristicShellPoints J hK C T₀ Tp S))
        ((normOneRationalQuotientHaarMeasure F G).restrict Dest) := by
    subst Λ
    exact hproj Tp S hTp J
  have hg : MeasurePreserving g (dg.restrict D)
      ((normOneRationalQuotientHaarMeasure F G).restrict Dest) :=
    transfer ΓJ (fam.parabolicRationalNormOneSubgroup_le J)
      (isDiscrete_parabolicRationalNormOneSubgroup (fam.p J))
      (fam.eq_standardParabolicRationalNormOneSubgroup J)
  exact hg.comp (hf.restrict_preimage hD)

end Langlands.Global.StandardParabolicFamily
