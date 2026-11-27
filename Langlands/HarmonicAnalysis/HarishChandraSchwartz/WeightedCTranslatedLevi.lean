import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCAuxiliaryInnerScalar
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralSubgroupQuotientHaar
import Langlands.Representation.Plancherel.ActualCommonLeviV3Statement

/-! # The translated inducing representation and its actual parameter chart -/

noncomputable section

set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

open CategoryTheory AlgebraicGeometry MeasureTheory
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open UnramifiedOperatorFamily StandardIntertwining DynamicCommonLeviComposition
  DynamicCommonLeviCompact DynamicCommonLeviContinuation ActualCommonLeviTensor
  DynamicOppositeCanonicalScalar ActualCommonLeviV3

universe u uV

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance translatedLeviAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance translatedLeviLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance translatedLeviLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance translatedLeviLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

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
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

local instance translatedLeviPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

local notation "χG" => CommGroupScheme.groupHom ζ ≫ i
local notation "χ" => χG ≫ (G.innerIso (n : rationalPoints G)).hom
local notation "m" => (n : rationalPoints G)
local notation "L" => parameterScheme χ
local notation "M" => RationalPointFamily.levi i ν I
local notation "fM" => leviRationalPointHomeomorph i ν I
local notation "eG" => standardLeviDynamicHomeomorph hG hi hν I hζ
local notation "cg" => leviConjugation χG m
local notation "e₁" => standardLeviParameterIso hG hi hν I hζ
local notation "e₂" => parameterConjugationIso χG m
local notation "eL" => lowerParameterIso hG hi hν I I' hζ n hn
local notation "eI" => auxiliaryInnerParameterIso hG hi hν I I' hζ hζ' n hn
local notation "b" => lowerCocharacter i ν (rootSet i ν I') ζ n
local notation "j₀" => Standard.leviHom i ν (rootSet i ν I)
local notation "j₁" => Standard.leviHom i ν (rootSet i ν I')
local notation "e_s" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
local notation "eIpt" => auxiliaryInnerLeviEquiv hG hi hν I I' hζ hζ' n hn

/-- The translated ambient Levi is identified with the original Levi by
inverse conjugation. -/
def weightedCLeviEquiv : levi χ ≃ₜ* M := (cg).symm.trans eG

/-- The corresponding isomorphism of actual reductive parameter schemes. -/
def weightedCParameterIso : L ≅ M₀ := (e₂).symm ≪≫ e₁

local notation "e" => weightedCLeviEquiv hG hi hν I hζ n
local notation "f" => weightedCParameterIso hG hi hν I hζ n

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
/-- The composite with the standard Levi inclusion is inverse conjugation. -/
theorem weightedCParameterIso_hom_comp :
    (f).hom ≫ j₀ = Dynamic.Affine.centralizerHom χ ≫ (G.innerIso m).inv := by
  simp only [weightedCParameterIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    standardLeviParameterIso_hom_comp, parameterConjugationIso]
  exact SubgroupFunctor.IsRepresentedBy.isoOfComap_inv_comp _ _ _ _

/-- On rational points the scheme isomorphism is the literal Levi comparison. -/
theorem weightedCParameterIso_points (z : rationalPoints L) :
    (fM) (rationalPoints.map (f).hom z) = (e) (parameterHomeomorph χ z) := by
  let v := parameterHomeomorph χ z
  let a := (cg).symm v
  have hv : rationalPoints.map (Dynamic.Affine.centralizerHom χ) z = (v : rationalPoints G) :=
    (parameterHomeomorph_apply_coe χ z).symm
  have ha := leviConjugation_apply_coe χG m a
  change ((cg) ((cg).symm v) : rationalPoints G) = _ at ha
  rw [ContinuousMulEquiv.apply_symm_apply] at ha
  apply Subtype.ext
  rw [leviRationalPointHomeomorph_apply_coe, ← rationalPoints_map_comp_apply,
    weightedCParameterIso_hom_comp, rationalPoints_map_comp_apply, hv,
    rationalPoints_map_innerIso_inv]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  change m⁻¹ * (v : rationalPoints G) * m = ((eG) a : rationalPoints G)
  rw [standardLeviDynamicHomeomorph_apply_coe, ha]
  group

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The lower and translated ambient parameter charts agree over the
original Levi scheme. -/
theorem weightedCParameterIso_lower : (eI).hom ≫ (f).hom = (eL).hom := by
  have hj := Standard.isRepresentedBy_leviHom i ν (rootSet i ν I)
  apply hj.hom_ext
  rw [Category.assoc, weightedCParameterIso_hom_comp, ← Category.assoc,
    auxiliaryInnerParameterIso_hom_comp, Category.assoc]
  exact (lowerParameterIso_hom_comp hG hi hν I I' hζ n hn).symm

local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
local notation "Φ" => unramifiedCharactersHomeomorph fM ν₀
local notation "liftParam" => rationalUnramifiedCharacterRestrict (f).hom

omit [LocallyOfFiniteType G.X.hom] in
/-- The original density uses the pullback along the standard parameter map. -/
theorem weightedC_restrict_ambientDensity (z : unramifiedCharacters ν₀) :
    rationalUnramifiedCharacterRestrict (e₂).hom ((liftParam) z) =
      standardLeviUnramifiedRestrict hG hi hν I hζ ((Φ) z) := by
  unfold standardLeviUnramifiedRestrict
  rw [ContinuousMulEquiv.symm_apply_apply]
  rw [← rationalUnramifiedCharacterRestrict_comp]
  simp only [weightedCParameterIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

/-- The lower density uses the same parameter read in the lower scheme. -/
theorem weightedC_restrict_lowerDensity (z : unramifiedCharacters ν₀) :
    rationalUnramifiedCharacterRestrict (eI).hom ((liftParam) z) =
      (parameterTransport b).symm (lowerUnramifiedCharacterConjugation hG hi hν I I' hζ n hn ((Φ) z)) := by
  rw [← rationalUnramifiedCharacterRestrict_comp, weightedCParameterIso_lower]
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro v
  change z.val (rationalPoints.map (eL).hom v) =
    ((Φ) z).val ((e_s).symm (parameterHomeomorph b v))
  have ht : (fM) (rationalPoints.map (eL).hom v) = (e_s).symm (parameterHomeomorph b v) :=
    Subtype.ext (leviRationalPointHomeomorph_lowerParameterIso hG hi hν I I' hζ n hn v)
  have hk := congrArg (fun x : M => ((Φ) z).val x) ht
  change z.val ((fM).symm ((fM) (rationalPoints.map (eL).hom v))) = _ at hk
  rw [ContinuousMulEquiv.symm_apply_apply] at hk
  exact hk

private theorem weightedCLeviEquiv_lower (x : levi b) : (e) ((eIpt) x) = (e_s).symm x := by
  apply Subtype.ext
  rw [lowerLeviConjugation_symm_coe]
  let a := (cg).symm ((eIpt) x)
  have ha := leviConjugation_apply_coe χG m a
  change ((cg) ((cg).symm ((eIpt) x)) : rationalPoints G) = _ at ha
  rw [ContinuousMulEquiv.apply_symm_apply] at ha
  have hcoe := auxiliaryInnerLeviEquiv_coe hG hi hν I I' hζ hζ' n hn x
  rw [RepresentedDynamicTransport.pointEquiv_apply_coe] at hcoe
  have hp := hcoe.symm.trans ha
  change rationalPoints.map j₁ (x : rationalPoints _) = _ at hp
  change ((eG) a : rationalPoints G) = _
  rw [standardLeviDynamicHomeomorph_apply_coe, hp]
  group

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))

local notation "A" => conjugateRepresentation χG m (SmoothRep.pullback eG π.obj)
local notation "B" => (lowerRepresentation hG hi hν I I' hζ n hn π).obj

/-- The ambient translated inducing representation restricts to the exact
lower inducing representation by the identity on the original carrier. -/
def weightedCTranslatedCoefficientEquiv :
    (SmoothRep.pullback (eIpt) (A)).representation.Equiv (B).representation :=
  Representation.Equiv.mk (LinearEquiv.refl ℂ π.obj) (fun x => by
    change π.obj.representation ((e) ((eIpt) x)) = π.obj.representation ((e_s).symm x)
    exact congrArg π.obj.representation (weightedCLeviEquiv_lower hG hi hν I I' hζ hζ' n hn x))

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  (sc : Tc.toGrp ⟶ M₀) (hs : IsSplitComponent sc)

local notation "CM" => rationalLeviSplitCenter I sc
local notation "hCM" => rationalLeviSplitCenter_le_center I sc hs

/-- The transported central subgroup is defined using the original
split-component image, in the actual translated Levi. -/
def weightedCTranslatedCenter : Subgroup (levi χ) :=
  (CM).map (e).symm.toMonoidHom

local notation "C" => weightedCTranslatedCenter hG hi hν I hζ n sc

instance weightedCTranslatedCenter_normal [(CM).Normal] : (C).Normal :=
  Subgroup.Normal.map inferInstance (e).symm.toMonoidHom (e).symm.surjective

include hs in
/-- The transported subgroup is central. -/
theorem weightedCTranslatedCenter_le_center : C ≤ Subgroup.center (levi χ) := by
  rintro _ ⟨x, hx, rfl⟩
  exact (centerHomOfEquiv (e).symm ⟨x, hCM hx⟩).property

/-- The transported subgroup is the split component of the actual
translated parameter scheme. -/
theorem weightedCTranslatedCenter_eq_range :
    C = (rationalPoints.map (sc ≫ (f).inv)).range.map
      (parameterHomeomorph χ).toMonoidHom := by
  rw [weightedCTranslatedCenter, rationalLeviSplitCenter, Subgroup.map_map,
    MonoidHom.map_range, MonoidHom.map_range]
  congr 1
  apply MonoidHom.ext
  intro x
  change (e).symm ((fM) (rationalPoints.map sc x)) =
    parameterHomeomorph χ (rationalPoints.map (sc ≫ (f).inv) x)
  apply (e).injective
  rw [ContinuousMulEquiv.apply_symm_apply, ← weightedCParameterIso_points hG hi hν I hζ n]
  congr 1
  rw [← rationalPoints_map_comp_apply, Category.assoc, Iso.inv_hom_id, Category.comp_id]

include hs in
/-- The subgroup and its split component give the actual split-center data
for the common-Levi comparison. -/
theorem weightedCTranslatedCenter_isActual : IsActualSplitCenter χ C :=
  ⟨Tc, sc ≫ (f).inv, hs.comp_iso (f).symm, weightedCTranslatedCenter_eq_range hG hi hν I hζ n sc⟩

private theorem weightedCTranslatedCenter_map : (C).map (e).toMonoidHom = CM := by
  rw [weightedCTranslatedCenter, Subgroup.map_map]
  conv_rhs => rw [← Subgroup.map_id CM]
  congr 1
  exact MonoidHom.ext (e).apply_symm_apply

variable [(CM).Normal]

local notation "qE" => quotientContinuousMulEquiv (e) CM C
  (weightedCTranslatedCenter_map hG hi hν I hζ n sc)

instance weightedCTranslatedQuotient_measurable : MeasurableSpace (levi χ ⧸ C) := borel _
instance weightedCTranslatedQuotient_borel : BorelSpace (levi χ ⧸ C) := ⟨rfl⟩

variable [MeasurableSpace (M ⧸ CM)] [BorelSpace (M ⧸ CM)]
  (mq₀ : Measure (M ⧸ CM)) [mq₀.IsHaarMeasure]

/-- The actual quotient Haar measure carried from the original split
central quotient to the translated one. -/
def weightedCTranslatedMeasure : Measure (levi χ ⧸ C) := mq₀.map (qE).symm

local notation "mq" => weightedCTranslatedMeasure hG hi hν I hζ n sc mq₀

instance weightedCTranslatedMeasure_haar : (mq).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map _ _

include hs in
/-- The transported Haar measure is invariant under inversion. -/
theorem weightedCTranslatedMeasure_invInvariant : (mq).IsInvInvariant := by
  let s := sc ≫ (f).inv
  have hs' : IsSplitComponent s := hs.comp_iso (f).symm
  have hclosed : IsClosed (C : Set (levi χ)) := by
    rw [weightedCTranslatedCenter_eq_range hG hi hν I hζ n sc]
    exact (parameterHomeomorph χ).toHomeomorph.isClosedMap _ (isClosed_range_splitComponent L s hs')
  let : IsClosed (C : Set (levi χ)) := hclosed
  let : SecondCountableTopology (rationalPoints L) :=
    Langlands.AlgebraicGeometry.PointTopology.rationalPoint_secondCountableTopology F L
  let : SecondCountableTopology (levi χ) :=
    (parameterHomeomorph χ).symm.toHomeomorph.secondCountableTopology
  let : T3Space (levi χ ⧸ C) := inferInstance
  let : (mq).Regular := inferInstance
  have hmod (z : levi χ) : Measure.modularCharacter z = 1 := by
    exact DynamicOppositeHermitianAdjunctionProof.levi_modularCharacter_eq_one χ hG z
  let : (mq).IsMulRightInvariant := Haar.centralSubgroupQuotient_isMulRightInvariant C
    (weightedCTranslatedCenter_le_center hG hi hν I hζ n sc hs) hclosed hmod mq
  exact Langlands.isInvInvariant_of_isMulRightInvariant mq

include hs in
/-- Square integrability on the original quotient transports to this
conjugate representation and its displayed Haar measure. -/
theorem weightedCTranslated_isSquareIntegrable
    (hq : IsSquareIntegrableModCentralSubgroup CM hCM π.obj.representation mq₀) :
    IsSquareIntegrableModCentralSubgroup C (weightedCTranslatedCenter_le_center hG hi hν I hζ n sc hs)
      (A).representation mq := by
  have he : (mq).map (qE) = mq₀ := by
    rw [weightedCTranslatedMeasure, Measure.map_map (map_continuous (qE)).measurable
      (map_continuous (qE).symm).measurable]
    convert Measure.map_id
    ext x
    exact (qE).apply_symm_apply x
  exact (isSquareIntegrableModCentralSubgroup_comp_iff (e) CM hCM C
    (weightedCTranslatedCenter_le_center hG hi hν I hζ n sc hs)
    (weightedCTranslatedCenter_map hG hi hν I hζ n sc) mq₀ mq he π.obj.representation).mpr hq

end Langlands.HarishChandraSchwartz.WeakExpansion
