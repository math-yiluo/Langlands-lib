import Langlands.HarmonicAnalysis.HarishChandraSchwartz.StandardLeviLowerSplitCenter
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLeviDynamicIwasawa
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DynamicOrbitDensityFromOppositeContinuations

/-! # The density at the actual lower compact in the weak expansion -/

noncomputable section

set_option maxRecDepth 8192

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
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

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance lowerPacketDensityLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance lowerPacketDensityLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance lowerPacketDensityLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "𝐋" => Standard.leviScheme i ν (rootSet i ν I)
set_option hygiene false in
local notation "𝐋'" => Standard.leviScheme i ν (rootSet i ν I')
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "χs" => lowerCocharacter i ν (rootSet i ν I') ζ n
set_option hygiene false in
local notation "eₛ" => lowerLeviConjugation i ν (rootSet i ν I) (rootSet i ν I') hG hi hν
  (rootSet_subset i ν I) ζ hζ n hn
set_option hygiene false in
local notation "Φ" => lowerParameterIso hG hi hν I I' hζ n hn

variable {S : CommGroupScheme (Spec (CommRingCat.of F))} (a : S.toGrp ⟶ 𝐋)

/-- The given split component of the inducing Levi, transported to the
canonical parameter scheme of the lower parabolic. -/
def lowerParameterSplitComponent : S.toGrp ⟶ parameterScheme χs := a ≫ (Φ).inv

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
theorem isSplitComponent_lowerParameterSplitComponent (ha : IsSplitComponent a) :
    IsSplitComponent (lowerParameterSplitComponent hG hi hν I I' hζ n hn a) :=
  ha.comp_iso (Φ).symm

set_option hygiene false in
local notation "C" => rationalLeviSplitCenter I a
set_option hygiene false in
local notation "C'" => lowerCentral hG hi hν I I' hζ n hn C
set_option hygiene false in
local notation "a'" => lowerParameterSplitComponent hG hi hν I I' hζ n hn a

set_option maxHeartbeats 1000000 in
/-- On the literal lower dynamic Levi this gives exactly the conjugated central subgroup. -/
theorem lowerCentral_eq_lowerParameterSplitRange :
    C' = ((parameterHomeomorph χs).toMonoidHom.comp (rationalPoints.map a')).range := by
  let e := leviRationalPointHomeomorph i ν I
  have hpoint (x : rationalPoints 𝐋) :
      parameterHomeomorph χs (rationalPoints.map (Φ).inv x) = eₛ (e x) := by
    rw [← ContinuousMulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [← leviRationalPointHomeomorph_lowerParameterIso hG hi hν I I' hζ n hn,
      LowerSplitCenter.rationalPoints_map_hom_inv]
  have hhom : ((eₛ).toMonoidHom.comp e.toMonoidHom).comp (rationalPoints.map a) =
      (parameterHomeomorph χs).toMonoidHom.comp (rationalPoints.map a') := by
    apply MonoidHom.ext
    intro x
    change eₛ (e (rationalPoints.map a x)) = parameterHomeomorph χs (rationalPoints.map a' x)
    rw [lowerParameterSplitComponent, LowerSplitCenter.rationalPoints_map_comp, hpoint]
  calc
    C' = (((eₛ).toMonoidHom.comp e.toMonoidHom).comp (rationalPoints.map a)).range := by
      simp only [lowerCentral, rationalLeviSplitCenter, Subgroup.map_map, MonoidHom.range_comp]
      rfl
    _ = _ := congrArg MonoidHom.range hhom

variable (ha : IsSplitComponent a) [(C).Normal]
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
  (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C (rationalLeviSplitCenter_le_center I a ha)
    π.obj.representation mu)
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))
  (hFactors : StandardLeviDynamicIwasawaAt i ν (K : Subgroup (rationalPoints G)))

set_option hygiene false in
local notation "K'" => LowerChamber.lowerCompact I' K.isOpen
set_option hygiene false in
local notation "hK'" => isCompact_leviSchemeCompact (i := i) (ν := ν) (J := rootSet i ν I') hKc
set_option hygiene false in
local notation "χL" => (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫
  Standard.leviTorusHom i ν (rootSet i ν I'))
set_option hygiene false in
local notation "hP'" => factorization_subtype (hFactors (rootSet i ν I') (rootSet_subset i ν I') χL)
set_option hygiene false in
local notation "hOpp'" => factorization_subtype (hFactors (rootSet i ν I') (rootSet_subset i ν I')
  (Dynamic.inverseCocharacter χL))
set_option hygiene false in
local notation "hG'" => lowerAmbient_isConnectedReductive hG hi hν I'
set_option hygiene false in
local notation "As" => (lowerRepresentation hG hi hν I I' hζ n hn π).obj
set_option hygiene false in
local notation "hC" => rationalLeviSplitCenter_le_center I a ha

variable
  (p : ForwardContinuation χL hRefl hCST hG' K' hK' hP' hOpp' As)
  (q : ReverseContinuation χL hRefl hCST hG' K' hK' hP' hOpp' As)
  {DForward DReverse : Set (unramifiedCharacters (normCharacters χL))}
  (hForward : IsOpen DForward) (hneForward : DForward.Nonempty)
  (hForwardΩ : DForward ⊆ forwardFullDomainRegion χL K' hK' As)
  (hReverse : IsOpen DReverse) (hneReverse : DReverse.Nonempty)
  (hReverseΩ : DReverse ⊆ reverseFullDomainRegion χL K' hK' As)

set_option maxHeartbeats 1200000 in
/-- From the two actual opposite continuations at the literal compact,
construct the density package of the conjugated representation. -/
def lowerDensityFromOppositeContinuations :
    LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST := by
  let C₁ : Subgroup (levi χL) := C'
  letI : C₁.Normal := lowerCentral_normal hG hi hν I I' hζ n hn C
  letI : MeasurableSpace (levi χL ⧸ C₁) := lowerQuotientMeasurableSpace hG hi hν I I' hζ n hn C
  letI : BorelSpace (levi χL ⧸ C₁) := lowerQuotientBorelSpace hG hi hν I I' hζ n hn C
  let mu₁ : Measure (levi χL ⧸ C₁) := lowerMeasure hG hi hν I I' hζ n hn C mu
  letI : mu₁.IsHaarMeasure :=
    lowerMeasure_isHaarMeasure hG hi hν I I' hζ n hn C mu
  exact DynamicInducedOrbit.DensityPackage.ofSquareIntegrable.{u, uV} (G := 𝐋') (T := T)
    (Standard.leviTorusHom i ν (rootSet i ν I')) (conjugatedCocharacter i ζ n)
    hRefl hCST hG' K' hK' hP' hOpp' As p q (DForward := DForward) (DReverse := DReverse)
    hForward hneForward hForwardΩ hReverse hneReverse hReverseΩ
    a' (isSplitComponent_lowerParameterSplitComponent hG hi hν I I' hζ n hn a ha)
    C₁ (lowerCentral_le_center hG hi hν I I' hζ n hn C hC) mu₁
    (lowerCentral_eq_lowerParameterSplitRange hG hi hν I I' hζ n hn a)
    (lowerRepresentation hG hi hν I I' hζ n hn π).property.1
    (lowerRepresentation_isSquareIntegrable hG hi hν I I' hζ n hn C hC mu π hsq)

end Langlands.HarishChandraSchwartz.WeakExpansion
