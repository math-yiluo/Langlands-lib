import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalWeakExpansionRegularityAssembly
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCAuxiliaryDistance
import Langlands.Representation.Plancherel.RealizedCommonLeviContinuedPair
import Langlands.Representation.Plancherel.ActualOppositeCompactScalar

/-! # The lower opposite pair in the auxiliary scalar calculation -/

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
  DynamicOppositeCanonicalScalar

universe u uV

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance innerScalarAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance innerScalarLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance innerScalarLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance innerScalarLeviFiniteType (J : Set (characterLattice T)) :
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

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  {ζ' : cocharacterLattice T} (hζ' : IsStandardCocharacter i ν (rootSet i ν I') ζ')

local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
local notation "M₀" => Standard.leviScheme i ν (rootSet i ν I)

local instance innerScalarPointTopology : TopologicalSpace (rationalPoints M₀) :=
  rationalPointTopology F (M₀).X

local notation "νM" => leviRationalNormCharacters i ν I
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul

variable (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

local notation "χs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫
  Standard.leviTorusHom i ν (rootSet i ν I')
local notation "J" => Standard.leviHom i ν (rootSet i ν I')
local notation "Lj" => Standard.leviScheme i ν (rootSet i ν I')
local notation "o" => CommGroupScheme.groupHom (-ζ') ≫ i
local notation "χG" => CommGroupScheme.groupHom ζ ≫ i
local notation "θ" => χG ≫ (G.innerIso (n : rationalPoints G)).hom
local notation "θ₀" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
local notation "x" => CommGroupScheme.groupHom (cOppositeParabolicCocharacter i ζ' ζ n) ≫ i
local notation "y" => Dynamic.inverseCocharacter (CommGroupScheme.groupHom (cParabolicCocharacter i ζ' ζ n) ≫ i)
local notation "b" => Dynamic.inverseCocharacter χs
local notation "hc" => Standard.isClosedSubgroup_leviHom i ν (rootSet i ν I')
local notation "hα" => outerCentralizer_neg hG hi hν I' hζ'
local notation "hj" => outer_isRepresentedBy (i := i) (ν := ν) I' (-ζ') hα
local notation "er" => RepresentedDynamicTransport.pointEquiv F (Dynamic.centralizer o) J hj hc
local notation "hL" => lowerAmbient_isConnectedReductive hG hi hν I'
local notation "hx" => auxiliary_realization hG hi hν I I' hζ n hn (-ζ') hα
local notation "hy" => auxiliary_opposite_realization_of_innerCocharacter i hG hi J hc ζ'
  (conjugatedCocharacter i ζ n) χs hj (lowerCocharacter_comp_leviHom I' n)
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- The conjugated torus cocharacter is conjugation of the original ambient
cocharacter. -/
theorem weightedC_conjugatedCocharacter_eq : θ₀ = θ := by
  rw [conjugatedCocharacter, groupHom_cocharacterAut_comp]

local notation "hθ" => weightedC_conjugatedCocharacter_eq (i := i) (ζ := ζ) n
local notation "hxG" => (centralizer_auxiliary hG hi hν I I' hζ n hn (-ζ') hα).trans
  (congrArg Dynamic.centralizer hθ)
local notation "hyG" => (Dynamic.centralizer_inverseCocharacter _).trans
  ((centralizer_auxiliary hG hi hν I I' hζ n hn ζ' (outerCentralizer_pos hG hi hν I' hζ')).trans
    (congrArg Dynamic.centralizer hθ))
local notation "hbL" => Dynamic.centralizer_inverseCocharacter χs

include hG hi hν hζ hζ' hn in
/-- The common Levi inclusion from the lower pair to the ambient pair. -/
def auxiliaryInnerLeviEquiv : levi χs ≃ₜ* levi θ :=
  (realizedLeviEquiv o J hj hc x χs hx).trans (leviChange x θ (hxG).symm)

local notation "eM" => auxiliaryInnerLeviEquiv hG hi hν I I' hζ hζ' n hn

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem auxiliaryInnerLeviEquiv_coe (l : levi χs) :
    ((eM) l : rationalPoints G) = ((er) (l : rationalPoints Lj) : rationalPoints G) :=
  (leviChange_apply_coe x θ (hxG).symm (realizedLeviEquiv o J hj hc x χs hx l)).trans
    (realizedLeviEquiv_coe o J hj hc x χs hx l)

include hG hi hν hζ hζ' hn in
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem auxInner_parameter_represents :
    (Dynamic.centralizer θ).IsRepresentedBy (Dynamic.Affine.centralizerHom χs ≫ J) := by
  let hc₀ := Dynamic.Affine.isRepresentedBy_centralizerHom χs
  let : Mono (Dynamic.Affine.centralizerHom χs).hom.hom := hc₀.1
  let : Mono (J).hom.hom := (hj).1
  refine ⟨?_, ?_⟩
  · change Mono ((Dynamic.Affine.centralizerHom χs).hom.hom ≫ (J).hom.hom)
    infer_instance
  · rw [← hxG, (hx).2.1]
    change SubgroupFunctor.range (Dynamic.Affine.centralizerHom χs ≫ J) =
      (Dynamic.centralizer χs).map J
    rw [← hc₀.2]
    apply SubgroupFunctor.ext
    intro Y
    apply Subgroup.ext
    intro w
    simp only [SubgroupFunctor.mem_range, SubgroupFunctor.mem_map, Grp.comp_hom_hom]
    exact ⟨fun ⟨v, hv⟩ => ⟨v ≫ (Dynamic.Affine.centralizerHom χs).hom.hom,
      ⟨v, rfl⟩, (Category.assoc _ _ _).trans hv⟩,
      fun ⟨_, ⟨v, rfl⟩, hv⟩ => ⟨v, (Category.assoc _ _ _).symm.trans hv⟩⟩

/-- The two actual parameter schemes represent the same ambient common Levi. -/
def auxiliaryInnerParameterIso : parameterScheme χs ≅ parameterScheme θ :=
  (auxInner_parameter_represents hG hi hν I I' hζ hζ' n hn).isoOfIsRepresentedBy
    (Dynamic.Affine.isRepresentedBy_centralizerHom θ)

local notation "ep" => auxiliaryInnerParameterIso hG hi hν I I' hζ hζ' n hn

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The parameter comparison agrees with the inclusions into the ambient group. -/
theorem auxiliaryInnerParameterIso_hom_comp :
    (ep).hom ≫ Dynamic.Affine.centralizerHom θ = Dynamic.Affine.centralizerHom χs ≫ J :=
  (auxInner_parameter_represents hG hi hν I I' hζ hζ' n hn).isoOfIsRepresentedBy_hom_comp
    (Dynamic.Affine.isRepresentedBy_centralizerHom θ)

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in
/-- The parameter isomorphism agrees at points with the literal inclusion. -/
theorem auxiliaryInnerParameterIso_points (v : rationalPoints (parameterScheme χs)) :
    parameterHomeomorph θ (rationalPoints.map (ep).hom v) = (eM) (parameterHomeomorph χs v) := by
  apply Subtype.ext
  rw [auxiliaryInnerLeviEquiv_coe, RepresentedDynamicTransport.pointEquiv_apply_coe,
    parameterHomeomorph_apply_coe, parameterHomeomorph_apply_coe, rationalPoints.map_apply]
  have he := auxiliaryInnerParameterIso_hom_comp hG hi hν I I' hζ hζ' n hn
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    congrArg (fun f : parameterScheme χs ⟶ G => v ≫ f.hom.hom) he

/-- Characters used for the two actual twists are the same along the
inclusion of the common Levi. -/
theorem auxiliaryInnerParameterTransport_apply (w : unramifiedCharacters (normCharacters θ))
    (l : levi χs) :
    (parameterTransport χs (rationalUnramifiedCharacterRestrict (ep).hom w)).val l =
      (parameterTransport θ w).val ((eM) l) := by
  obtain ⟨v, rfl⟩ := (parameterHomeomorph χs).surjective l
  rw [← auxiliaryInnerParameterIso_points hG hi hν I I' hζ hζ' n hn v]
  change (rationalUnramifiedCharacterRestrict (ep).hom w).val
    ((parameterHomeomorph χs).symm (parameterHomeomorph χs v)) =
      w.val ((parameterHomeomorph θ).symm (parameterHomeomorph θ (rationalPoints.map (ep).hom v)))
  rw [ContinuousMulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply,
    rationalUnramifiedCharacterRestrict_apply]

attribute [local instance]
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel

local notation "Mπ" => RationalPointFamily.levi i ν I

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u})
  (hCST : CentralSplitTorusCharacterStatement.{u})
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := Mπ))
  (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG
    (SmoothRep.pullback (standardLeviDynamicHomeomorph hG hi hν I hζ) π.obj))
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)
  (hxK : ∀ g : rationalPoints G, ∃ p : parabolic x, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))
  (hyK : ∀ g : rationalPoints G, ∃ p : parabolic y, ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G))

local notation "B" => (lowerRepresentation hG hi hν I I' hζ n hn π).obj

variable (A : SmoothRep.{0, u, uV} ℂ (levi θ))
  (eB : (SmoothRep.pullback eM A).representation.Equiv (B).representation)
  (p : ContinuedPair θ hG K hK x hxG hxK y hyG hyK A)
  (q : ContinuedPair θ hG K hK y hyG hyK x hxG hxK A)

local notation "X" => unramifiedCharacters (normCharacters θ)
local notation "XL" => unramifiedCharacters (normCharacters χs)
/-- Restriction to the lower parameter scheme along its ambient identification. -/
def auxiliaryInnerParameterRestriction : X →ₜ* XL :=
  rationalUnramifiedCharacterRestrict (ep).hom
local notation "τ" => auxiliaryInnerParameterRestriction hG hi hν I I' hζ hζ' n hn
local notation "hτ" => auxiliaryInnerParameterTransport_apply hG hi hν I I' hζ hζ' n hn
local notation "he" => auxiliaryInnerLeviEquiv_coe hG hi hν I I' hζ hζ' n hn

include hN in
private theorem lowerCompact_in_ambient (k : PM.K) :
    ((er) (k : rationalPoints Lj) : rationalPoints G) ∈ K := by
  have hk := k.property
  change (k : rationalPoints Lj) ∈ PM.K.toSubgroup at hk
  rw [hN.lower] at hk
  rw [RepresentedDynamicTransport.pointEquiv_apply_coe]
  exact hk

private theorem lowerCompact_nontrivial :
    Nontrivial (CompactInductionPicture (decomposition χs) PM.K B) := by
  obtain ⟨v, ℓ, hv⟩ := exists_normalized_compactCoefficient (χ := χs) (hG := hL)
    (K := PM.K) (hK := PM.hK) (hPK := PM.hPK) (A := B) (hne := PM.hne) (hi := PM.hirr)
  have hv₀ : v ≠ 0 := by
    intro heq
    rw [heq, map_zero] at hv
    exact zero_ne_one hv
  exact ⟨v, 0, hv₀⟩

local notation "hF" => conditionalSquaredModulus χs hRefl hCST hL
local notation "hR" => conditionalReverseSquaredModulus χs hRefl hCST hL

private def lowerForward : ForwardContinuation χs hRefl hCST hL PM.K PM.hK PM.hPK PM.hOppK B :=
  PM.p

private def lowerReverse : ReverseContinuation χs hRefl hCST hL PM.K PM.hK PM.hPK PM.hOppK B :=
  PM.q

local notation "LQ" => lowerForward hG hi hν I I' hζ n hn hRefl hCST π PM
local notation "LQ'" => lowerReverse hG hi hν I I' hζ n hn hRefl hCST π PM
local notation "PR" => p.regularRegion ∩ q.regularRegion
private def lowerRegular : Set XL := (LQ).regularRegion ∩ (LQ').regularRegion
local notation "QR" => lowerRegular hG hi hν I I' hζ n hn hRefl hCST π PM
local notation "GJ" => fun z : ↥(PR) => p.presentation.continuedComposite q.presentation z
local notation "LJ" => fun w : ↥(QR) => (LQ).continuedComposite LQ' ⟨w.val, w.property⟩

include hN eB in
set_option maxHeartbeats 2500000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The round trip through the negative auxiliary parabolic agrees with
the round trip of the prescribed lower pair up to the two Haar scales. -/
theorem auxiliaryInner_compare :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (w : X) (hw : w ∈ PR) (hw' : (τ) w ∈ QR) (s t : ℂ),
      GJ ⟨w, hw⟩ = s • LinearMap.id → LJ ⟨(τ) w, hw'⟩ = t • LinearMap.id →
      s = (c : ℂ) * t := by
  have hKN := lowerCompact_in_ambient hG hi hν I I' hζ hζ' n hn K hRefl hCST π PG PM hN
  let _ := lowerCompact_nontrivial hG hi hν I I' hζ n hn hRefl hCST π PM
  exact exists_realizedContinuedRoundTrip_scalar_scale_of_compact_inclusion
    o J hj hc x y χs b hx hy θ χs hG hL hxG hyG rfl hbL eM A B eB (ep).hom hτ
    K hK PM.K PM.hK hxK hyK PM.hPK PM.hOppK p hF LQ q hR LQ' he hKN

end Langlands.HarishChandraSchwartz.WeakExpansion
