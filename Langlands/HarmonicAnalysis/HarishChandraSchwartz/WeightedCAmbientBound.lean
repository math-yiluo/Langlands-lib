import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCScalarRoundTrip
import Langlands.Representation.Plancherel.GalleryWeightedCompactBound
import Langlands.Representation.Plancherel.ActualCommonLeviV3SquareIntegrableData

/-! # The actual density-weighted tensor in the ambient compact pictures -/

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
  DynamicOppositeCanonicalScalar ActualCommonLeviV3 ActualCommonLeviCompactTensor
  DynamicCommonLeviPresentations ActualCommonLeviIwasawa

universe u uV

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

attribute [local instance] cMainRTAmbientAffine cMainRTLeviAffineHom cMainRTLeviAffine
  cMainRTLeviFiniteType

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

attribute [local instance] cMainRTPointTopology

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

local notation "f" => weightedCParameterIso hG hi hν I hζ n
local notation "ν₀" => fun a => (rationalNormCharacters M₀ a).toMul
local notation "Φ" => unramifiedCharactersHomeomorph fM ν₀
local notation "liftParam" => rationalUnramifiedCharacterRestrict (f).hom
local notation "τ" => rationalUnramifiedCharacterRestrict (eI).hom
local notation "δG" => rationalUnramifiedCharacterRestrict (e₂).hom
local notation "Z" => unramifiedCharacters (normCharacters χ)
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
local notation "GR" => unramifiedRegularFunctions (normCharacters χG)
local notation "LR" => unramifiedRegularFunctions (normCharacters b)
local notation "hp" => parameterProjection_continuous χ
local notation "hL" => parameterScheme_isConnectedReductive χ hG
local notation "Frac" => rationalUnramifiedFunctionField L hp hL
local notation "φ" => algebraMap R Frac
local notation "E" => rationalUnramifiedRegularFunctionsEquiv (e₂)
local notation "E'" => rationalUnramifiedFunctionFieldEquiv (parameterProjection_continuous χG)
  (parameterScheme_isConnectedReductive χG hG) hp hL (e₂)
local notation "tG" => lowerAmbient_isConnectedReductive hG hi hν I'

variable (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))
  (hRefl : RelativeRootReflectionExistenceStatement.{u}) (hCST : CentralSplitTorusCharacterStatement.{u})
  (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := M))

local notation "A₀" => SmoothRep.pullback eG π.obj
local notation "A" => conjugateRepresentation χG m A₀
local notation "B" => (lowerRepresentation hG hi hν I I' hζ n hn π).obj

variable (PG : DynamicInducedOrbit.DensityPackage i ζ hRefl hCST hG A₀)
  (PM : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST)
  (hN : CommonCompactNormalization hG hi hν I I' hζ n hn K hRefl hCST π PG PM)

attribute [local instance]
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel

local notation "θ₀" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫ i
local notation "eχ" => weightedC_conjugatedCocharacter_eq (i := i) (ζ := ζ) n
local notation "Vertex" => GalleryVertex χ

local notation "θ" => (⟨χ, rfl⟩ : Vertex)
local notation "x" => weightedCAuxiliaryVertex hG hi hν I I' hζ n hn ζ'
  (outerCentralizer_pos hG hi hν I' hζ')
local notation "y" => weightedCAuxiliaryVertex hG hi hν I I' hζ n hn (-ζ')
  (outerCentralizer_neg hG hi hν I' hζ')
local notation "V" => ({θ, GalleryVertex.opposite θ, x, GalleryVertex.opposite x, y} : Finset Vertex)

variable (iw : ∀ (v : Vertex) (g : rationalPoints G), ∃ p : parabolic v.val, ∃ k : K,
  g = (p : rationalPoints G) * (k : rationalPoints G))
  (p : CompactContinuationSystem χ hG A K hK iw)

local notation "cd[" v "]" => commonDecomposition χ (v : Vertex).val (v : Vertex).property
local notation "hU[" v "]" => radical_isClosed (v : Vertex).val
local notation "hδ[" v "]" => radical_unimodular (v : Vertex).val hG
local notation "I[" v "," z "]" => UnramifiedLeviInduction cd[v] hU[v]
  (leviNormCharacters χ) (parameterTransport χ z) A
local notation "Datum[" v "," w "]" => GenericComparisonData χ hG K hK (v : Vertex).val
  (v : Vertex).property (iw v) (w : Vertex).val (w : Vertex).property (iw w) A

variable (g₀ : Datum[y,θ]) (g₁ : Datum[x,y])

local notation "Reg₀" => genericLocus χ hG K hK (y).val (y).property (iw y)
  (θ).val (θ).property (iw θ) A (g₀).forward (g₀).reverse
local notation "Reg₁" => genericLocus χ hG K hK (x).val (x).property (iw x)
  (y).val (y).property (iw y) A (g₁).forward (g₁).reverse

variable (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (mq : Measure (levi χ ⧸ C)) [mq.IsHaarMeasure] [mq.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC (A).representation mq)
  (hIr : (A).IsIrreducible) (hCs : IsActualSplitCenter χ C)
  (bForm : InvariantPositiveForm (A).representation)
  {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  {sc : Tc.toGrp ⟶ L} (hs : IsSplitComponent sc)

local notation "Ex" => compactNormModel χ hG A K hK (x).val (x).property (iw x) bForm
local notation "Ey" => compactNormModel χ hG (A).contragredient K hK (y).val (y).property (iw y)
  (dualInvariantForm bForm (compactOpenCofinal_of_nonarchimedean (levi χ)) hsq.1)
local notation "e" => TensorProduct.congr (Ex) (Ey)
local notation "N[" a "]" => galleryWeightedNumerator χ hG A K hK iw p y θ x g₀ a
local notation "Bd[" d "]" => galleryWeightedDenominator χ hG A K hK iw p y θ x g₀ d
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "Gδ" => weightedCAmbientDensityValue hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "Lδ" => weightedCLowerDensityValue hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "AllRegular" => fun w : Z => ∀ v ∈ V, ∀ v' ∈ V, w ∈ (p v v').regularRegion

include hN hIr hCs hs in
set_option maxHeartbeats 3800000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual package density ratio gives a cleared bounded ambient
compact tensor on a common dense open regular region. -/
theorem exists_weightedCAmbientCompactBound [Nontrivial A] [DecidableEq Vertex]
    (hPG : PG.canonicalScalar ≠ 0) (hPM : PM.canonicalScalar ≠ 0) :
    ∃ (a d : R) (S : Set Z), (Bd[d]) ≠ 0 ∧ IsDenseOpenUnitaryRegion L S ∧
      (∀ w ∈ S, AllRegular w ∧ d.val w ≠ 0 ∧ w ∈ Reg₀ ∧ w ∈ Reg₁) ∧
      HasClearedUnitaryBound L (fun w => (e).toLinearMap.comp (N[a] w)) (Bd[d]) ∧
      (∀ z : unramifiedCharacters ν₀, ∀ hz : (Φ) z ∈ D₀, (liftParam) z ∈ S →
        Gδ ⟨(Φ) z, hz⟩ * (Lδ ⟨(Φ) z, hz⟩)⁻¹ = a.val ((liftParam) z) / d.val ((liftParam) z)) := by
  have hirr (v : Vertex) : ∃ c : R, c ≠ 0 ∧ ∀ w : Z, c.val w ≠ 0 → (I[v,w]).IsIrreducible := by
    obtain ⟨c, hc, hv⟩ := exists_actual_induction_irreducibility_factor χ A C hC mq hG hsq hIr hCs
      v.val v.property
    exact ⟨c, hc, fun w hw => (Langlands.isIrreducible_iff_of_equiv
      (normalizedInductionLeviEquiv cd[v] hU[v] hδ[v] (twistObject χ w A))).mp (hv w hw)⟩
  have hR := exists_weightedCScalar_roundTrip
    hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM hN iw p hs hIr hsq.1 hPG hPM (hirr x) (hirr y)
  refine hR.elim fun a hR => hR.elim fun d hR => hR.elim fun T hR => hR.elim fun κ hR => ?_
  have hT := hR.2.1
  have hLoc := hR.2.2.1
  have hEq := hR.2.2.2
  refine (g₀).hasDense.2.2.2.elim fun B₀ hB₀ => (g₁).hasDense.2.2.2.elim fun B₁ hB₁ => ?_
  have ho₀ : IsDenseOpenUnitaryRegion L B₀ := ⟨hB₀.1, hB₀.2.2.2.1, hB₀.2.2.2.2⟩
  have ho₁ : IsDenseOpenUnitaryRegion L B₁ := ⟨hB₁.1, hB₁.2.2.2.1, hB₁.2.2.2.2⟩
  have hS : IsDenseOpenUnitaryRegion L (T ∩ (B₀ ∩ B₁)) := hT.inter L (ho₀.inter L ho₁)
  have hθ : θ ∈ V := by simp
  have hx : x ∈ V := by simp
  have hy : y ∈ V := by simp
  have hLoc' (w : Z) (hw : w ∈ T ∩ (B₀ ∩ B₁)) :
      AllRegular w ∧ d.val w ≠ 0 ∧ w ∈ Reg₀ ∧ w ∈ Reg₁ :=
    ⟨(hLoc w hw.1).1, (hLoc w hw.1).2.1, hB₀.2.2.1 hw.2.1, hB₁.2.2.1 hw.2.2⟩
  have hBound := galleryWeightedCompact_hasClearedUnitaryBound χ hG A K hK iw p y θ x g₀ g₁
    C hC mq hsq hIr bForm (T ∩ (B₀ ∩ B₁)) a d κ (fun w hw =>
      ⟨(hLoc' w hw).2.2.1, (hLoc' w hw).2.2.2, (hLoc' w hw).1 y hy θ hθ,
        (hLoc' w hw).1 θ hθ x hx, (hLoc' w hw).1 y hy x hx, (hLoc' w hw).1 x hx y hy,
        (hLoc' w hw).2.1, (hLoc w hw.1).2.2.2.2⟩) hs (by
      have h := isDistanceAdditive_auxiliary i hG hi (-ζ') (conjugatedCocharacter i ζ n)
      rw [neg_neg] at h
      change IsDistanceAdditive
        (CommGroupScheme.groupHom (auxiliaryCocharacter i (-ζ') (conjugatedCocharacter i ζ n)) ≫ i) χ
        (CommGroupScheme.groupHom (auxiliaryCocharacter i ζ' (conjugatedCocharacter i ζ n)) ≫ i)
      rw [← eχ]
      exact h)
    hS.unitary_dense
  have hne : (Bd[d]) ≠ 0 := by
    refine hS.dense.nonempty.elim fun w hw => ?_
    have he : (Bd[d]).val w ≠ 0 := mul_ne_zero (hLoc' w hw).2.1
      (mul_ne_zero ((hLoc' w hw).1 θ hθ x hx) (hLoc' w hw).2.2.1.choose.2)
    exact fun h0 => he (by rw [h0]; rfl)
  exact ⟨a, d, T ∩ (B₀ ∩ B₁), hne, hS, hLoc', hBound, fun z hz hw => hEq z hz hw.1⟩

end Langlands.HarishChandraSchwartz.WeakExpansion
