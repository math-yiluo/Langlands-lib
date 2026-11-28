import Langlands.HarmonicAnalysis.HarishChandraSchwartz.WeightedCRoundTripVertices

/-! # The ambient round trip at the translated parabolic -/

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
  DynamicCommonLeviPresentations

universe u uV

open DynamicOppositeStandardIntertwining RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {i : T.toGrp ⟶ G} {ν : cocharacterLattice T}

local instance cAmbRTAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
local instance cAmbRTLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance cAmbRTLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance cAmbRTLeviFiniteType (J : Set (characterLattice T)) :
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

local instance cAmbRTPointTopology : TopologicalSpace (rationalPoints M₀) :=
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
local notation "ox" => GalleryVertex.opposite x
local notation "oθ" => GalleryVertex.opposite θ
local notation "V" => ({θ, oθ, x, ox, y} : Finset Vertex)

variable (iw : ∀ (v : Vertex) (g : rationalPoints G), ∃ p : parabolic v.val, ∃ k : K,
  g = (p : rationalPoints G) * (k : rationalPoints G))
  (p : CompactContinuationSystem χ hG A K hK iw)

local notation "J[" v "," w "," z "]" => compactContinuationValue χ hG A K hK iw p v w z
local notation "R[" v "," w "]" => (p v w).regularRegion
local notation "U[" v "," z "]" => UnramifiedLeviInduction
  (commonDecomposition χ (v : Vertex).val (v : Vertex).property) (radical_isClosed (v : Vertex).val)
  (leviNormCharacters χ) (parameterTransport χ z) A
local notation "D₀" => cWeightedDomain hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "gConst" => (RationalPlancherelDensity.plancherelDensityConstant i ζ PG.K PG.hK : ℂ)
local notation "lConst" => (RationalPlancherelDensity.plancherelDensityConstant
  (Standard.leviTorusHom i ν (rootSet i ν I')) (conjugatedCocharacter i ζ n) PM.K PM.hK : ℂ)

local notation "Gδ" => weightedCAmbientDensityValue hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM
local notation "Lδ" => weightedCLowerDensityValue hG hi hν I I' hζ hζ' n hn K hK hRefl hCST π PG PM

variable {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
  {sc : Tc.toGrp ⟶ L} (hs : IsSplitComponent sc)
  (hIr : (A).IsIrreducible) (hAd : (A).IsAdmissible)

local notation "AllRegular" => fun w : Z => ∀ v ∈ V, ∀ v' ∈ V, w ∈ R[v,v']

local notation "χs" => CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫
  Standard.leviTorusHom i ν (rootSet i ν I')


set_option maxHeartbeats 20000000 in
set_option backward.isDefEq.respectTransparency.types false in
/-- The ambient package scalar evaluates the round trip of the opposite pair
at the conjugated parabolic, up to one positive Haar factor, and gives the
ambient density as a reciprocal fraction. -/
theorem exists_weightedC_ambientRoundTrip (hPG : PG.canonicalScalar ≠ 0) :
    ∃ (Gnum Gden c₀ : R) (t₀ : ℝ≥0), 0 < t₀ ∧ Gnum ≠ 0 ∧ Gden ≠ 0 ∧ c₀ ≠ 0 ∧
      (∀ w : Z, w ∈ R[θ,oθ] → w ∈ R[oθ,θ] → c₀.val w ≠ 0 →
        Gden.val w ≠ 0 ∧ (J[oθ,θ,w]).comp (J[θ,oθ,w]) =
          ((t₀ : ℂ) * (Gnum.val w / Gden.val w)) • LinearMap.id) ∧
      (∀ z : unramifiedCharacters ν₀, ∀ hz : (Φ) z ∈ D₀, Gnum.val ((liftParam) z) ≠ 0 →
        Gδ ⟨(Φ) z, hz⟩ =
          gConst * (Gden.val ((liftParam) z) / Gnum.val ((liftParam) z))) := by
  obtain ⟨aG, bG, hbG, _, hGFrac, _⟩ := package_compact_spec PG
  have haG : aG ≠ 0 := by
    intro h
    apply hPG
    rw [hGFrac, h, map_zero, zero_div]
  obtain ⟨qF, qR, a', b', t₀, ht₀, hb', hqF, hqR, hT, hV⟩ :=
    exists_conjugatedChangedCompact_canonicalScalar χG m PG.K PG.hK hRefl hCST hG A₀ PG.hPK
      PG.hOppK PG.p PG.q PG.hDForward PG.hneForward PG.hDForwardΩ PG.hDReverse PG.hneReverse
      PG.hDReverseΩ PG.hD PG.hne PG.hirr K hK (iw θ) (iw oθ)
  let Gnum : R := (E) aG
  let Gden : R := (E) bG
  have hGnum : Gnum ≠ 0 := (map_ne_zero_iff (E) (E).injective).mpr haG
  have hGden : Gden ≠ 0 := (map_ne_zero_iff (E) (E).injective).mpr hbG
  let c₀ : R := Gden * (b' * (qF.denominator * qR.denominator))
  have hc₀ : c₀ ≠ 0 := weightedC_regular_mul_ne_zero hG n hGden
    (weightedC_regular_mul_ne_zero hG n hb' (weightedC_regular_mul_ne_zero hG n hqF hqR))
  refine ⟨Gnum, Gden, c₀, t₀, ht₀, hGnum, hGden, hc₀, ?_, ?_⟩
  · intro w hθo hoθ hw
    have hw' : Gden.val w * (b'.val w * (qF.denominator.val w * qR.denominator.val w)) ≠ 0 := hw
    simp only [mul_ne_zero_iff] at hw'
    obtain ⟨hbGw, hb'w, hqFw, hqRw⟩ := hw'
    have hF := oppositeForwardContinuedPair_eq χ K hK hRefl hCST hG A (iw θ) (iw oθ) qF
      (p θ oθ) ⟨w, hθo, hqFw⟩
    have hR := oppositeReverseContinuedPair_eq χ K hK hRefl hCST hG A (iw θ) (iw oθ) qR
      (p oθ θ) ⟨w, hoθ, hqRw⟩
    have hθcomp : (J[oθ,θ,w]).comp (J[θ,oθ,w]) = (a'.val w / b'.val w) • LinearMap.id :=
      (congrArg₂ LinearMap.comp hR hF).trans (hV ⟨w, hqFw, hqRw⟩).2
    have hOuter : a'.val w / b'.val w = (t₀ : ℂ) * (Gnum.val w / Gden.val w) := by
      have hfield : φ a' / φ b' = φ (algebraMap ℂ R (t₀ : ℂ) * Gnum) / φ Gden := by
        have hGFrac' := hGFrac
        unfold DynamicInducedOrbit.DensityPackage.canonicalScalar at hGFrac'
        rw [hT, hGFrac', map_div₀, rationalUnramifiedFunctionFieldEquiv_algebraMap,
          rationalUnramifiedFunctionFieldEquiv_algebraMap, map_mul, mul_div_assoc]
      have hv := rationalFunction_value_eq L hp hL hb'w hbGw rfl hfield
      exact hv.trans (mul_div_assoc _ _ _)
    exact ⟨hbGw, hθcomp.trans (by rw [hOuter])⟩
  · intro z hz hnum
    change rationalValueAt (packageDensity PG) hz.2.1 = _
    have hnumG : aG.val (standardLeviUnramifiedRestrict hG hi hν I hζ ((Φ) z)) =
        Gnum.val ((liftParam) z) := by
      rw [← weightedC_restrict_ambientDensity hG hi hν I hζ n z]
      rfl
    have hdenG : bG.val (standardLeviUnramifiedRestrict hG hi hν I hζ ((Φ) z)) =
        Gden.val ((liftParam) z) := by
      rw [← weightedC_restrict_ambientDensity hG hi hν I hζ n z]
      rfl
    have hρG := packageDensity_value_of_scalarFraction PG hz.2.1 hGFrac (hnumG.symm ▸ hnum)
    rw [hρG, hnumG, hdenG]

end Langlands.HarishChandraSchwartz.WeakExpansion
