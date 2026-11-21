import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalLowerPacketDensity
import Langlands.Representation.Plancherel.DynamicContinuationOpenFullDomain
import Langlands.Representation.Plancherel.DynamicOppositeFullLeviContinuation
import Langlands.GroupScheme.Dynamic.CentralizerRestriction
import Langlands.GroupScheme.Rational.TorusSplitPartTransfer

/-! # Lower packet densities on nonempty open full convergence domains -/

noncomputable section

set_option maxRecDepth 8192
set_option backward.isDefEq.respectTransparency false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Plancherel Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz.WeakExpansion

open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar RationalPointFamily

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
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

local instance lowerOpenDomainsLeviAffineHom (J : Set (characterLattice T)) :
    IsAffineHom (Standard.leviScheme i ν J).X.hom :=
  leviScheme_isAffineHom i ν J
local instance lowerOpenDomainsLeviAffine (J : Set (characterLattice T)) :
    IsAffine (Standard.leviScheme i ν J).X.left :=
  isAffine_of_isAffineHom (Standard.leviScheme i ν J).X.hom
local instance lowerOpenDomainsLeviFiniteType (J : Set (characterLattice T)) :
    LocallyOfFiniteType (Standard.leviScheme i ν J).X.hom :=
  leviScheme_locallyOfFiniteType i ν J

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (I I' : Finset (SimpleRoot i ν))
  {ζ : cocharacterLattice T} (hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ)
  (n : normalizerPoints i)
  (hn : conjugatedLevi i ν (rootSet i ν I) n ≤ standardLevi i ν (rootSet i ν I'))

set_option hygiene false in
local notation "L'" => Standard.leviScheme i ν (rootSet i ν I')
set_option hygiene false in
local notation "𝐌" => {x : rationalPoints G //
  @Membership.mem (rationalPoints G) (Subgroup (rationalPoints G)) _
    (standardLeviPoints i ν (rootSet i ν I)) x}
set_option hygiene false in
local notation "χ'" => lowerCocharacter i ν (rootSet i ν I') ζ n

variable (π : IrreducibleAdmissibleRep.{0, u, uV} (k := ℂ) (G := 𝐌))
  {K : OpenSubgroup (rationalPoints G)} (hKc : IsCompact (K : Set (rationalPoints G)))

set_option hygiene false in
local notation "K'" => LowerChamber.lowerCompact I' K.isOpen
set_option hygiene false in
local notation "hK'" => isCompact_leviSchemeCompact (i := i) (ν := ν) (J := rootSet i ν I') hKc
set_option hygiene false in
local notation "π'" => lowerRepresentation hG hi hν I I' hζ n hn π
set_option hygiene false in
local notation "Ωf" => forwardFullDomainRegion χ' K' hK' (π').obj
set_option hygiene false in
local notation "Ωr" => reverseFullDomainRegion χ' K' hK' (π').obj

/-- Both actual opposite compact integrals in the lower Levi have a nonempty
open full convergence domain at the literal lower compact. -/
def LowerPacketOpenFullDomains : Prop :=
  IsOpen Ωf ∧ Set.Nonempty Ωf ∧ IsOpen Ωr ∧ Set.Nonempty Ωr

set_option maxHeartbeats 1200000 in
/-- At the empty output face every element of the lower Levi commutes with
the conjugated cocharacter, so both full convergence domains are universal. -/
theorem lowerPacketOpenFullDomains_of_emptyOutput (hempty : rootSet i ν I' = ∅) :
    LowerPacketOpenFullDomains hG hi hν I I' hζ n hn π hKc := by
  let j := Standard.leviHom i ν (rootSet i ν I')
  have : Mono j.hom.hom := (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I')).1
  have hLevi : standardLevi i ν (rootSet i ν I') = torusCentralizer i :=
    (congrArg (standardLevi i ν) hempty).trans
      (standardLevi_empty_eq_torusCentralizer_of_generic i ν hG hi hν)
  have hL : DynamicOppositeStandardIntertwining.levi χ' = ⊤ := by
    apply top_unique
    intro g _
    apply (Dynamic.mem_centralizer_comp_iff j χ' g).mp
    have hmem : g ≫ j.hom.hom ∈ (standardLevi i ν (rootSet i ν I')).carrier _ := by
      rw [← (Standard.isRepresentedBy_leviHom i ν (rootSet i ν I')).2]
      exact SubgroupFunctor.mem_range.mpr ⟨g, rfl⟩
    rw [hLevi] at hmem
    change g ≫ j.hom.hom ∈ (Dynamic.centralizer
      ((CommGroupScheme.groupHom (conjugatedCocharacter i ζ n) ≫
        Standard.leviTorusHom i ν (rootSet i ν I')) ≫ j)).carrier _
    rw [show j = Standard.leviHom i ν (rootSet i ν I') from rfl,
      Category.assoc, Standard.leviTorusHom_comp, ← torusCentralizer_gm_eq_dynamicCentralizer]
    exact torusCentralizer_le_of_factor i _ (CommGroupScheme.groupHom (conjugatedCocharacter i ζ n))
      rfl _ hmem
  have hf := forwardFullDomainRegion_eq_univ_of_levi_eq_top χ' K' hK' (π').obj hL
  have hr := reverseFullDomainRegion_eq_univ_of_levi_eq_top χ' K' hK' (π').obj hL
  unfold LowerPacketOpenFullDomains
  rw [hf, hr]
  exact ⟨isOpen_univ, Set.univ_nonempty, isOpen_univ, Set.univ_nonempty⟩

set_option hygiene false in
local notation "C" => rationalLeviSplitCenter I a

set_option maxHeartbeats 3000000 in
/-- The opposite open full domains supply the density package on the lower
Levi at the literal intersection with the ambient compact. -/
theorem exists_lowerDensityPackage_at_compact_of_openFullDomains
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (a : A.toGrp ⟶ Standard.leviScheme i ν (rootSet i ν I)) (ha : IsSplitComponent a)
    [(C).Normal] [MeasurableSpace (𝐌 ⧸ C)] [BorelSpace (𝐌 ⧸ C)]
    (mu : Measure (𝐌 ⧸ C)) [mu.IsHaarMeasure]
    (hsq : IsSquareIntegrableModCentralSubgroup C (rationalLeviSplitCenter_le_center I a ha)
      π.obj.representation mu)
    (hRefl : RelativeRootReflectionExistenceStatement.{u})
    (hCST : CentralSplitTorusCharacterStatement.{u})
    (hFactors : StandardLeviDynamicIwasawaAt i ν K.toSubgroup)
    (hDomains : LowerPacketOpenFullDomains hG hi hν I I' hζ n hn π hKc) :
    ∃ P : LowerDensityPackage hG hi hν I I' hζ n hn π hRefl hCST,
      P.K.toSubgroup = leviSchemeCompact K.toSubgroup i ν (rootSet i ν I') := by
  obtain ⟨hFopen, hFne, hRopen, hRne⟩ := hDomains
  let a' := lowerParameterSplitComponent hG hi hν I I' hζ n hn a
  have ha' := isSplitComponent_lowerParameterSplitComponent hG hi hν I I' hζ n hn a ha
  have hG' := lowerAmbient_isConnectedReductive hG hi hν I'
  have hP' (g : rationalPoints L') :
      ∃ p : parabolic χ', ∃ k : K', g = (p : rationalPoints L') * (k : rationalPoints L') :=
    factorization_subtype (P := parabolic χ') (K := K')
      (hFactors (rootSet i ν I') (rootSet_subset i ν I') χ') g
  have hOpp' (g : rationalPoints L') :
      ∃ p : oppositeParabolic χ', ∃ k : K', g = (p : rationalPoints L') * (k : rationalPoints L') :=
    factorization_subtype (P := oppositeParabolic χ') (K := K')
      (hFactors (rootSet i ν I') (rootSet_subset i ν I') (Dynamic.inverseCocharacter χ')) g
  have hfin := SmoothRep.hasFiniteLength_of_isIrreducible (π').property.1
  let p := DynamicCommonLeviContinuation.forwardContinuationOfOpenFullDomain hG' χ' a' ha' K' hK'
    (π').obj hRefl hCST hP' hOpp' (π').property.2 hfin hFopen hFne
  let q := DynamicCommonLeviContinuation.reverseContinuationOfOpenFullDomain hG' χ' a' ha' K' hK'
    (π').obj hRefl hCST hP' hOpp' (π').property.2 hfin hRopen hRne
  exact ⟨lowerDensityFromOppositeContinuations hG hi hν I I' hζ n hn a ha π mu hsq hRefl hCST
    hKc hFactors p q hFopen hFne subset_rfl hRopen hRne subset_rfl, rfl⟩

end Langlands.HarishChandraSchwartz.WeakExpansion
